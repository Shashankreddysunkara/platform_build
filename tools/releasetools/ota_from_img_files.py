#!/usr/bin/env python
#
# Copyright (C) 2008 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
Given a target-files zipfile, produces an OTA package that installs
that build.  An incremental OTA is produced if -i is given, otherwise
a full OTA is produced.

Usage:  ota_from_target_files [flags] input_target_files output_ota_package

  --board_config  <file>
      Deprecated.

  -k (--package_key) <key> Key to use to sign the package (default is
      the value of default_system_dev_certificate from the input
      target-files's META/misc_info.txt, or
      "build/target/product/security/testkey" if that value is not
      specified).

      For incremental OTAs, the default value is based on the source
      target-file, not the target build.

  -i  (--incremental_from)  <file>
      Generate an incremental OTA using the given target-files zip as
      the starting build.

  -o  (--oem_settings)  <file>
      Use the file to specify the expected OEM-specific properties
      on the OEM partition of the intended device.

  --oem_no_mount
      For devices with OEM-specific properties but without an OEM partition,
      do not mount the OEM partition in the updater-script. This should be
      very rarely used, since it's expected to have a dedicated OEM partition
      for OEM-specific properties. Only meaningful when -o is specified.

  -w  (--wipe_user_data)
      Generate an OTA package that will wipe the user data partition
      when installed.

  --downgrade
      Intentionally generate an incremental OTA that updates from a newer
      build to an older one (based on timestamp comparison). "post-timestamp"
      will be replaced by "ota-downgrade=yes" in the metadata file. A data
      wipe will always be enforced, so "ota-wipe=yes" will also be included in
      the metadata file. The update-binary in the source build will be used in
      the OTA package, unless --binary flag is specified.

  -e  (--extra_script)  <file>
      Insert the contents of file at the end of the update script.

  -a  (--aslr_mode)  <on|off>
      Specify whether to turn on ASLR for the package (on by default).

  -2  (--two_step)
      Generate a 'two-step' OTA package, where recovery is updated
      first, so that any changes made to the system partition are done
      using the new recovery (new kernel, etc.).

  --block
      Generate a block-based OTA if possible.  Will fall back to a
      file-based OTA if the target_files is older and doesn't support
      block-based OTAs.

  -b  (--binary)  <file>
      Use the given binary as the update-binary in the output package,
      instead of the binary in the build's target_files.  Use for
      development only.

  -t  (--worker_threads) <int>
      Specifies the number of worker-threads that will be used when
      generating patches for incremental updates (defaults to 3).

  --stash_threshold <float>
      Specifies the threshold that will be used to compute the maximum
      allowed stash size (defaults to 0.8).

  --gen_verify
      Generate an OTA package that verifies the partitions.

  --log_diff <file>
      Generate a log file that shows the differences in the source and target
      builds for an incremental package. This option is only meaningful when
      -i is specified.

  --payload_signer <signer>
      Specify the signer when signing the payload and metadata for A/B OTAs.
      By default (i.e. without this flag), it calls 'openssl pkeyutl' to sign
      with the package private key. If the private key cannot be accessed
      directly, a payload signer that knows how to do that should be specified.
      The signer will be supplied with "-inkey <path_to_key>",
      "-in <input_file>" and "-out <output_file>" parameters.

  --payload_signer_args <args>
      Specify the arguments needed for payload signer.
"""

import sys

if sys.hexversion < 0x02070000:
  print >> sys.stderr, "Python 2.7 or newer is required."
  sys.exit(1)

import multiprocessing
import os
import subprocess
import shlex
import tempfile
import zipfile

import common
import edify_generator
import sparse_img

OPTIONS = common.OPTIONS
OPTIONS.package_key = None
OPTIONS.incremental_source = None
OPTIONS.verify = False
OPTIONS.require_verbatim = set()
OPTIONS.prohibit_verbatim = set(("system/build.prop",))
OPTIONS.patch_threshold = 0.95
OPTIONS.wipe_user_data = False
OPTIONS.downgrade = False
OPTIONS.extra_script = None
OPTIONS.aslr_mode = True
OPTIONS.worker_threads = multiprocessing.cpu_count() // 2
if OPTIONS.worker_threads == 0:
  OPTIONS.worker_threads = 1
OPTIONS.two_step = False
OPTIONS.no_signing = False
OPTIONS.block_based = False
OPTIONS.updater_binary = None
OPTIONS.oem_source = None
OPTIONS.oem_no_mount = False
OPTIONS.fallback_to_full = True
OPTIONS.full_radio = False
OPTIONS.full_bootloader = False
# Stash size cannot exceed cache_size * threshold.
OPTIONS.cache_size = None
OPTIONS.stash_threshold = 0.8
OPTIONS.gen_verify = False
OPTIONS.log_diff = None
OPTIONS.payload_signer = None
OPTIONS.payload_signer_args = []

def SignOutput(temp_zip_name, output_zip_name):
  key_passwords = common.GetKeyPasswords([OPTIONS.package_key])
  pw = key_passwords[OPTIONS.package_key]

  common.SignFile(temp_zip_name, output_zip_name, OPTIONS.package_key, pw,
                  whole_file=True)


def AppendAssertions(script, info_dict, oem_dict=None):
  oem_props = info_dict.get("oem_fingerprint_properties")
  if not oem_props:
    device = GetBuildProp("ro.product.device", info_dict)
    script.AssertDevice(device)
  else:
    if oem_dict is None:
      raise common.ExternalError(
          "No OEM file provided to answer expected assertions")
    for prop in oem_props.split():
      if oem_dict.get(prop) is None:
        raise common.ExternalError(
            "The OEM file is missing the property %s" % prop)
      script.AssertOemProperty(prop, oem_dict.get(prop))


def HasRecoveryPatch(target_files_zip):
  namelist = [name for name in target_files_zip.namelist()]
  return ("SYSTEM/recovery-from-boot.p" in namelist or
          "SYSTEM/etc/recovery.img" in namelist)

def HasVendorPartition(target_files_zip):
  try:
    target_files_zip.getinfo("VENDOR/")
    return True
  except KeyError:
    return False

def GetOemProperty(name, oem_props, oem_dict, info_dict):
  if oem_props is not None and name in oem_props:
    return oem_dict[name]
  return GetBuildProp(name, info_dict)


def CalculateFingerprint(oem_props, oem_dict, info_dict):
  if oem_props is None:
    return GetBuildProp("ro.build.fingerprint", info_dict)
  return "%s/%s/%s:%s" % (
      GetOemProperty("ro.product.brand", oem_props, oem_dict, info_dict),
      GetOemProperty("ro.product.name", oem_props, oem_dict, info_dict),
      GetOemProperty("ro.product.device", oem_props, oem_dict, info_dict),
      GetBuildProp("ro.build.thumbprint", info_dict))


def GetImage(which, tmpdir, info_dict):
  # Return an image object (suitable for passing to BlockImageDiff)
  # for the 'which' partition (most be "system" or "vendor").  If a
  # prebuilt image and file map are found in tmpdir they are used,
  # otherwise they are reconstructed from the individual files.

  assert which in ("system", "vendor")

  path = os.path.join(tmpdir, "IMAGES", which + ".img")
  mappath = os.path.join(tmpdir, "IMAGES", which + ".map")
  if os.path.exists(path) and os.path.exists(mappath):
    print "using %s.img" % (which,)
    # This is a 'new' target-files, which already has the image in it.

  else:
    print "cannot find %s.img" % (which,)
    sys.exit(1)

  # Bug: http://b/20939131
  # In ext4 filesystems, block 0 might be changed even being mounted
  # R/O. We add it to clobbered_blocks so that it will be written to the
  # target unconditionally. Note that they are still part of care_map.
  clobbered_blocks = "0"

  return sparse_img.SparseImage(path, mappath, clobbered_blocks)


def WriteMetadata(metadata, output_zip):
  common.ZipWriteStr(output_zip, "META-INF/com/android/metadata",
                     "".join(["%s=%s\n" % kv
                              for kv in sorted(metadata.iteritems())]))


def GetBuildProp(prop, info_dict):
  """Return the fingerprint of the build of a given target-files info_dict."""
  try:
    return info_dict.get("build.prop", {})[prop]
  except KeyError:
    raise common.ExternalError("couldn't find %s in build.prop" % (prop,))

def WriteBlockIncrementalOTAPackage(target_zip, source_zip, output_zip):
  # TODO(tbao): We should factor out the common parts between
  # WriteBlockIncrementalOTAPackage() and WriteIncrementalOTAPackage().
  source_version = OPTIONS.source_info_dict["recovery_api_version"]
  target_version = OPTIONS.target_info_dict["recovery_api_version"]

  if source_version == 0:
    print("WARNING: generating edify script for a source that "
          "can't install it.")
  script = edify_generator.EdifyGenerator(
      source_version, OPTIONS.target_info_dict,
      fstab=OPTIONS.source_info_dict["fstab"])

  recovery_mount_options = OPTIONS.source_info_dict.get(
      "recovery_mount_options")
  source_oem_props = OPTIONS.source_info_dict.get("oem_fingerprint_properties")
  target_oem_props = OPTIONS.target_info_dict.get("oem_fingerprint_properties")
  oem_dict = None
  if source_oem_props or target_oem_props:
    if OPTIONS.oem_source is None:
      raise common.ExternalError("OEM source required for this build")
    if not OPTIONS.oem_no_mount:
      script.Mount("/oem", recovery_mount_options)
    oem_dict = common.LoadDictionaryFromLines(
        open(OPTIONS.oem_source).readlines())

  metadata = {
      "pre-device": GetOemProperty("ro.product.device", source_oem_props,
                                   oem_dict, OPTIONS.source_info_dict),
      "ota-type": "BLOCK",
  }

  post_timestamp = GetBuildProp("ro.build.date.utc", OPTIONS.target_info_dict)
  pre_timestamp = GetBuildProp("ro.build.date.utc", OPTIONS.source_info_dict)
  is_downgrade = long(post_timestamp) < long(pre_timestamp)

  if OPTIONS.downgrade:
    metadata["ota-downgrade"] = "yes"
    if not is_downgrade:
      raise RuntimeError("--downgrade specified but no downgrade detected: "
                         "pre: %s, post: %s" % (pre_timestamp, post_timestamp))
  else:
    if is_downgrade:
      # Non-fatal here to allow generating such a package which may require
      # manual work to adjust the post-timestamp. A legit use case is that we
      # cut a new build C (after having A and B), but want to enfore the
      # update path of A -> C -> B. Specifying --downgrade may not help since
      # that would enforce a data wipe for C -> B update.
      print("\nWARNING: downgrade detected: pre: %s, post: %s.\n"
            "The package may not be deployed properly. "
            "Try --downgrade?\n" % (pre_timestamp, post_timestamp))
    metadata["post-timestamp"] = post_timestamp
  
  source_fp = CalculateFingerprint(source_oem_props, oem_dict,
                                   OPTIONS.source_info_dict)
  target_fp = CalculateFingerprint(target_oem_props, oem_dict,
                                   OPTIONS.target_info_dict)
  metadata["pre-build"] = source_fp
  metadata["post-build"] = target_fp
  metadata["pre-build-incremental"] = GetBuildProp(
      "ro.build.version.incremental", OPTIONS.source_info_dict)
  metadata["post-build-incremental"] = GetBuildProp(
      "ro.build.version.incremental", OPTIONS.target_info_dict)

  source_boot = common.GetBootableImage(
      "/tmp/boot.img", "boot.img", OPTIONS.source_tmp, "BOOT",
      OPTIONS.source_info_dict)
  target_boot = common.GetBootableImage(
      "/tmp/boot.img", "boot.img", OPTIONS.target_tmp, "BOOT")
  updating_boot = (not OPTIONS.two_step and
                   (source_boot.data != target_boot.data))

  target_recovery = common.GetBootableImage(
      "/tmp/recovery.img", "recovery.img", OPTIONS.target_tmp, "RECOVERY")

  system_src = GetImage("system", OPTIONS.source_tmp, OPTIONS.source_info_dict)
  print("got source")
  system_tgt = GetImage("system", OPTIONS.target_tmp, OPTIONS.target_info_dict)
  print("got target")

  blockimgdiff_version = 1
  if OPTIONS.info_dict:
    blockimgdiff_version = max(
        int(i) for i in
        OPTIONS.info_dict.get("blockimgdiff_versions", "1").split(","))

  # Check the first block of the source system partition for remount R/W only
  # if the filesystem is ext4.
  system_src_partition = OPTIONS.source_info_dict["fstab"]["/system"]
  check_first_block = system_src_partition.fs_type == "ext4"
  # Disable using imgdiff for squashfs. 'imgdiff -z' expects input files to be
  # in zip formats. However with squashfs, a) all files are compressed in LZ4;
  # b) the blocks listed in block map may not contain all the bytes for a given
  # file (because they're rounded to be 4K-aligned).
  system_tgt_partition = OPTIONS.target_info_dict["fstab"]["/system"]
  disable_imgdiff = (system_src_partition.fs_type == "squashfs" or
                     system_tgt_partition.fs_type == "squashfs")
  system_diff = common.BlockDifference("system", system_tgt, system_src,
                                       check_first_block,
                                       version=blockimgdiff_version,
                                       disable_imgdiff=disable_imgdiff)

  #TODO - if vendor partition is present
  """
  if HasVendorPartition(target_zip):
    if not HasVendorPartition(source_zip):
      raise RuntimeError("can't generate incremental that adds /vendor")
    vendor_src = GetImage("vendor", OPTIONS.source_tmp,
                          OPTIONS.source_info_dict)
    vendor_tgt = GetImage("vendor", OPTIONS.target_tmp,
                          OPTIONS.target_info_dict)

    # Check first block of vendor partition for remount R/W only if
    # disk type is ext4
    vendor_partition = OPTIONS.source_info_dict["fstab"]["/vendor"]
    check_first_block = vendor_partition.fs_type == "ext4"
    disable_imgdiff = vendor_partition.fs_type == "squashfs"
    vendor_diff = common.BlockDifference("vendor", vendor_tgt, vendor_src,
                                         check_first_block,
                                         version=blockimgdiff_version,
                                         disable_imgdiff=disable_imgdiff)
  else:
  """
  vendor_diff = None

  AppendAssertions(script, OPTIONS.target_info_dict, oem_dict)
  

  # Dump fingerprints
  script.Print(source_fp)
  script.Print(target_fp)

  script.Print("Verifying current system...")

  # device_specific.IncrementalOTA_VerifyBegin()
  print("IncrementalOTA_VerifyBegin")
  # When blockimgdiff version is less than 3 (non-resumable block-based OTA),
  # patching on a device that's already on the target build will damage the
  # system. Because operations like move don't check the block state, they
  # always apply the changes unconditionally.
  if blockimgdiff_version <= 2:
    if source_oem_props is None:
      script.AssertSomeFingerprint(source_fp)
    else:
      script.AssertSomeThumbprint(
          GetBuildProp("ro.build.thumbprint", OPTIONS.source_info_dict))

  else: # blockimgdiff_version > 2
    if source_oem_props is None and target_oem_props is None:
      script.AssertSomeFingerprint(source_fp, target_fp)
    elif source_oem_props is not None and target_oem_props is not None:
      script.AssertSomeThumbprint(
          GetBuildProp("ro.build.thumbprint", OPTIONS.target_info_dict),
          GetBuildProp("ro.build.thumbprint", OPTIONS.source_info_dict))
    elif source_oem_props is None and target_oem_props is not None:
      script.AssertFingerprintOrThumbprint(
          source_fp,
          GetBuildProp("ro.build.thumbprint", OPTIONS.target_info_dict))
    else:
      script.AssertFingerprintOrThumbprint(
          target_fp,
          GetBuildProp("ro.build.thumbprint", OPTIONS.source_info_dict))

  # Check the required cache size (i.e. stashed blocks).
  size = []
  if system_diff:
    size.append(system_diff.required_cache)
  if vendor_diff:
    size.append(vendor_diff.required_cache)

  if updating_boot:
    boot_type, boot_device = common.GetTypeAndDevice(
        "/boot", OPTIONS.source_info_dict)
    d = common.Difference(target_boot, source_boot)
    _, _, d = d.ComputePatch()
    if d is None:
      include_full_boot = True
      common.ZipWriteStr(output_zip, "boot.img", target_boot.data)
    else:
      include_full_boot = False

      print "boot      target: %d  source: %d  diff: %d" % (
          target_boot.size, source_boot.size, len(d))

      common.ZipWriteStr(output_zip, "patch/boot.img.p", d)

      script.PatchCheck("%s:%s:%d:%s:%d:%s" %
                        (boot_type, boot_device,
                         source_boot.size, source_boot.sha1,
                         target_boot.size, target_boot.sha1))
      size.append(target_boot.size)

  if size:
    script.CacheFreeSpaceCheck(max(size))

  # device_specific.IncrementalOTA_VerifyEnd()
  print("IncrementalOTA_VerifyEnd")

  # Verify the existing partitions.
  system_diff.WriteVerifyScript(script, touched_blocks_only=True)
  if vendor_diff:
    vendor_diff.WriteVerifyScript(script, touched_blocks_only=True)

  script.Comment("---- start making changes here ----")

  # device_specific.IncrementalOTA_InstallBegin()
  print("IncrementalOTA_InstallBegin")
  system_diff.WriteScript(script, output_zip,
                          progress=0.8 if vendor_diff else 0.9)

  if vendor_diff:
    vendor_diff.WriteScript(script, output_zip, progress=0.1)

  if not OPTIONS.two_step:
    if updating_boot:
      if include_full_boot:
        print "boot image changed; including full."
        script.Print("Installing boot image...")
        script.WriteRawImage("/boot", "boot.img")
      else:
        # Produce the boot image by applying a patch to the current
        # contents of the boot partition, and write it back to the
        # partition.
        print "boot image changed; including patch."
        script.Print("Patching boot image...")
        script.ShowProgress(0.1, 10)
        script.ApplyPatch("%s:%s:%d:%s:%d:%s"
                          % (boot_type, boot_device,
                             source_boot.size, source_boot.sha1,
                             target_boot.size, target_boot.sha1),
                          "-",
                          target_boot.size, target_boot.sha1,
                          source_boot.sha1, "patch/boot.img.p")
    else:
      print "boot image unchanged; skipping."

  # Do device-specific installation (eg, write radio image).
  # device_specific.IncrementalOTA_InstallEnd()
  print("IncrementalOTA_InstallEnd")
  
  if OPTIONS.extra_script is not None:
    script.AppendExtra(OPTIONS.extra_script)

  if OPTIONS.wipe_user_data:
    script.Print("Erasing user data...")
    script.FormatPartition("/data")
    metadata["ota-wipe"] = "yes"

  script.SetProgress(1)
  # For downgrade OTAs, we prefer to use the update-binary in the source
  # build that is actually newer than the one in the target build.
  if OPTIONS.downgrade:
    script.AddToZip(source_zip, output_zip, input_path=OPTIONS.updater_binary)
  else:
    script.AddToZip(target_zip, output_zip, input_path=OPTIONS.updater_binary)
  metadata["ota-required-cache"] = str(script.required_cache)
  WriteMetadata(metadata, output_zip)


def WriteIncrementalOTAPackage(target_zip, source_zip, output_zip):
  target_has_recovery_patch = HasRecoveryPatch(target_zip)
  source_has_recovery_patch = HasRecoveryPatch(source_zip)

  # if (OPTIONS.block_based and
      # target_has_recovery_patch and
      # source_has_recovery_patch):
  return WriteBlockIncrementalOTAPackage(target_zip, source_zip, output_zip)

def main(argv):

  def option_handler(o, a):
    if o == "--board_config":
      pass   # deprecated
    elif o in ("-k", "--package_key"):
      OPTIONS.package_key = a
    elif o in ("-i", "--incremental_from"):
      OPTIONS.incremental_source = a
    elif o == "--full_radio":
      OPTIONS.full_radio = True
    elif o == "--full_bootloader":
      OPTIONS.full_bootloader = True
    elif o in ("-w", "--wipe_user_data"):
      OPTIONS.wipe_user_data = True
    elif o == "--downgrade":
      OPTIONS.downgrade = True
      OPTIONS.wipe_user_data = True
    elif o in ("-o", "--oem_settings"):
      OPTIONS.oem_source = a
    elif o == "--oem_no_mount":
      OPTIONS.oem_no_mount = True
    elif o in ("-e", "--extra_script"):
      OPTIONS.extra_script = a
    elif o in ("-a", "--aslr_mode"):
      if a in ("on", "On", "true", "True", "yes", "Yes"):
        OPTIONS.aslr_mode = True
      else:
        OPTIONS.aslr_mode = False
    elif o in ("-t", "--worker_threads"):
      if a.isdigit():
        OPTIONS.worker_threads = int(a)
      else:
        raise ValueError("Cannot parse value %r for option %r - only "
                         "integers are allowed." % (a, o))
    elif o in ("-2", "--two_step"):
      OPTIONS.two_step = True
    elif o == "--no_signing":
      OPTIONS.no_signing = True
    elif o == "--verify":
      OPTIONS.verify = True
    elif o == "--block":
      OPTIONS.block_based = True
    elif o in ("-b", "--binary"):
      OPTIONS.updater_binary = a
    elif o in ("--no_fallback_to_full",):
      OPTIONS.fallback_to_full = False
    elif o == "--stash_threshold":
      try:
        OPTIONS.stash_threshold = float(a)
      except ValueError:
        raise ValueError("Cannot parse value %r for option %r - expecting "
                         "a float" % (a, o))
    elif o == "--gen_verify":
      OPTIONS.gen_verify = True
    elif o == "--log_diff":
      OPTIONS.log_diff = a
    elif o == "--payload_signer":
      OPTIONS.payload_signer = a
    elif o == "--payload_signer_args":
      OPTIONS.payload_signer_args = shlex.split(a)
    else:
      return False
    return True

  args = common.ParseOptions(argv, __doc__,
                             extra_opts="b:k:i:d:we:t:a:2o:",
                             extra_long_opts=[
                                 "board_config=",
                                 "package_key=",
                                 "incremental_from=",
                                 "full_radio",
                                 "full_bootloader",
                                 "wipe_user_data",
                                 "downgrade",
                                 "extra_script=",
                                 "worker_threads=",
                                 "aslr_mode=",
                                 "two_step",
                                 "no_signing",
                                 "block",
                                 "binary=",
                                 "oem_settings=",
                                 "oem_no_mount",
                                 "verify",
                                 "no_fallback_to_full",
                                 "stash_threshold=",
                                 "gen_verify",
                                 "log_diff=",
                                 "payload_signer=",
                                 "payload_signer_args=",
                             ], extra_option_handler=option_handler)

  if len(args) != 2:
    common.Usage(__doc__)
    sys.exit(1)

  if OPTIONS.downgrade:
    # Sanity check to enforce a data wipe.
    if not OPTIONS.wipe_user_data:
      raise ValueError("Cannot downgrade without a data wipe")

    # We should only allow downgrading incrementals (as opposed to full).
    # Otherwise the device may go back from arbitrary build with this full
    # OTA package.
    if OPTIONS.incremental_source is None:
      raise ValueError("Cannot generate downgradable full OTAs")

  # Load the dict file from the zip directly to have a peek at the OTA type.
  # For packages using A/B update, unzipping is not needed.
  print "unzipping target target-files..."
  OPTIONS.input_tmp, input_zip = common.UnzipTemp(args[0])
  input_zip1 = zipfile.ZipFile(args[0], "r")
  OPTIONS.info_dict = common.LoadInfoDict(input_zip1, args[0], OPTIONS.input_tmp)
  common.ZipClose(input_zip1)

  common.Mountext4("system.img", OPTIONS.input_tmp)
  OPTIONS.target_tmp = OPTIONS.input_tmp
  OPTIONS.info_dict = common.LoadInfoDict(input_zip, args[0], OPTIONS.target_tmp, OPTIONS.target_tmp)

  if OPTIONS.verbose:
    print "--- target info ---"
    common.DumpInfoDict(OPTIONS.info_dict)

  if OPTIONS.info_dict.get("no_recovery") == "true":
    raise common.ExternalError(
        "--- target build has specified no recovery ---")

  # Use the default key to sign the package if not specified with package_key.
  if not OPTIONS.no_signing:
    if OPTIONS.package_key is None:
      OPTIONS.package_key = OPTIONS.info_dict.get(
          "default_system_dev_certificate",
          "build/target/product/security/testkey")

  # Set up the output zip. Create a temporary zip file if signing is needed.
  if OPTIONS.no_signing:
    if os.path.exists(args[1]):
      os.unlink(args[1])
    output_zip = zipfile.ZipFile(args[1], "w",
                                 compression=zipfile.ZIP_DEFLATED)
  else:
    temp_zip_file = tempfile.NamedTemporaryFile()
    output_zip = zipfile.ZipFile(temp_zip_file, "w",
                                 compression=zipfile.ZIP_DEFLATED)

  # Non A/B OTAs rely on /cache partition to store temporary files.
  cache_size = OPTIONS.info_dict.get("cache_size", None)
  if cache_size is None:
    print "--- can't determine the cache partition size ---"
  OPTIONS.cache_size = cache_size

  # Generate an incremental OTA. It will fall back to generate a full OTA on
  # failure unless no_fallback_to_full is specified.
  print "unzipping source target-files..."
  OPTIONS.source_tmp, source_zip = common.UnzipTemp(
      OPTIONS.incremental_source)
  common.Mountext4("system.img", OPTIONS.source_tmp)
  OPTIONS.target_info_dict = OPTIONS.info_dict
  OPTIONS.source_info_dict = common.LoadInfoDict(source_zip, OPTIONS.incremental_source, OPTIONS.source_tmp, OPTIONS.source_tmp)
  if OPTIONS.verbose:
    print "--- source info ---"
    common.DumpInfoDict(OPTIONS.source_info_dict)
  try:
    WriteIncrementalOTAPackage(input_zip, source_zip, output_zip)
    if OPTIONS.log_diff:
      out_file = open(OPTIONS.log_diff, 'w')
      import target_files_diff
      target_files_diff.recursiveDiff('',
                                      OPTIONS.source_tmp,
                                      OPTIONS.input_tmp,
                                      out_file)
      out_file.close()
  except ValueError as e:
    if not OPTIONS.fallback_to_full:
      raise
    print "--- failed to build incremental ---:",e
    sys.exit(1)

  common.ZipClose(output_zip)

  # Sign the generated zip package unless no_signing is specified.
  if not OPTIONS.no_signing:
    SignOutput(temp_zip_file.name, args[1])
    temp_zip_file.close()

  print "done."


if __name__ == '__main__':
  try:
    common.CloseInheritedPipes()
    main(sys.argv[1:])
  except common.ExternalError as e:
    print
    print "   ERROR: %s" % (e,)
    print
    sys.exit(1)
  finally:
    common.Cleanup()
