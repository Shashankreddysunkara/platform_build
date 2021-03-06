# Install jni libraries for one arch.
# Input variables:
#   my_2nd_arch_prefix: indicate if this is for TARGET_2ND_ARCH.
#   my_embed_jni: indicate if we want to embed the jni libs in the apk.
#   my_prebuilt_jni_libs
#   my_installed_module_stem (from configure_module_stem.mk)
#   partition_tag (from base_rules.mk)
#   my_prebuilt_src_file (from prebuilt_internal.mk)
#
# Output variables:
#   my_jni_shared_libraries, my_jni_shared_libraries_abi, if we are going to embed the libraries into the apk;
#   my_embedded_prebuilt_jni_libs, prebuilt jni libs embedded in prebuilt apk.
#

my_jni_shared_libraries := \
    $(addprefix $($(my_2nd_arch_prefix)TARGET_OUT_INTERMEDIATE_LIBRARIES)/, \
      $(addsuffix .so, \
          $(LOCAL_JNI_SHARED_LIBRARIES)))

# App-specific lib path.
my_app_lib_path := $(dir $(LOCAL_INSTALLED_MODULE))lib/$(TARGET_$(my_2nd_arch_prefix)ARCH)
my_embedded_prebuilt_jni_libs :=

ifdef my_embed_jni
# App explicitly requires the prebuilt NDK stl shared libraies.
# The NDK stl shared libraries should never go to the system image.
ifneq ($(filter $(LOCAL_NDK_STL_VARIANT), stlport_shared c++_shared),)
ifndef LOCAL_SDK_VERSION
$(error LOCAL_SDK_VERSION must be defined with LOCAL_NDK_STL_VARIANT, \
    LOCAL_PACKAGE_NAME=$(LOCAL_PACKAGE_NAME))
endif
endif
ifeq (stlport_shared,$(LOCAL_NDK_STL_VARIANT))
my_jni_shared_libraries += \
    $(HISTORICAL_NDK_VERSIONS_ROOT)/$(LOCAL_NDK_VERSION)/sources/cxx-stl/stlport/libs/$(TARGET_$(my_2nd_arch_prefix)CPU_ABI)/libstlport_shared.so
else ifeq (c++_shared,$(LOCAL_NDK_STL_VARIANT))
my_jni_shared_libraries += \
    $(HISTORICAL_NDK_VERSIONS_ROOT)/$(LOCAL_NDK_VERSION)/sources/cxx-stl/llvm-libc++/libs/$(TARGET_$(my_2nd_arch_prefix)CPU_ABI)/libc++_shared.so
endif

# Set the abi directory used by the local JNI shared libraries.
# (Doesn't change how the local shared libraries are compiled, just
# sets where they are stored in the apk.)
ifeq ($(LOCAL_JNI_SHARED_LIBRARIES_ABI),)
    my_jni_shared_libraries_abi := $(TARGET_$(my_2nd_arch_prefix)CPU_ABI)
else
    my_jni_shared_libraries_abi := $(LOCAL_JNI_SHARED_LIBRARIES_ABI)
endif

else  # not my_embed_jni

my_jni_shared_libraries := $(strip $(my_jni_shared_libraries))
ifneq ($(my_jni_shared_libraries),)
# The jni libaries will be installed to the system.img.
my_jni_filenames := $(notdir $(my_jni_shared_libraries))
# Make sure the JNI libraries get installed
my_shared_library_path := $($(my_2nd_arch_prefix)TARGET_OUT$(partition_tag)_SHARED_LIBRARIES)
# Do not use order-only dependency, because we want to rebuild the image if an jni is updated.
$(LOCAL_INSTALLED_MODULE) : $(addprefix $(my_shared_library_path)/, $(my_jni_filenames))

# Create symlink in the app specific lib path
ifdef LOCAL_POST_INSTALL_CMD
# Add a shell command separator
LOCAL_POST_INSTALL_CMD += ;
endif

my_symlink_target_dir := $(patsubst $(PRODUCT_OUT)%,%,\
    $(my_shared_library_path))
LOCAL_POST_INSTALL_CMD += \
  mkdir -p $(my_app_lib_path) \
  $(foreach lib, $(my_jni_filenames), ;ln -sf $(my_symlink_target_dir)/$(lib) $(my_app_lib_path)/$(lib))
$(LOCAL_INSTALLED_MODULE): PRIVATE_POST_INSTALL_CMD := $(LOCAL_POST_INSTALL_CMD)

# Clear jni_shared_libraries to not embed it into the apk.
my_jni_shared_libraries :=
endif  # $(my_jni_shared_libraries) not empty
endif  # my_embed_jni

ifdef my_prebuilt_jni_libs
# Files like @lib/<abi>/libfoo.so (path inside the apk) are JNI libs embedded prebuilt apk;
# Files like path/to/libfoo.so (path relative to LOCAL_PATH) are prebuilts in the source tree.
my_embedded_prebuilt_jni_libs := $(patsubst @%,%, \
    $(filter @%, $(my_prebuilt_jni_libs)))

# prebuilt JNI exsiting as separate source files.
my_prebuilt_jni_libs := $(addprefix $(LOCAL_PATH)/, \
    $(filter-out @%, $(my_prebuilt_jni_libs)))
ifdef my_prebuilt_jni_libs
ifdef my_embed_jni
# Embed my_prebuilt_jni_libs to the apk
my_jni_shared_libraries += $(my_prebuilt_jni_libs)
else # not my_embed_jni
# Install my_prebuilt_jni_libs as separate files.
$(foreach lib, $(my_prebuilt_jni_libs), \
    $(eval $(call copy-one-file, $(lib), $(my_app_lib_path)/$(notdir $(lib)))))

$(LOCAL_INSTALLED_MODULE) : $(addprefix $(my_app_lib_path)/, $(notdir $(my_prebuilt_jni_libs)))
endif  # my_embed_jni
endif  # inner my_prebuilt_jni_libs
endif  # outer my_prebuilt_jni_libs

# Verify that all included libraries are built against the NDK
ifneq ($(strip $(LOCAL_JNI_SHARED_LIBRARIES)),)
my_link_type := $(call intermediates-dir-for,APPS,$(LOCAL_MODULE))/$(my_2nd_arch_prefix)jni_link_type
my_link_type_deps := $(strip \
  $(foreach l,$(LOCAL_JNI_SHARED_LIBRARIES),\
    $(call intermediates-dir-for,SHARED_LIBRARIES,$(l),,,$(my_2nd_arch_prefix))/link_type))
ifneq ($(LOCAL_SDK_VERSION),)
$(my_link_type): PRIVATE_LINK_TYPE := sdk
$(my_link_type): PRIVATE_ALLOWED_TYPES := ndk
else
$(my_link_type): PRIVATE_LINK_TYPE := platform
$(my_link_type): PRIVATE_ALLOWED_TYPES := (ndk|platform)
endif
$(my_link_type): PRIVATE_DEPS := $(my_link_type_deps)
$(my_link_type): PRIVATE_MODULE := $(LOCAL_MODULE)
$(my_link_type): PRIVATE_MAKEFILE := $(LOCAL_MODULE_MAKEFILE)
$(my_link_type): $(my_link_type_deps)
	@echo Check JNI module types: $@
	$(hide) mkdir -p $(dir $@)
	$(hide) rm -f $@
	$(hide) for f in $(PRIVATE_DEPS); do \
	  grep -qE '^$(PRIVATE_ALLOWED_TYPES)$$' $$f || \
	    $(call echo-warning,"$(PRIVATE_MAKEFILE): $(PRIVATE_MODULE) ($(PRIVATE_LINK_TYPE)) should not link to $$(basename $${f%_intermediates/link_type}) ($$(cat $$f))"); \
	done
	$(hide) touch $@

$(LOCAL_BUILT_MODULE): | $(my_link_type)

my_link_type :=
my_link_type_deps :=
endif
