#
# Copyright (C) 2016 Eddi De Pieri <eddi@depieri.net>
# Copyright (C) 2015 Gilles Mazoyer <mazoyer.gilles@omega.ovh>
#
# This is free software, licensed under the GNU General Public License v2.
# See /LICENSE for more information.
#

include $(TOPDIR)/rules.mk
include $(INCLUDE_DIR)/kernel.mk

PKG_NAME:=asterisk13-chan-lantiq
PKG_RELEASE:=$(LINUX_VERSION)

PKG_BUILD_DIR := $(BUILD_DIR)/asterisk-13-chan-lantiq

include $(INCLUDE_DIR)/package.mk

define Package/asterisk13-chan-lantiq
  SECTION:=net
  CATEGORY:=Network
  SUBMENU:=Telephony
  DEPENDS:=@(TARGET_lantiq_falcon||TARGET_lantiq_xway||TARGET_lantiq_xrx200) \
		asterisk13 +asterisk13-codec-alaw +asterisk13-codec-a-mu \
		+asterisk13-format-sln +asterisk13-res-musiconhold +kmod-ltq-tapi
  TITLE:=lantiq channel
  VERSION:=$(LINUX_VERSION)-$(PKG_RELEASE)
  URL:=https://github.com/avlasic/asterisk_channel_lantiq.git
endef

define Package/asterisk13-chan-lantiq/description
  Asterisk 13 channel using lantiq kernel module
endef

define Build/Prepare
	mkdir -p $(PKG_BUILD_DIR)/src
	$(CP) ../src/* $(PKG_BUILD_DIR)/src/
	mkdir -p $(PKG_BUILD_DIR)/configs
	$(CP) ../configs/* $(PKG_BUILD_DIR)/configs/
	mkdir -p $(PKG_BUILD_DIR)/obj
endef

define Build/Configure
endef

define Build/Compile
	rm -f $(PKG_BUILD_DIR)/obj/* $(PKG_BUILD_DIR)/*.so
	$(TARGET_CC) $(TARGET_CFLAGS) -DBCMPH_DEBUG -DAST_VERSION=130 -DLOW_MEMORY -D_FORTIFY_SOURCE=2\
		-I$(BUILD_DIR)/lantiq/inc \
		-I$(STAGING_DIR)/usr/include/asterisk-13/include \
		-Wall -Wstrict-prototypes -Wmissing-prototypes -Wmissing-declarations \
		-fPIC -pthread \
		-c $(PKG_BUILD_DIR)/src/chan_lantiq.c \
		-o $(PKG_BUILD_DIR)/obj/chan_lantiq.o
	$(TARGET_CC) $(TARGET_LDFLAGS) -shared -fPIC -pthread \
		$(PKG_BUILD_DIR)/obj/chan_lantiq.o \
		-o $(PKG_BUILD_DIR)/chan_lantiq.so
endef

define Package/asterisk13-chan-lantiq/install
	$(INSTALL_DIR) $(1)/etc/asterisk
	$(INSTALL_DATA) $(PKG_BUILD_DIR)/configs/lantiq.conf.sample $(1)/etc/asterisk/
	$(INSTALL_DIR) $(1)/usr/lib/asterisk/modules
	$(INSTALL_BIN) $(PKG_BUILD_DIR)/chan_lantiq.so $(1)/usr/lib/asterisk/modules/
endef

$(eval $(call BuildPackage,asterisk13-chan-lantiq))
