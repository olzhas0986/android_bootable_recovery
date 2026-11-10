/*
	Copyright 2012 to 2017 bigbiff/Dees_Troy TeamWin
	This file is part of TWRP/TeamWin Recovery Project.

	Copyright (C) 2018-2025 OrangeFox Recovery Project
	This file is part of the OrangeFox Recovery Project.

	TWRP is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	TWRP is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with TWRP.  If not, see <http://www.gnu.org/licenses/>.
*/

/*
 * High-speed full OTA support, adapted from khargosxh18/android_bootable_recovery_fox.
 * This file is part of TWRP, distributed under GPL-3.0-or-later.
 */
#include "highspeed.hpp"
#include "highspeed_manifest.hpp"
#include <algorithm>
#include <cctype>
#include <cerrno>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <fstream>
#include <map>
#include <set>
#include <string>
#include <vector>
#include <fcntl.h>
#include <linux/fs.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/sysmacros.h>
#include <sys/wait.h>
#include <unistd.h>
#include <android-base/properties.h>
#include <android-base/strings.h>
#include <android-base/unique_fd.h>
#include <openssl/sha.h>
#include "highspeed_metadata.pb.h"
#include "data.hpp"
#include "variables.h"
#include "partitions.hpp"
#include "twcommon.h"
#include "twrp-functions.hpp"
#include "gui/gui.hpp"
extern "C" {
#include "gui/gui.h"
}

namespace {

const char* kHighSpeedExtractorPath = "/system/bin/otaripper";

std::string g_hs_reason;

void HsWhy(const std::string& why) { g_hs_reason = why; }
void HsSay(Message text) { gui_msg(text); }
void HsLog(const std::string& text) { LOGINFO("high-speed: %s\n", text.c_str()); }
void HsFail(const std::string& what) { gui_msg(Msg(msg::kError, "high_speed_error=High speed flash failed: {1}")(what)); }

std::string HsSize(uint64_t bytes) {
	char buf[32];
	if (bytes >= (1ULL << 30))
		snprintf(buf, sizeof(buf), "%.2f GiB", bytes / double(1ULL << 30));
	else
		snprintf(buf, sizeof(buf), "%.0f MiB", bytes / double(1ULL << 20));
	return buf;
}

std::string HsTrim(std::string line) {
	if (line.compare(0, 6, "ERROR:") == 0)
		line.erase(0, 6);
	while (!line.empty() && line.front() == ' ')
		line.erase(0, 1);
	if (line.size() > 120) {
		line.resize(117);
		line += "...";
	}
	return line;
}

const size_t kPayloadMagicSize = 4;
const size_t kPayloadVersionSize = 8;
const size_t kPayloadManifestSizeSize = 8;
const size_t kPayloadSignatureSizeSize = 4;

// boot-chain images an A/B ROM ships (same names on every vendor).
// any other physical partition in the payload is treated as firmware,
// since those names depend on the SoC.
bool IsBootChainPartition(const std::string& name) {
	static const std::set<std::string> boot_chain = {
		"boot", "init_boot", "vendor_boot", "vendor_kernel_boot", "dtbo",
		"recovery", "pvmfw",
	};
	return boot_chain.count(name) > 0 || name == "vbmeta" || name.compare(0, 7, "vbmeta_") == 0;
}

// identity, calibration and user data. an OTA never has these, so if the
// payload does, stop. also rejects names that already have a slot suffix.
bool IsValidHighSpeedName(const std::string& name) {
	return !name.empty() && name.size() <= 34 &&
		std::all_of(name.begin(), name.end(), [](unsigned char c) {
			return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
			       (c >= '0' && c <= '9') || c == '_';
		});
}

bool IsProtectedPartition(const std::string& name) {
	static const std::set<std::string> protected_names = {
		"super", "userdata", "metadata", "misc", "persist", "cache", "frp",
		"devinfo", "modemst1", "modemst2", "fsg", "fsc", "keystore", "config",
	};
	if (protected_names.count(name))
		return true;
	return name.size() > 2 &&
		(name.compare(name.size() - 2, 2, "_a") == 0 || name.compare(name.size() - 2, 2, "_b") == 0);
}

struct HighSpeedPartitionPlan {
	std::string name;          // bare partition name from the payload manifest
	std::string target_path;   // "/" + name, for the fstab slot lookup
	uint64_t expanded_size = 0; // decompressed size, straight from the manifest
	bool is_logical = false;   // true if this one lives in Super (needs the group rebuild)
	bool is_firmware = false;  // physical, not boot chain
	std::string sha256;        // SHA-256 from the manifest, raw bytes
};

// the dynamic-partition group the payload's manifest puts the logical
// partitions in. name is bare (no slot suffix), size is the budget the ROM
// was built for. empty/0 means the manifest didn't say.
struct HighSpeedGroupSpec {
	std::string name;
	uint64_t size = 0;
};

uint64_t ReadBigEndian64(const uint8_t* p) {
	uint64_t v = 0;
	for (int i = 0; i < 8; i++)
		v = (v << 8) | p[i];
	return v;
}

// which slot recovery itself booted from -- that slot must never be
// written. ro.boot.slot_suffix is authoritative (the slot menu can change
// the *bootloader's* active slot without changing what we booted from);
// fall back to the manager's notion of the active slot only if the
// property is missing. returns "A", "B", or "" if it can't be known.
std::string DetermineBootedSlot() {
	std::string prop = android::base::GetProperty("ro.boot.slot_suffix", "");
	std::string display = PartitionManager.Get_Active_Slot_Display();
	if (prop == "_a" || prop == "_b") {
		std::string from_prop = (prop == "_a") ? "A" : "B";
		if (!display.empty() && display != from_prop)
			LOGINFO("high-speed: active slot display is '%s' but recovery booted from '%s' -- treating '%s' as the booted slot\n",
				display.c_str(), from_prop.c_str(), from_prop.c_str());
		return from_prop;
	}

	return "";
}

// resolves symlinks and only succeeds if the final target is a block device
bool ResolveBlockNode(const std::string& path, std::string* real) {
	char buf[PATH_MAX];
	if (realpath(path.c_str(), buf) == nullptr)
		return false;
	struct stat st;
	if (stat(buf, &st) != 0 || !S_ISBLK(st.st_mode))
		return false;
	*real = buf;
	return true;
}

bool GetBlockDeviceSize(const std::string& path, uint64_t* size) {
	android::base::unique_fd fd(open(path.c_str(), O_RDONLY | O_CLOEXEC));
	if (fd == -1)
		return false;
	uint64_t bytes = 0;
	if (ioctl(fd.get(), BLKGETSIZE64, &bytes) != 0)
		return false;
	*size = bytes;
	return true;
}

// extra checks for firmware targets, a bad write can't be undone there:
// must be a real partition (not a whole disk), kernel PARTNAME must match
// <name><target suffix>, and it must be writable
bool VerifyFirmwareNode(const std::string& node, const std::string& expected_partname) {
	struct stat st;
	if (stat(node.c_str(), &st) != 0 || !S_ISBLK(st.st_mode))
		return false;
	const std::string sys = "/sys/dev/block/" + std::to_string(major(st.st_rdev)) + ":" +
		std::to_string(minor(st.st_rdev));
	if (access((sys + "/partition").c_str(), F_OK) != 0) {
		HsWhy("'" + expected_partname + "' is not a kernel partition");
		return false;
	}
	std::string partname, line;
	std::ifstream uevent(sys + "/uevent");
	while (std::getline(uevent, line))
		if (line.compare(0, 9, "PARTNAME=") == 0)
			partname = line.substr(9);
	if (partname != expected_partname) {
		HsWhy("kernel names the target '" + partname + "', expected '" + expected_partname + "'");
		return false;
	}
	android::base::unique_fd fd(open(node.c_str(), O_RDONLY | O_CLOEXEC));
	int read_only = 1;
	if (fd == -1 || ioctl(fd.get(), BLKROGET, &read_only) != 0 || read_only != 0) {
		HsWhy("'" + expected_partname + "' is read-only");
		return false;
	}
	return true;
}

// re-reads the first `size` bytes of the device from storage (cache
// dropped) and compares the SHA-256 with the manifest. separate from the
// extractor's own check on purpose.
bool VerifyDeviceSha256(int fd, uint64_t size, const std::string& expected) {
	if (expected.size() != SHA256_DIGEST_LENGTH || size == 0)
		return false;
	if (ioctl(fd, BLKFLSBUF, 0) != 0)
		return false;
	SHA256_CTX ctx;
	SHA256_Init(&ctx);
	std::vector<uint8_t> buf(4 << 20);
	uint64_t offset = 0;
	while (offset < size) {
		size_t want = (size_t)std::min<uint64_t>(buf.size(), size - offset);
		ssize_t got = pread(fd, buf.data(), want, offset);
		if (got < 0 && errno == EINTR)
			continue;
		if (got <= 0)
			return false;
		SHA256_Update(&ctx, buf.data(), (size_t)got);
		offset += (uint64_t)got;
	}
	uint8_t digest[SHA256_DIGEST_LENGTH];
	SHA256_Final(digest, &ctx);
	return memcmp(digest, expected.data(), sizeof(digest)) == 0;
}

// works out the exact node a physical (boot/dtbo/vbmeta...) partition
// must be written to on the TARGET slot, without touching any global slot state.
// The node name is built from the partition's own name, like
// <by-name dir><name><target suffix>. It is not built from TWPartition's
// Primary_Block_Device. Once recovery has restarted, TWRP has already
// pointed the slot-less by-name link at the booted slot and keeps the
// resolved node (for example /dev/block/sde12). Adding a suffix to that
// names a node that does not exist.
//
// Every check here fails closed. The target must be a real block device,
// and the booted slot's node must be found and must be a different device.
bool ResolvePhysicalTarget(const HighSpeedPartitionPlan& part, const std::string& booted_suffix,
                           const std::string& target_suffix, std::string* node) {
	if (part.name.empty() || part.name.find('/') != std::string::npos ||
	    part.name.find("..") != std::string::npos) {
		HsWhy("'" + part.name + "' is not a usable partition name");
		return false;
	}

	// if the fstab knows this partition, it has to be a slot-select one.
	// only the flag is used here, never its block device path.
	TWPartition* twp = PartitionManager.Find_Partition_By_Path(part.target_path);
	if (twp && !twp->Is_SlotSelect()) {
		HsWhy("'" + part.name + "' is not a slot-select partition on this device");
		return false;
	}

	static const char* kByNameDirs[] = {
		"/dev/block/bootdevice/by-name/",
		"/dev/block/by-name/",
	};
	std::string dir, target_real;
	for (const char* d : kByNameDirs) {
		if (ResolveBlockNode(std::string(d) + part.name + target_suffix, &target_real)) {
			dir = d;
			break;
		}
	}
	if (dir.empty()) {
		HsWhy("no block device for '" + part.name + target_suffix + "'");
		return false;
	}

	// the booted slot's node must be found too. if it can't be, there is
	// no way to prove the target is a different device, so stop.
	std::string booted_real;
	if (!ResolveBlockNode(dir + part.name + booted_suffix, &booted_real)) {
		HsWhy("can't find '" + part.name + booted_suffix + "' to compare against");
		return false;
	}
	if (booted_real == target_real) {
		HsWhy("'" + part.name + "' target is the booted slot's partition");
		return false;
	}
	if (!VerifyFirmwareNode(target_real, part.name + target_suffix)) {
		return false;
	}
	*node = target_real;
	LOGINFO("high-speed: '%s' -> '%s%s%s' (%s)\n", part.name.c_str(), dir.c_str(),
		part.name.c_str(), target_suffix.c_str(), target_real.c_str());
	return true;
}

// otaripper only decodes full-OTA "replace" style operations, so allow-list
// exactly those (by proto value, so this builds against any update_metadata
// version) and reject everything else up front instead of finding out
// partway through extraction:
//   0 REPLACE, 1 REPLACE_BZ, 6 ZERO, 7 DISCARD, 8 REPLACE_XZ, 14 REPLACE_ZSTD
bool OpTypeIsSupported(twrp_highspeed::InstallOperation::Type type) {
	switch (static_cast<int>(type)) {
		case 0:
		case 1:
		case 6:
		case 7:
		case 8:
		case 14:
			return true;
		default:
			return false;
	}
}

// reads payload.bin's header straight out of the zip and parses the
// manifest, so we know which partitions exist and whether anything in
// there is a format we can't handle -- before touching disk at all
bool ProbeHighSpeedPayload(const std::string& package_path, ZipArchiveHandle zip,
                            bool include_firmware,
                            std::vector<HighSpeedPartitionPlan>* plan,
                            HighSpeedGroupSpec* group_spec,
                            std::vector<std::string>* skipped_firmware) {
	plan->clear();
	skipped_firmware->clear();
	g_hs_reason = "unknown reason";
	*group_spec = HighSpeedGroupSpec();

	ZipEntry64 payload_entry;
	if (FindEntry(zip, "payload.bin", &payload_entry) != 0) {
		HsWhy("payload.bin not found in the zip");
		return false;
	}

	// we read payload.bin's bytes straight off disk at its zip offset
	// below, which only lines up correctly if the entry is stored
	// uncompressed inside the zip -- most OTA tooling does this already,
	// but if it isn't, bail rather than read garbage
	if (payload_entry.method != 0) {
		HsWhy("payload.bin is compressed inside the zip");
		return false;
	}

	size_t to_read = std::min<uint64_t>(payload_entry.uncompressed_length, 4 * 1024 * 1024);
	std::vector<uint8_t> buf(to_read);

	android::base::unique_fd fd(open(package_path.c_str(), O_RDONLY | O_CLOEXEC));
	if (fd == -1) {
		HsWhy("can't open the zip");
		return false;
	}

	size_t got = 0;
	while (got < to_read) {
		ssize_t r = pread(fd.get(), buf.data() + got, to_read - got, payload_entry.offset + got);
		if (r < 0) {
			if (errno == EINTR)
				continue;
			HsWhy(std::string("can't read the payload (") + strerror(errno) + ")");
			return false;
		}
		if (r == 0) {
			HsWhy("payload.bin ends early");
			return false;
		}
		got += r;
	}

	size_t off = 0;
	if (to_read < kPayloadMagicSize + kPayloadVersionSize + kPayloadManifestSizeSize ||
	    memcmp(buf.data(), "CrAU", kPayloadMagicSize) != 0) {
		HsWhy("payload.bin has a bad header");
		return false;
	}
	off += kPayloadMagicSize;

	uint64_t version = ReadBigEndian64(buf.data() + off);
	off += kPayloadVersionSize;
	if (version != 2) {
		HsWhy("payload version " + std::to_string(version) + " is not supported");
		return false;
	}

	uint64_t manifest_size = ReadBigEndian64(buf.data() + off);
	off += kPayloadManifestSizeSize;
	if (manifest_size == 0 || manifest_size > 64 * 1024 * 1024 ||
	    payload_entry.uncompressed_length < 24 ||
	    manifest_size > payload_entry.uncompressed_length - 24) {
		HsWhy("invalid or oversized payload manifest");
		return false;
	}

	if (off + kPayloadSignatureSizeSize > to_read) {
		HsWhy("payload header is truncated");
		return false;
	}
	off += kPayloadSignatureSizeSize;

	if (off + manifest_size > to_read) {
		// the manifest is bigger than our first read grabbed -- read again
		// with a buffer sized for the whole thing
		to_read = off + manifest_size;
		buf.assign(to_read, 0);
		got = 0;
		while (got < to_read) {
			ssize_t r = pread(fd.get(), buf.data() + got, to_read - got, payload_entry.offset + got);
			if (r < 0) {
				if (errno == EINTR)
					continue;
				HsWhy(std::string("can't read the payload manifest (") + strerror(errno) + ")");
				return false;
			}
			if (r == 0) {
				HsWhy("payload manifest ends early");
				return false;
			}
			got += r;
		}
	}

	twrp_highspeed::DeltaArchiveManifest manifest;
	if (!manifest.ParseFromArray(buf.data() + off, static_cast<int>(manifest_size))) {
		HsWhy("can't parse the payload manifest");
		return false;
	}

	if (!ValidateHighSpeedManifest(manifest, payload_entry.uncompressed_length,
	        24 + manifest_size + ReadHighSpeedBE32(buf.data() + 20), &g_hs_reason))
		return false;

	if (manifest.minor_version() != 0) {
		// a nonzero minor version means this is a delta payload, which
		// references an old partition we don't have lying around in the
		// shape this path expects -- full payloads only here
		HsWhy("incremental (delta) package, a full OTA is needed");
		return false;
	}

	// the payload itself says which partitions live in Super (any group's
	// partition_names). that's authoritative, so ROM-specific logical
	// partitions (mi_ext, odm_dlkm, ...) don't each need a hard-coded entry
	std::set<std::string> logical_names;
	if (manifest.has_dynamic_partition_metadata()) {
		for (const auto& g : manifest.dynamic_partition_metadata().groups())
			for (const auto& n : g.partition_names())
				logical_names.insert(n);
	}

	for (const auto& part : manifest.partitions()) {
		const std::string& name = part.partition_name();
		if (!IsValidHighSpeedName(name) || IsProtectedPartition(name)) {
			HsWhy("payload writes the protected partition '" + name + "'");
			return false;
		}

		HighSpeedPartitionPlan entry;
		entry.name = name;
		// payload says what's in Super, everything else is physical and
		// goes to <name><target slot>
		entry.is_logical = logical_names.count(name) > 0;
		entry.is_firmware = !entry.is_logical && !IsBootChainPartition(name);
		if (entry.is_firmware && !include_firmware) {
			LOGINFO("high-speed probe: not flashing firmware partition '%s' (firmware option is off)\n",
				name.c_str());
			skipped_firmware->push_back(name);
			continue;
		}

		for (const auto& op : part.operations()) {
			if (!OpTypeIsSupported(op.type())) {
				HsWhy("'" + name + "' uses an operation type that can't be decoded");
				return false;
			}
		}

		entry.target_path = "/" + name;
		entry.expanded_size = part.new_partition_info().size();
		entry.sha256 = part.new_partition_info().hash();
		plan->push_back(std::move(entry));
	}

	if (plan->empty()) {
		HsWhy("nothing to flash in this package");
		return false;
	}

	// which Super group does the payload say the logical partitions live
	// in, and how big is its budget? all of them must be in ONE group --
	// the rebuild handles exactly one, so anything else stops here, before
	// anything on the device is touched
	bool any_logical = false;
	for (const auto& entry : *plan)
		any_logical = any_logical || entry.is_logical;
	if (any_logical) {
		if (!manifest.has_dynamic_partition_metadata()) {
			LOGINFO("high-speed probe: payload has no dynamic partition metadata, keeping the device's current group size\n");
		} else {
			const twrp_highspeed::DynamicPartitionGroup* chosen = nullptr;
			for (const auto& entry : *plan) {
				if (!entry.is_logical)
					continue;
				const twrp_highspeed::DynamicPartitionGroup* owner = nullptr;
				for (const auto& g : manifest.dynamic_partition_metadata().groups()) {
					for (const auto& n : g.partition_names()) {
						if (n != entry.name)
							continue;
						if (owner && owner != &g) {
							HsWhy("'" + entry.name + "' is listed in more than one dynamic group");
							return false;
						}
						owner = &g;
					}
				}
				if (!owner) {
					HsWhy("'" + entry.name + "' isn't in any dynamic group");
					return false;
				}
				if (chosen && chosen != owner) {
					HsWhy("the partitions span more than one dynamic group");
					return false;
				}
				chosen = owner;
			}
			if (chosen) {
				if (!IsValidHighSpeedName(chosen->name()) || chosen->name().size() > 34) {
					HsWhy("invalid dynamic partition group name");
					return false;
				}
				group_spec->name = chosen->name();
				group_spec->size = chosen->size();
				LOGINFO("high-speed probe: payload declares group '%s' with size %llu\n",
					group_spec->name.c_str(), (unsigned long long)group_spec->size);
			}
		}
	}

	return true;
}

}  // namespace


namespace {
bool ValidateHighSpeedDevice(ZipArchiveHandle zip) {
	ZipEntry64 entry;
	if (FindEntry(zip, "META-INF/com/android/metadata", &entry) != 0 ||
	    entry.uncompressed_length == 0 || entry.uncompressed_length > 1024 * 1024) {
		HsWhy("missing or invalid OTA device metadata");
		return false;
	}
	std::string text(entry.uncompressed_length, '\0');
	if (ExtractToMemory(zip, &entry, reinterpret_cast<uint8_t*>(&text[0]), text.size()) != 0) {
		HsWhy("cannot read OTA device metadata");
		return false;
	}
	std::map<std::string, std::string> metadata;
	for (const auto& line : android::base::Split(text, "\n")) {
		const auto pos = line.find('=');
		if (pos != std::string::npos)
			metadata[line.substr(0, pos)] = android::base::Trim(line.substr(pos + 1));
	}
	std::set<std::string> accepted;
	accepted.insert(android::base::GetProperty("ro.product.device", ""));
	for (const auto& name : android::base::Split(
	        android::base::GetProperty("ro.twrp.target.devices", ""), ",|"))
		if (!name.empty()) accepted.insert(name);
	for (const auto& name : android::base::Split(metadata["pre-device"], ",|")) {
		if (!name.empty() && accepted.count(name) && metadata["ota-type"] == "AB")
			return true;
	}
	HsWhy("OTA is not an A/B package for this device");
	return false;
}
} // namespace

HighSpeedResult TryHighSpeedAbInstall(const std::string& package, ZipArchiveHandle zip) {
	if (!DataManager::GetIntValue("tw_high_speed_flash"))
		return HighSpeedResult::kNotApplicable;

	ZipEntry64 unused;
	if (FindEntry(zip, "payload_properties.txt", &unused) != 0)
		return HighSpeedResult::kNotApplicable;

	// from here on the toggle is on and this really is an A/B payload zip,
	// so every way out below is kAborted -- we never quietly drop back to
	// the normal path once we've gotten this far

	if (access(kHighSpeedExtractorPath, X_OK) != 0) {
		HsFail("extractor missing (/system/bin/otaripper)");
		return HighSpeedResult::kAborted;
	}

	HsSay(Msg("high_speed_title=High speed flash"));
	HsSay(Msg("high_speed_reading=Reading payload..."));
	std::vector<HighSpeedPartitionPlan> plan;
	HighSpeedGroupSpec group_spec;
	std::vector<std::string> skipped_firmware;
	const bool include_firmware = DataManager::GetIntValue("tw_high_speed_firmware") != 0;
	if (!ProbeHighSpeedPayload(package, zip, include_firmware, &plan, &group_spec, &skipped_firmware)) {
		HsFail("package not supported: " + g_hs_reason);
		return HighSpeedResult::kAborted;
	}

	{
		uint64_t total = 0;
		size_t firmware_count = 0;
		for (const auto& p : plan) {
			total += p.expanded_size;
			if (p.is_firmware)
				firmware_count++;
		}
		HsLog("  Payload: " + std::to_string(plan.size()) + " images, " + HsSize(total));
		if (firmware_count)
			HsLog("  Firmware: " + std::to_string(firmware_count) + " images included, verified from storage");
		else if (!skipped_firmware.empty())
			HsLog("  Firmware: not flashed (" + std::to_string(skipped_firmware.size()) + " skipped)");
	}

	// ---- which slot are we allowed to write? -------------------------
	// the slot recovery booted from is never written. if we can't tell
	// which one that is, stop before touching anything.
	const std::string booted_slot = DetermineBootedSlot();
	if (booted_slot.empty()) {
		HsFail("can't tell which slot is booted");
		return HighSpeedResult::kAborted;
	}
	const std::string target_slot = (booted_slot == "A") ? "B" : "A";
	const std::string booted_suffix = (booted_slot == "A") ? "_a" : "_b";
	const std::string target_suffix = (target_slot == "A") ? "_a" : "_b";
	LOGINFO("high-speed: booted slot %s, writing slot %s\n", booted_slot.c_str(), target_slot.c_str());
	HsLog("  Target: slot " + target_slot + " (booted from " + booted_slot + ")");

	// no partition may appear twice in the plan
	{
		std::set<std::string> seen_names;
		for (auto& part : plan) {
			if (!seen_names.insert(part.name).second) {
				HsFail("'" + part.name + "' appears twice in the payload");
				return HighSpeedResult::kAborted;
			}
		}
	}

	// ---- pre-flight, BEFORE anything destructive ---------------------
	// resolve and validate every physical target (exists, is a block
	// device, isn't the booted slot's node, big enough for the image).
	// nothing has been modified at this point, so any failure here is free.
	std::map<std::string, std::string> nodes;  // partition name -> real block node
	std::set<std::string> seen_nodes;
	for (auto& part : plan) {
		if (part.is_logical)
			continue;
		std::string node;
		if (!ResolvePhysicalTarget(part, booted_suffix, target_suffix, &node)) {
			HsFail(g_hs_reason);
			return HighSpeedResult::kAborted;
		}
		uint64_t node_size = 0;
		if (!GetBlockDeviceSize(node, &node_size)) {
			HsFail("can't read the size of the '" + part.name + "' target");
			return HighSpeedResult::kAborted;
		}
		if (node_size < part.expanded_size) {
			HsFail("'" + part.name + "' is " + HsSize(part.expanded_size) + ", its slot " + target_slot + " partition only " + HsSize(node_size));
			return HighSpeedResult::kAborted;
		}
		if (!seen_nodes.insert(node).second) {
			HsFail("two images map to the same device ('" + part.name + "')");
			return HighSpeedResult::kAborted;
		}
		nodes[part.name] = node;
	}

	const bool reflash_twrp = DataManager::GetIntValue(TW_AUTO_REFLASHTWRP_VAR) != 0;
	if (reflash_twrp && !nodes.count("boot")) {
		HsFail("ramdisk preservation requires a boot image in the payload");
		return HighSpeedResult::kAborted;
	}
	if (!ValidateHighSpeedDevice(zip)) {
		HsFail(g_hs_reason);
		return HighSpeedResult::kAborted;
	}
	if (!PartitionManager.Mount_By_Path("/metadata", false)) {
		HsFail("cannot mount /metadata to check snapshot state");
		return HighSpeedResult::kAborted;
	}

	// biggest partitions first. the extractor works through them in this
	// order, and the biggest one decides how long the whole extraction
	// takes, so it shouldn't sit queued behind small ones. the -p list and
	// the descriptor list below are both built from this one ordering --
	// the extractor pairs them up by position.
	std::vector<const HighSpeedPartitionPlan*> by_size;
	for (auto& part : plan)
		by_size.push_back(&part);
	std::stable_sort(by_size.begin(), by_size.end(),
		[](const HighSpeedPartitionPlan* a, const HighSpeedPartitionPlan* b) {
			return a->expanded_size > b->expanded_size;
		});
	std::string joined_names;
	for (size_t i = 0; i < by_size.size(); i++) {
		if (i > 0)
			joined_names += ",";
		joined_names += by_size[i]->name;
	}


	// ---- first destructive step: lay out the target slot's Super group
	// in ONE pass, at final sizes, so the dm nodes exist at the right size
	// before the extractor claims them. Only TARGET metadata is committed,
	// but source Super extents may be reused if both ROMs cannot fit.
	std::map<std::string, std::string> mapped_paths;
	struct MappingCleanup {
		std::map<std::string, std::string>& paths;
		const std::string& suffix;
		~MappingCleanup() { PartitionManager.Unmap_High_Speed_Targets(suffix, paths); }
	} cleanup{mapped_paths, target_suffix};
	{
		std::vector<std::pair<std::string, uint64_t>> logical_sizes;
		for (auto& part : plan) {
			if (part.is_logical)
				logical_sizes.push_back({part.name, part.expanded_size});
		}
		if (!logical_sizes.empty())
			HsLog("  Super layout for slot " + target_slot + "...");
		if (!PartitionManager.Rebuild_Logical_Group_For_High_Speed_Flash(target_suffix, logical_sizes,
			group_spec.name, group_spec.size, &mapped_paths)) {
			return HighSpeedResult::kAborted;
		}
	}

	if (!PartitionManager.Set_High_Speed_Boot_Slot(target_suffix, false)) {
		HsFail("cannot mark target slot unbootable before writing");
		return HighSpeedResult::kAborted;
	}

	DataManager::SetValue("tw_high_speed_reboot_required", 1);

	// validate every logical node the rebuild just mapped
	for (auto& part : plan) {
		if (!part.is_logical)
			continue;
		auto it = mapped_paths.find(part.name);
		if (it == mapped_paths.end()) {
			HsFail("Super layout gave no device for '" + part.name + "'");
			return HighSpeedResult::kAborted;
		}
		std::string node;
		if (!ResolveBlockNode(it->second, &node)) {
			HsFail("Super device for '" + part.name + "' is not a block device");
			return HighSpeedResult::kAborted;
		}
		uint64_t node_size = 0;
		if (!GetBlockDeviceSize(node, &node_size) || node_size < part.expanded_size) {
			HsFail("Super device for '" + part.name + "' is " + HsSize(node_size) + ", the image is " + HsSize(part.expanded_size));
			return HighSpeedResult::kAborted;
		}
		if (!seen_nodes.insert(node).second) {
			HsFail("two images map to the same Super device ('" + part.name + "')");
			return HighSpeedResult::kAborted;
		}
		nodes[part.name] = node;
	}

	// claim every target exclusively BEFORE the extractor starts. O_EXCL on
	// a block device fails with EBUSY while it is mounted or held open by
	// someone else, so the extractor can never write underneath a live
	// filesystem. every node was verified above as an existing block device,
	// so this can never fall into creating a regular file under /dev/block.
	// the descriptors are inherited by the extractor as-is.
	std::vector<android::base::unique_fd> target_fds;
	for (const auto* part : by_size) {
		android::base::unique_fd fd(open(nodes[part->name].c_str(), O_RDWR | O_EXCL | O_CLOEXEC));
		if (fd == -1) {
			HsFail("'" + part->name + "' is busy, no exclusive access (" + strerror(errno) + ")");
			return HighSpeedResult::kAborted;
		}
		target_fds.push_back(std::move(fd));
	}

	HsSay(Msg("high_speed_writing=Writing {1} images...")(plan.size()));

	time_t extract_start, extract_stop;
	time(&extract_start);

	// the extractor prints one "<partition>:<percent>" line per percent. a
	// partition only reports 100 after it was fully written, checksummed and
	// flushed. worker count is chosen by the extractor from CPUs and free RAM.
	std::vector<std::string> extractor_args = { kHighSpeedExtractorPath, "--strict", "--no-open" };
	for (const auto& fd : target_fds) {
		extractor_args.push_back("--direct-fd");
		extractor_args.push_back(std::to_string(fd.get()));
	}
	// optional: after the writes, drop the device cache and verify what the
	// storage really holds instead of what the page cache holds (slower)
	if (DataManager::GetIntValue("tw_high_speed_readback"))
		extractor_args.push_back("--readback");
	// firmware is always re-read and SHA-256 checked before the slot switch
	{
		std::string firmware_list;
		for (const auto* part : by_size)
			if (part->is_firmware)
				firmware_list += (firmware_list.empty() ? "" : ",") + part->name;
		if (!firmware_list.empty()) {
			extractor_args.push_back("--readback-for");
			extractor_args.push_back(firmware_list);
		}
	}
	extractor_args.push_back("-p");
	extractor_args.push_back(joined_names);
	extractor_args.push_back(package);
	std::vector<char*> extractor_argv;
	for (auto& arg : extractor_args)
		extractor_argv.push_back(const_cast<char*>(arg.c_str()));
	extractor_argv.push_back(nullptr);

	// the extractor's stdout and stderr are merged into a pipe we read progress
	// and error lines from.
	int out_pipe[2];
	if (pipe2(out_pipe, O_CLOEXEC) != 0) {
		HsFail(std::string("can't start the extractor (") + strerror(errno) + ")");
		return HighSpeedResult::kAborted;
	}

	int status = 0;
	pid_t pid = fork();
	if (pid == 0) {
		if (dup2(out_pipe[1], STDOUT_FILENO) < 0 ||
		    dup2(out_pipe[1], STDERR_FILENO) < 0) _exit(126);
		close(out_pipe[0]);
		close(out_pipe[1]);
		// the claimed targets were opened O_CLOEXEC; let them survive the exec
		for (const auto& fd : target_fds)
			if (fcntl(fd.get(), F_SETFD, 0) < 0) _exit(126);
		execv(extractor_argv[0], extractor_argv.data());
		_exit(127);
	} else if (pid < 0) {
		close(out_pipe[0]);
		close(out_pipe[1]);
		HsFail(std::string("can't start the extractor (") + strerror(errno) + ")");
		return HighSpeedResult::kAborted;
	}
	close(out_pipe[1]);

	// overall progress = each partition's percent weighted by its size.
	// never shown as 100: completion is announced by the "written and
	// flushed" line once the extractor has exited cleanly

	std::map<std::string, uint64_t> part_size;
	std::map<std::string, int> part_pct;
	std::string last_error;
	uint64_t total_bytes = 0;
	for (auto& part : plan) {
		part_size[part.name] = part.expanded_size;
		part_pct[part.name] = 0;
		total_bytes += part.expanded_size;
	}

	int last_shown = -1;
	std::string pending;
		char chunk[512];
		for (;;) {
			ssize_t r = read(out_pipe[0], chunk, sizeof(chunk));
			if (r < 0) {
				if (errno == EINTR)
					continue;
				break;
			}
			if (r == 0)
				break;  // extractor closed stdout (it exited)
			pending.append(chunk, r);
			size_t nl;
			while ((nl = pending.find('\n')) != std::string::npos) {
				std::string line = pending.substr(0, nl);
				pending.erase(0, nl + 1);

				// Strip trailing \r for cleaner logging and matching
				if (!line.empty() && line.back() == '\r') {
					line.pop_back();
				}

				// "<partition>:<percent>" lines drive the progress bar. anything else
				// the extractor prints (worker count, throughput summary, and on a
				// failure its "ERROR: ..." line) is written to the recovery log.
				// Whether the flash worked is decided by the exit status and the
				// completion check below, never by what the text says.
				bool is_progress = false;
				size_t colon = line.rfind(':');
				if (colon != std::string::npos && total_bytes != 0) {
					auto it = part_pct.find(line.substr(0, colon));
					const char* pct_str = line.c_str() + colon + 1;
					while (*pct_str == ' ') pct_str++;
					if (it != part_pct.end() && isdigit((unsigned char)*pct_str)) {
						is_progress = true;
						it->second = std::max(0, std::min(100, atoi(pct_str)));
						uint64_t weighted = 0;
						for (auto& kv : part_pct)
							weighted += (uint64_t)kv.second * part_size[kv.first];
						int overall = std::min<int>(99, (int)(weighted / total_bytes));
						if (overall != last_shown) {
							last_shown = overall;
							// the GUI console is append-only and can't rewrite a line it
							// already printed, so the live percentage goes to the progress
							// bar instead (same mechanism the normal path's "set_progress"
							// uses) -- one element updating in place, no line spam
							DataManager::SetProgress(((float)overall) / 100.0f);
						}
					}
				}
				if (!is_progress && !line.empty()) {
					if (line.rfind("ERROR", 0) == 0)
						last_error = line;
					LOGINFO("high-speed: extractor: %s\n", line.c_str());
				}
			}
			if (pending.size() > 4096)
				pending.clear();  // never let a runaway line grow forever
		}
	close(out_pipe[0]);

	pid_t waited;
	do {
		waited = waitpid(pid, &status, 0);
	} while (waited < 0 && errno == EINTR);

	// --- Check 1: exit status and signals (the authoritative result) ---
	if (WIFSIGNALED(status)) {
		int sig = WTERMSIG(status);
		HsFail(std::string("extractor crashed (") + strsignal(sig) + ")");
		return HighSpeedResult::kAborted;
	}

	if (waited != pid || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
		HsFail(last_error.empty() ? std::string("extractor exited with an error") : HsTrim(last_error));
		return HighSpeedResult::kAborted;
	}

	// --- Check 2: completion. the extractor only reports 100 for a partition
	// after it was written, checksummed and flushed, so a clean exit with any
	// partition short of 100 means something went wrong that the exit status
	// didn't show. this is the last gate before the slot gets switched.
	for (auto& kv : part_pct) {
		if (kv.second < 100) {
			HsFail("'" + kv.first + "' stopped at " + std::to_string(kv.second) + "%");
			return HighSpeedResult::kAborted;
		}
	}

	DataManager::SetProgress(1.0f);

	// the extractor already fsync'd every partition it finished; flush
	// each claimed target once more from here, then a global sync, and only
	// call it success if every flush went through. the claims are released
	// right after, before anything else touches these partitions.
	HsLog("  Flushing to storage...");
	for (size_t i = 0; i < target_fds.size(); i++) {
		if (fsync(target_fds[i].get()) != 0) {
			HsFail("can't flush '" + by_size[i]->name + "' to storage (" + strerror(errno) + ")");
			return HighSpeedResult::kAborted;
		}
	}
	// firmware: one more read-back check while the claims are still held
	{
		size_t verified_count = 0;
		for (size_t i = 0; i < target_fds.size(); i++) {
			if (!by_size[i]->is_firmware)
				continue;
			if (!VerifyDeviceSha256(target_fds[i].get(), by_size[i]->expanded_size, by_size[i]->sha256)) {
				HsFail("firmware '" + by_size[i]->name + "' doesn't match its SHA-256 on storage");
				return HighSpeedResult::kAborted;
			}
			verified_count++;
		}
		if (verified_count)
			HsLog("  Firmware verified: " + std::to_string(verified_count) + " images");
	}
	target_fds.clear();
	sync();

	time(&extract_stop);
	int extract_secs = (int) difftime(extract_stop, extract_start);
	HsSay(Msg("high_speed_written=Images written in {1}s")(extract_secs));

	// update_engine never ran, so nothing told the bootloader to switch
	// slots -- that's the one piece of its job we still have to do
	// ourselves, and only now that every partition has actually succeeded
	if (!PartitionManager.Unmap_High_Speed_Targets(target_suffix, mapped_paths)) {
		HsFail("cannot release target Super mappings; reboot recovery before retrying");
		return HighSpeedResult::kAborted;
	}
	mapped_paths.clear();
	if (reflash_twrp) {
		HsSay(Msg("high_speed_restore_twrp=Restoring TWRP ramdisk to the target boot image..."));
		if (!PartitionManager.Reflash_Current_Twrp_For_High_Speed(target_suffix, nodes.at("boot"))) {
			HsFail("target ramdisk repack failed; target slot remains unbootable");
			return HighSpeedResult::kAborted;
		}
		android::base::unique_fd boot_fd(open(nodes.at("boot").c_str(), O_RDWR | O_EXCL | O_CLOEXEC));
		if (boot_fd == -1 || fsync(boot_fd.get()) != 0) {
			HsFail("cannot flush the repacked target boot image");
			return HighSpeedResult::kAborted;
		}
	}
	if (!PartitionManager.Set_High_Speed_Boot_Slot(target_suffix, true)) {
		HsFail("images written, but bootloader slot activation failed");
		return HighSpeedResult::kAborted;
	}

	HsLog("  Active slot is now " + target_slot);
	return HighSpeedResult::kSucceeded;
}
