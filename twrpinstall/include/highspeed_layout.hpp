// SPDX-License-Identifier: GPL-3.0-or-later
#pragma once
#include <algorithm>
#include <cstdint>
#include <set>
#include <string>
#include <utility>
#include <vector>

inline bool HighSpeedHasSlotSuffix(const std::string& name, const std::string& suffix) {
    return name.size() > suffix.size() &&
           name.compare(name.size() - suffix.size(), suffix.size(), suffix) == 0;
}

// This only edits an in-memory liblp builder. No mappings, boot flags or on-disk
// metadata are changed until the caller has validated the resulting layout.
// Prefer keeping the source. If it does not fit, use the full-OTA recovery
// fallback from update_engine::DeleteSourcePartitions: release source groups.
template <typename Builder>
bool PrepareHighSpeedLayout(Builder* builder,
        const std::string& source_suffix, const std::string& target_suffix,
        const std::string& group_name, uint64_t group_size,
        const std::vector<std::pair<std::string, uint64_t>>& partitions,
        std::vector<std::string>* old_targets, std::vector<std::string>* old_sources,
        bool* reclaimed_source, std::string* reason) {
    old_targets->clear();
    old_sources->clear();
    *reclaimed_source = false;
    auto fail = [&](const char* message) { *reason = message; return false; };
    if (!builder || (source_suffix != "_a" && source_suffix != "_b") ||
        (target_suffix != "_a" && target_suffix != "_b") || source_suffix == target_suffix ||
        !HighSpeedHasSlotSuffix(group_name, target_suffix) || !group_size || partitions.empty())
        return fail("invalid full-OTA Super layout request");
    uint64_t total = 0;
    std::set<std::string> names;
    for (const auto& entry : partitions) {
        if (entry.first.empty() || !entry.second || !names.insert(entry.first).second ||
            entry.second > group_size - total)
            return fail("ROM exceeds its Super group size or has invalid partitions");
        total += entry.second;
    }
    auto remove_groups = [&](const std::string& suffix, std::vector<std::string>* removed) {
        // ListGroups returns a copy, so removing a group cannot invalidate this loop.
        for (const auto& name : builder->ListGroups()) {
            if (!HighSpeedHasSlotSuffix(name, suffix)) continue;
            for (const auto* part : builder->ListPartitionsInGroup(name))
                removed->push_back(part->name());
            builder->RemoveGroupAndPartitions(name);
        }
    };
    remove_groups(target_suffix, old_targets);
    auto allocate = [&]() {
        if (!builder->AddGroup(group_name, group_size)) return false;
        for (const auto& entry : partitions) {
            auto* part = builder->AddPartition(entry.first + target_suffix, group_name, 0);
            if (!part || !builder->ResizePartition(part, entry.second)) return false;
        }
        return true;
    };
    if (allocate()) return true;
    // Discard the failed partial allocation before reusing any source extents.
    builder->RemoveGroupAndPartitions(group_name);
    remove_groups(source_suffix, old_sources);
    if (old_sources->empty() || !allocate())
        return fail("ROM does not fit in Super even after releasing the source slot");
    *reclaimed_source = true;
    return true;
}

// Mounts contains each mount point plus whether it is backed by a device being
// released. Also unmount descendants (bind mounts, firmware mounts) first.
inline bool HighSpeedUnmountPlan(const std::vector<std::pair<std::string, bool>>& mounts,
                                std::vector<std::string>* paths) {
    paths->clear();
    for (const auto& source : mounts) {
        if (source.second && (source.first.empty() || source.first[0] != '/' ||
            source.first == "/" || source.first == "/data" || source.first == "/metadata"))
            return false;
    }
    for (const auto& mount : mounts) {
        for (const auto& source : mounts) {
            if (source.second && (mount.first == source.first ||
                mount.first.compare(0, source.first.size() + 1, source.first + "/") == 0)) {
                paths->push_back(mount.first);
                break;
            }
        }
    }
    std::stable_sort(paths->begin(), paths->end(), [](const auto& a, const auto& b) {
        return a.size() > b.size();
    });
    return true;
}
