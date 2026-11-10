// SPDX-License-Identifier: GPL-3.0-or-later
#pragma once
#include <algorithm>
#include <cstdint>
#include <limits>
#include <string>
#include <set>
#include <utility>
#include <vector>

inline uint32_t ReadHighSpeedBE32(const uint8_t* p) {
    return (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16) |
           (uint32_t(p[2]) << 8) | uint32_t(p[3]);
}

// Template keeps the preflight arithmetic independently testable, without
// Android or protobuf libraries. Manifest is DeltaArchiveManifest in recovery.
template <typename Manifest>
bool ValidateHighSpeedManifest(const Manifest& manifest, uint64_t payload_size,
                              uint64_t data_start, std::string* reason) {
    auto fail = [&](const char* text) { *reason = text; return false; };
    if (data_start > payload_size)
        return fail("payload metadata/signature exceeds payload size");
    if (manifest.partial_update())
        return fail("partial OTA: use the standard installer");
    if (manifest.minor_version() != 0)
        return fail("incremental payload: use the standard installer");
    const uint64_t block_size = manifest.block_size();
    if (block_size != 4096 || manifest.partitions_size() == 0 || manifest.partitions_size() > 256)
        return fail("unsupported block size or empty payload");
    std::set<std::string> names;
    for (const auto& part : manifest.partitions()) {
        if (!names.insert(part.partition_name()).second)
            return fail("duplicate payload partition");
        if (part.has_old_partition_info() ||
            (part.run_postinstall() && !part.postinstall_optional()) ||
            part.hash_tree_extent().num_blocks() || part.fec_extent().num_blocks())
            return fail("payload requires source data, mandatory postinstall, verity or FEC generation");
        const uint64_t size = part.new_partition_info().size();
        if (!size || size % block_size || size > (1ULL << 40) ||
            part.new_partition_info().hash().size() != 32 || part.operations_size() == 0)
            return fail("partition has invalid size, missing SHA-256 or no operations");
        const uint64_t blocks = size / block_size;
        std::vector<std::pair<uint64_t, uint64_t>> ranges;
        for (const auto& op : part.operations()) {
            const int type = static_cast<int>(op.type());
            const bool zero = type == 6 || type == 7;
            if (!(type == 0 || type == 1 || zero || type == 8 || type == 14))
                return fail("unsupported or incremental payload operation");
            if (op.src_extents_size() || !op.src_sha256_hash().empty() || op.dst_extents_size() == 0)
                return fail("source-dependent operation or missing destination");
            if (zero && op.data_length() != 0)
                return fail("zero operation carries data");
            if (!zero && (op.data_length() == 0 || op.data_sha256_hash().size() != 32))
                return fail("missing operation data or SHA-256");
            if (op.data_offset() > payload_size - data_start ||
                op.data_length() > payload_size - data_start - op.data_offset())
                return fail("operation data exceeds payload size");
            uint64_t op_blocks = 0;
            for (const auto& extent : op.dst_extents()) {
                const uint64_t first = extent.start_block(), count = extent.num_blocks();
                if (!count || first >= blocks || count > blocks - first)
                    return fail("operation extent exceeds partition size");
                ranges.emplace_back(first, first + count);
                op_blocks += count;
                if (op_blocks > blocks)
                    return fail("operation extents exceed partition size");
            }
            if (type == 0 && (op.data_length() > op_blocks * block_size ||
                (op.data_length() - 1) / block_size + 1 != op_blocks))
                return fail("raw operation size does not match destination extents");
        }
        std::sort(ranges.begin(), ranges.end());
        uint64_t next = 0;
        for (const auto& range : ranges) {
            if (range.first != next)
                return fail("partition operations overlap or leave a gap");
            next = range.second;
        }
        if (next != blocks)
            return fail("partition operations do not cover the whole image");
    }
    std::set<std::string> logical_names;
    for (const auto& group : manifest.dynamic_partition_metadata().groups()) {
        for (const auto& name : group.partition_names()) {
            if (!names.count(name) || !logical_names.insert(name).second)
                return fail("dynamic group references a missing or repeated partition");
        }
    }
    return true;
}
