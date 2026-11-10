#pragma once
#include <string>
#include <ziparchive/zip_archive.h>
enum class HighSpeedResult { kNotApplicable, kAborted, kSucceeded };
HighSpeedResult TryHighSpeedAbInstall(const std::string& package, ZipArchiveHandle zip);
