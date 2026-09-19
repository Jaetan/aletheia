// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// One owning temporary path for the test tree.  Three suites needed a scratch
// file, a scratch file with content, and a scratch directory, and each carried
// its own type with its own lifetime to get right; one removed its file
// through the throwing overloads, from inside a destructor.  This one removes
// whatever is at the path, file or directory, and cannot throw doing it.
//
// Non-copyable and non-movable, so the path's life is exactly the scope that
// declared it.  `path` is public and const, which is what the call sites read.
//
// A name is placed under a directory this process owns, not under the system
// temp directory itself: the mutation lane runs the whole suite in several
// processes at once, and two of them writing and removing one fixed name
// failed each other's file-size-cap cases.

#include <algorithm>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <optional>
#include <ranges>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <thread>
#include <utility>

#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

namespace aletheia::test {

/// The name every scratch directory of this test tree starts with, spelled
/// once for the process that makes one and the sweep that clears the rest.
inline constexpr std::string_view scratch_prefix = "aletheia-cpp-tests-";

/// An attempt on a scratch directory's exclusive lock, held for this object's
/// scope.  The lock is what tells a directory whose owner is still running
/// from one whose owner is gone: the kernel drops a `flock` however its holder
/// ends, a signal included, whereas a process id is reused and a timestamp is
/// not a freshness signal.  Two descriptors on one directory conflict even
/// inside a single process, so a process's own scratch directory is as safe
/// from its own sweep as from anyone else's.
class ScratchLock {
public:
    /// Opens `dir` and tries its lock; `owns` reports the outcome.  A read
    /// mode stream is what opens a directory without a variadic call, and the
    /// descriptor behind it is all this uses.
    explicit ScratchLock(const std::filesystem::path& dir)
        : file_(std::fopen(dir.c_str(), "re"))
        , held_(file_ != nullptr && ::flock(::fileno(file_), LOCK_EX | LOCK_NB) == 0) {}

    ~ScratchLock() {
        if (file_ != nullptr)
            (void)std::fclose(file_);
    }

    ScratchLock(const ScratchLock&) = delete;
    ScratchLock(ScratchLock&&) = delete;
    auto operator=(const ScratchLock&) -> ScratchLock& = delete;
    auto operator=(ScratchLock&&) -> ScratchLock& = delete;

    /// True when the lock was taken and `dir` still names the directory it was
    /// taken on.  A sweep that removed the directory between this object's
    /// open and its lock leaves the lock held on an inode no path reaches, and
    /// every file the owner would write into it fails.
    [[nodiscard]] auto owns(const std::filesystem::path& dir) const -> bool {
        struct ::stat locked = {};
        struct ::stat named = {};
        return held_ && ::fstat(::fileno(file_), &locked) == 0 &&
               ::stat(dir.c_str(), &named) == 0 && locked.st_dev == named.st_dev &&
               locked.st_ino == named.st_ino;
    }

private:
    std::FILE* file_;
    bool held_;
};

/// Removes every scratch directory under the system temp directory whose
/// owning process is gone, which is every one whose lock can be taken.  A run
/// a signal ends never reaches static destruction and keeps its directory,
/// which about one run in eight of a mutation sweep does, so without this
/// the temp filesystem fills and a later run fails on whatever
/// writes next rather than on the cause.  Nothing here throws or reports: a
/// directory this cannot open is one it leaves alone.
inline void reap_dead_scratch_dirs() {
    std::error_code ec;
    auto const root = std::filesystem::temp_directory_path(ec);
    if (ec)
        return;
    for (std::filesystem::directory_iterator it{root, ec}, end; !ec && it != end;
         it.increment(ec)) {
        auto const& dir = it->path();
        if (!dir.filename().string().starts_with(scratch_prefix))
            continue;
        std::error_code entry;
        // The symlink status, not the resolved one: the system temp directory
        // is world writable, and a link planted under this name would
        // otherwise be read as the directory it points at.
        if (!std::filesystem::is_directory(std::filesystem::symlink_status(dir, entry)))
            continue;
        const ScratchLock lock{dir};
        if (!lock.owns(dir))
            continue;
        std::filesystem::remove_all(dir, entry);
    }
}

/// The scratch directory of this process, created on first use and removed
/// when the process ends, or by the next run when this one is killed before it
/// can.  A sweep that runs the suite once per mutant would otherwise leave one
/// directory per killed run behind.
[[nodiscard]] inline auto scratch_dir() -> const std::filesystem::path& {
    struct Owned {
        std::filesystem::path dir = std::filesystem::temp_directory_path() /
                                    (std::string(scratch_prefix) + std::to_string(::getpid()));
        std::optional<ScratchLock> lock;

        Owned() {
            // The dead directories go first, before anything is created: what
            // this repairs is a temp filesystem with no space left, where
            // creating one more is the operation that fails.  A directory this
            // process id left behind is among them, nothing holding its lock.
            reap_dead_scratch_dirs();
            // A peer sweeping the dead directories can take this one between
            // its creation and its lock, in which case the lock names an inode
            // no path reaches and the attempt starts over.  The peer holds its
            // lock only for the removal, so yielding to it is what the tries
            // are for, and the first that holds is the last.
            constexpr int tries = 64;
            if (std::ranges::any_of(std::views::repeat(0, tries), [this](auto) { return take(); }))
                return;
            throw std::runtime_error("cannot hold " + dir.string());
        }

        /// One try at owning `dir`: creates it and takes its lock, answering
        /// whether the lock it took is the directory still at that path.
        auto take() -> bool {
            std::error_code ec;
            std::filesystem::create_directories(dir, ec);
            if (ec)
                throw std::runtime_error("cannot create " + dir.string() + ": " + ec.message());
            lock.emplace(dir);
            if (lock->owns(dir))
                return true;
            lock.reset();
            std::this_thread::yield();
            return false;
        }

        ~Owned() {
            std::error_code ec;
            // Removed under the lock, so no peer sweep can be inside this
            // directory while it goes.
            std::filesystem::remove_all(dir, ec);
            lock.reset();
        }

        Owned(const Owned&) = delete;
        Owned(Owned&&) = delete;
        auto operator=(const Owned&) -> Owned& = delete;
        auto operator=(Owned&&) -> Owned& = delete;
    };
    static const Owned owned;
    return owned.dir;
}

// Tag for the directory shape, so the three constructors differ by more than
// their argument count at the call site.
struct AsDirectory {};

class TempPath {
public:
    // A name under this process's scratch directory, with anything already
    // there removed.
    explicit TempPath(std::string_view name) : path(scratch_dir() / name) { clear(); }

    // The same, with `content` written to it.
    TempPath(std::string_view name, std::string_view content) : TempPath(name) {
        std::ofstream out{path};
        out << content;
        out.close();
        if (!out)
            throw std::runtime_error("cannot write " + path.string());
    }

    // A directory at an explicit path, created now.
    TempPath(std::filesystem::path where, AsDirectory /*unused*/) : path(std::move(where)) {
        std::filesystem::create_directories(path);
    }

    TempPath(const TempPath&) = delete;
    TempPath(TempPath&&) = delete;
    auto operator=(const TempPath&) -> TempPath& = delete;
    auto operator=(TempPath&&) -> TempPath& = delete;
    ~TempPath() { clear(); }

    [[nodiscard]] auto string() const -> std::string { return path.string(); }

    const std::filesystem::path path;

private:
    void clear() const {
        std::error_code ec;
        std::filesystem::remove_all(path, ec);
    }
};

} // namespace aletheia::test
