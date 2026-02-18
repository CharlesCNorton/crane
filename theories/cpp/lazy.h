// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#pragma once
#include <functional>
#include <optional>

namespace crane {

template<typename T>
class lazy {
    std::function<T()> thunk_;
    mutable std::optional<T> cache_;
public:
    explicit lazy(T value) : cache_(std::move(value)) {}

    explicit lazy(std::function<T()> thunk) : thunk_(std::move(thunk)) {}

    const T& force() const {
        if (!cache_) cache_ = thunk_();
        return *cache_;
    }
};

} // namespace crane
