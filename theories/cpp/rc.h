// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// rc.h — single-allocation, Rust-like rc<T>/weak<T> for C++ (single-threaded)
// GENERATED USING GPT-5
// - **Single allocation**: control block and T live in one heap block
// - Non-atomic counts (like Rust's rc). Not thread-safe.
// - weak<T> supported to break cycles. No enable_shared_from_this, by design.
// - Intentionally minimal; extend with custom allocators/deleters as needed.

#pragma once
#include <cstddef>
#include <utility>
#include <type_traits>
#include <new>
#include <cassert>

namespace crane {

// Forward declarations
template <typename T> class rc;
template <typename T> class weak;

template <typename T>
struct ControlBlock {
    std::size_t strong{1}; // number of owning rc
    std::size_t weak{0};   // number of weak

    // Raw storage for T. We construct/destroy T manually via placement new.
    alignas(T) unsigned char storage[sizeof(T)];

    T*       ptr()       noexcept { return reinterpret_cast<T*>(&storage[0]); }
    const T* ptr() const noexcept { return reinterpret_cast<const T*>(&storage[0]); }
};

// Factory

template <typename T, typename... Args>
rc<T> make_rc(Args&&... args);

// rc<T> — owning reference-counted pointer (like Rust Rc<T>)

template <typename T>
class rc {
public:
    using element_type = T;

    rc() noexcept = default; // null rc

    rc(const rc& other) noexcept : ctrl_(other.ctrl_) { inc_strong(); }
    rc(rc&& other) noexcept : ctrl_(other.ctrl_) { other.ctrl_ = nullptr; }

    // Construct from weak if still alive
    explicit rc(const weak<T>& weak) noexcept : ctrl_(weak.ctrl_) {
        if (!ctrl_ || ctrl_->strong == 0) { ctrl_ = nullptr; return; }
        inc_strong();
    }

    rc& operator=(const rc& other) noexcept {
        if (this != &other) { release(); ctrl_ = other.ctrl_; inc_strong(); }
        return *this;
    }

    rc& operator=(rc&& other) noexcept {
        if (this != &other) { release(); ctrl_ = other.ctrl_; other.ctrl_ = nullptr; }
        return *this;
    }

    ~rc() { release(); }

    T* get() const noexcept { return ctrl_ ? ctrl_->ptr() : nullptr; }
    T& operator*() const noexcept { assert(get()); return *get(); }
    T* operator->() const noexcept { return get(); }
    explicit operator bool() const noexcept { return get() != nullptr; }

    std::size_t use_count() const noexcept { return ctrl_ ? ctrl_->strong : 0; }

    void reset() noexcept { release(); }

    void swap(rc& other) noexcept { std::swap(ctrl_, other.ctrl_); }

    weak<T> downgrade() const noexcept; // like Rc::downgrade() in Rust

private:
    template <typename U, typename... Args>
    friend rc<U> make_rc(Args&&... args);
    friend class weak<T>;

    explicit rc(ControlBlock<T>* ctrl) noexcept : ctrl_(ctrl) {}

    void inc_strong() noexcept { if (ctrl_) { ++ctrl_->strong; } }

    void release() noexcept {
        if (!ctrl_) return;
        assert(ctrl_->strong > 0);
        if (--ctrl_->strong == 0) {
            // Destroy T in-place
            ctrl_->ptr()->~T();
            if (ctrl_->weak == 0) {
                delete ctrl_;
                ctrl_ = nullptr;
                return;
            }
        }
        ctrl_ = nullptr;
    }

    ControlBlock<T>* ctrl_{nullptr};
};

// weak<T> — non-owning observer

template <typename T>
class weak {
public:
    weak() noexcept = default;
    weak(const weak& other) noexcept : ctrl_(other.ctrl_) { inc_weak(); }
    weak(weak&& other) noexcept : ctrl_(other.ctrl_) { other.ctrl_ = nullptr; }

    weak& operator=(const weak& other) noexcept {
        if (this != &other) { release(); ctrl_ = other.ctrl_; inc_weak(); }
        return *this;
    }

    weak& operator=(weak&& other) noexcept {
        if (this != &other) { release(); ctrl_ = other.ctrl_; other.ctrl_ = nullptr; }
        return *this;
    }

    ~weak() { release(); }

    bool expired() const noexcept { return !ctrl_ || ctrl_->strong == 0; }
    rc<T> lock() const noexcept { return rc<T>(*this); }
    void reset() noexcept { release(); }

private:
    friend class rc<T>;

    explicit weak(ControlBlock<T>* ctrl) noexcept : ctrl_(ctrl) { inc_weak(); }

    void inc_weak() noexcept { if (ctrl_) { ++ctrl_->weak; } }

    void release() noexcept {
        if (!ctrl_) return;
        assert(ctrl_->weak > 0);
        if (--ctrl_->weak == 0 && ctrl_->strong == 0) {
            delete ctrl_;
            ctrl_ = nullptr;
            return;
        }
        ctrl_ = nullptr;
    }

    ControlBlock<T>* ctrl_{nullptr};
};

// rc::downgrade implementation

template <typename T>
weak<T> rc<T>::downgrade() const noexcept { return weak<T>(ctrl_); }

// make_rc implementation (single allocation: one new for control + T)

template <typename T, typename... Args>
rc<T> make_rc(Args&&... args) {
    static_assert(!std::is_array<T>::value, "rc<T> does not support arrays");
    auto* ctrl = new ControlBlock<T>();
    try {
        ::new (static_cast<void*>(ctrl->ptr())) T(std::forward<Args>(args)...);
    } catch (...) {
        delete ctrl;
        throw;
    }
    return rc<T>(ctrl);
}

} // namespace mini_rc

/*
Usage example:

#include "rc.h"
#include <iostream>
using namespace crane;

struct Node {
    int value;
    weak<Node> parent;         // break cycles
    rc<Node> left, right;      // children own their subtrees
    explicit Node(int v): value(v) {}
    ~Node(){ std::cout << "drop Node(" << value << ")
"; }
};

int main(){
    auto root = make_rc<Node>(1);
    root->left = make_rc<Node>(2);
    root->left->parent = root.downgrade();

    std::cout << root.use_count() << "
"; // 1
}
*/
