// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Skip List Node implementation for STM-based skip list
// This file provides the C++ runtime support for the extracted Rocq skip list.

#ifndef SKIPNODE_H
#define SKIPNODE_H

#include <memory>
#include <optional>
#include <vector>
#include <mini_stm.h>

template <typename K, typename V>
struct SkipNode {
    K key;
    std::shared_ptr<stm::TVar<V>> value;
    std::vector<std::shared_ptr<stm::TVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>>> forward;
    unsigned int level;

    SkipNode(K k, V v, unsigned int lvl)
        : key(std::move(k))
        , value(stm::newTVar<V>(std::move(v)))
        , level(lvl)
    {
        // Create forward pointers for levels 0 to lvl (inclusive)
        forward.reserve(lvl + 1);
        for (unsigned int i = 0; i <= lvl; ++i) {
            forward.push_back(
                stm::newTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(std::nullopt)
            );
        }
    }

    // Factory method that returns a shared_ptr to a new node
    static std::shared_ptr<SkipNode<K, V>> create(K k, V v, unsigned int lvl) {
        return std::make_shared<SkipNode<K, V>>(std::move(k), std::move(v), lvl);
    }
};

#endif // SKIPNODE_H
