#pragma once
// boost::unordered_flat_map 垫片(手工构建用): 即 std::unordered_map。
#include <functional>
#include <unordered_map>
namespace boost {
template <class K, class V, class H = std::hash<K>, class P = std::equal_to<K>>
using unordered_flat_map = std::unordered_map<K, V, H, P>;
namespace unordered {
using boost::unordered_flat_map;
}  // namespace unordered
}  // namespace boost
