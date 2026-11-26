#pragma once
// boost::unordered_flat_set 垫片(手工构建用): 即 std::unordered_set。
#include <functional>
#include <unordered_set>
namespace boost {
template <class K, class H = std::hash<K>, class P = std::equal_to<K>>
using unordered_flat_set = std::unordered_set<K, H, P>;
namespace unordered {
using boost::unordered_flat_set;
}  // namespace unordered
}  // namespace boost
