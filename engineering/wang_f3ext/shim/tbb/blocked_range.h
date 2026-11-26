#pragma once
// tbb 垫片(手工构建用): blocked_range。
#include <cstddef>
namespace tbb {
template <class T>
class blocked_range {
 public:
  using value_type = T;
  blocked_range(T b, T e) : b_(b), e_(e) {}
  T begin() const { return b_; }
  T end() const { return e_; }
  std::size_t size() const { return static_cast<std::size_t>(e_ - b_); }
  bool empty() const { return b_ == e_; }

 private:
  T b_;
  T e_;
};
}  // namespace tbb
