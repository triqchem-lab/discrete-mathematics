#pragma once
namespace tbb {
template <class T> class blocked_range {
 public:
  blocked_range(T b, T e) : b_(b), e_(e) {}
  T begin() const { return b_; }
  T end() const { return e_; }
 private:
  T b_, e_;
};
}
