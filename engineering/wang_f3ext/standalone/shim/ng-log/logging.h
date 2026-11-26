#pragma once
#include <cstdlib>
#include <iostream>
#include <string>
namespace wang_shim {
struct Checker {
  explicit Checker(bool ok, const char *expr) : ok_(ok), expr_(expr) {}
  ~Checker() { if (!ok_) { std::cerr << "CHECK failed: " << expr_ << "\n"; std::abort(); } }
  Checker &operator<<(const char *) { return *this; }
  template <class T> Checker &operator<<(const T &) { return *this; }
  bool ok_;
  const char *expr_;
};
struct Logger {
  bool fatal;
  Logger(bool f) : fatal_(f) {}
  ~Logger() { if (fatal_) std::abort(); }
  template <class T> Logger &operator<<(const T &) { return *this; }
  bool fatal_;
};
}
#define CHECK(x) wang_shim::Checker(static_cast<bool>(x), #x)
#define CHECK_GE(a, b) wang_shim::Checker((a) >= (b), #a " >= " #b)
#define CHECK_LE(a, b) wang_shim::Checker((a) <= (b), #a " <= " #b)
#define CHECK_EQ(a, b) wang_shim::Checker((a) == (b), #a " == " #b)
#define CHECK_NE(a, b) wang_shim::Checker((a) != (b), #a " != " #b)
#define CHECK_LT(a, b) wang_shim::Checker((a) < (b), #a " < " #b)
#define CHECK_GT(a, b) wang_shim::Checker((a) > (b), #a " > " #b)
#define CHECK_NOTNULL(x) (x)
#define LOG(x) wang_shim::Logger(std::string(#x) == "FATAL")
namespace nglog { inline void InitializeLogging(const char *) {} }
