#pragma once
// ng-log 垫片(手工构建用): CHECK 族 / LOG 族 / FLAGS_alsologtostderr / FLAGS_log_dir。
// CHECK 失败: 打印表达式与流式消息到 stderr 后 abort(非零退出)——与 ng-log 的 CHECK 语义一致。
// LOG(level): INFO 及以上默认打到 stderr(等价 FLAGS_alsologtostderr = true); LOG(FATAL) 打印后 abort。
// 流操作数只在对应级别启用时才被求值(if/else 惯用法)。
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <string>

namespace nglog {

enum class Severity { INFO = 0, WARNING = 1, ERROR = 2, FATAL = 3 };

inline Severity &MinSeverity() {
  static Severity s = Severity::INFO;
  return s;
}
inline bool LogEnabled(Severity s) { return static_cast<int>(s) >= static_cast<int>(MinSeverity()); }
inline const char *SeverityName(Severity s) {
  switch (s) {
    case Severity::INFO: return "I";
    case Severity::WARNING: return "W";
    case Severity::ERROR: return "E";
    default: return "F";
  }
}

struct Logger {
  const bool fatal;
  explicit Logger(Severity s) : fatal(s == Severity::FATAL) {}
  template <class T>
  Logger &operator<<(const T &v) {
    std::cerr << v;
    return *this;
  }
  ~Logger() {
    std::cerr << "\n";
    std::cerr.flush();
    if (fatal) std::abort();
  }
};

struct Checker {
  bool ok;
  const char *expr;
  Checker(bool o, const char *e) : ok(o), expr(e) {}
  template <class T>
  Checker &operator<<(const T &) {
    return *this;
  }
  ~Checker() {
    if (!ok) {
      std::cerr << "CHECK failed: " << expr << "\n";
      std::cerr.flush();
      std::abort();
    }
  }
};

inline void InitializeLogging(const char *) {}

}  // namespace nglog

// gflags 兼容的日志旗标(由 *_main.cc 赋值)。
inline bool FLAGS_alsologtostderr = true;
inline std::string FLAGS_log_dir;

#define LOG(level) \
  if (!nglog::LogEnabled(nglog::Severity::level)) { \
  } else \
    nglog::Logger(nglog::Severity::level) << nglog::SeverityName(nglog::Severity::level) << " "

#define CHECK(x) nglog::Checker(static_cast<bool>(x), #x)
#define CHECK_OP(a, b, op, name) nglog::Checker(((a)op(b)), name)
#define CHECK_EQ(a, b) CHECK_OP(a, b, ==, #a " == " #b)
#define CHECK_NE(a, b) CHECK_OP(a, b, !=, #a " != " #b)
#define CHECK_LE(a, b) CHECK_OP(a, b, <=, #a " <= " #b)
#define CHECK_LT(a, b) CHECK_OP(a, b, <, #a " < " #b)
#define CHECK_GE(a, b) CHECK_OP(a, b, >=, #a " >= " #b)
#define CHECK_GT(a, b) CHECK_OP(a, b, >, #a " > " #b)
#define CHECK_NOTNULL(x) (x)

// DCHECK 族: 调试断言(NDEBUG 下为空操作, 与 glog/ng-log 一致)。
#ifdef NDEBUG
#define DCHECK(x) nglog::Checker(true, #x)
#define DCHECK_OP(a, b, op, name) nglog::Checker(true, name)
#else
#define DCHECK(x) CHECK(x)
#define DCHECK_OP(a, b, op, name) CHECK_OP(a, b, op, name)
#endif
#define DCHECK_EQ(a, b) DCHECK_OP(a, b, ==, #a " == " #b)
#define DCHECK_NE(a, b) DCHECK_OP(a, b, !=, #a " != " #b)
#define DCHECK_LE(a, b) DCHECK_OP(a, b, <=, #a " <= " #b)
#define DCHECK_LT(a, b) DCHECK_OP(a, b, <, #a " < " #b)
#define DCHECK_GE(a, b) DCHECK_OP(a, b, >=, #a " >= " #b)
#define DCHECK_GT(a, b) DCHECK_OP(a, b, >, #a " > " #b)

// LOG_EVERY_T(level, 秒数): 距上次输出达到指定秒数才记录(首次立即记录), 与 glog 语义一致。
// 状态(上次输出时刻)是每个调用点一个的 thread_local, 由立即调用 lambda 内的静态局部变量承载。
// 2026-11-28 修: 第一版把判断写反了——间隔不足秒数的调用才输出, 首次调用与间隔足够的反而不输出。
// 搜索快的时候完成事件密集, 看不出问题; 一慢下来进度行就完全消失(续跑 v3 在 dim 4 上跑了 55 分钟
// 只看到 1 行, 实际至少完成了 1 条轨道)。回归测试: shim_test/log_every_t_test.cc。
#define LOG_EVERY_T(level, secs)                                                  \
  if ([&]() {                                                                    \
        static thread_local std::chrono::steady_clock::time_point pbshim_last_;   \
        if (!nglog::LogEnabled(nglog::Severity::level)) {                        \
          return true; /* 日志关着: 不输出 */                                    \
        }                                                                        \
        const auto pbshim_now = std::chrono::steady_clock::now();                 \
        if (std::chrono::duration<double>(pbshim_now - pbshim_last_).count() <    \
            static_cast<double>(secs)) {                                          \
          return true; /* 距上次输出还没到间隔: 不输出 */                        \
        }                                                                        \
        pbshim_last_ = pbshim_now;                                               \
        return false; /* 输出 */                                                 \
      }()) {                                                                     \
  } else                                                                         \
    nglog::Logger(nglog::Severity::level)                                        \
        << nglog::SeverityName(nglog::Severity::level) << " "
