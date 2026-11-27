// log_every_t_test.cc —— ng-log 垫片里 LOG_EVERY_T 的语义回归。
// 期望(与 glog 一致): 每个调用点、每个线程, 首次调用立即输出; 之后距上次输出不足 N 秒的调用不输出;
// 够了 N 秒再输出一次。把 stderr 重定向到文件里数行数。
// 背景: 第一版的判断是反的(间隔不足才输出), 搜索一慢进度行就全没了。
#include <chrono>
#include <cstdio>
#include <cstring>
#include <fcntl.h>
#include <string>
#include <thread>
#include <unistd.h>

#include "ng-log/logging.h"

namespace {
std::string ReadAll(const char *path) {
  FILE *f = std::fopen(path, "r");
  if (!f) return {};
  std::string s;
  char buf[4096];
  size_t n;
  while ((n = std::fread(buf, 1, sizeof(buf), f)) > 0) s.append(buf, n);
  std::fclose(f);
  return s;
}
int Count(const std::string &s, const char *needle) {
  int c = 0;
  for (size_t p = s.find(needle); p != std::string::npos; p = s.find(needle, p + 1)) ++c;
  return c;
}
} // namespace

int main() {
  const char *path = "log_every_t_test.err";
  unlink(path);
  const int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (fd < 0) {
    std::fprintf(stdout, "open failed\n");
    return 2;
  }
  const int saved = dup(2);
  std::fflush(stderr);
  dup2(fd, 2);
  const auto marker = [](int i) { LOG_EVERY_T(INFO, 1) << "MARK" << i; };
  marker(1);      // 首次: 输出
  marker(2);      // 间隔不足 1 秒: 不输出
  marker(3);      // 不输出
  std::this_thread::sleep_for(std::chrono::milliseconds(1200));
  marker(4);      // 够 1 秒: 输出
  marker(5);      // 不输出
  // 另一个调用点各有各的状态: 这个调用点第一次也要立即输出
  LOG_EVERY_T(INFO, 1) << "OTHER";
  std::fflush(stderr);
  dup2(saved, 2);
  close(saved);
  close(fd);
  const std::string out = ReadAll(path);
  const int marks = Count(out, "MARK");
  const int others = Count(out, "OTHER");
  const bool ok = marks == 2 && others == 1 && std::strstr(out.c_str(), "MARK1") != nullptr &&
                  std::strstr(out.c_str(), "MARK4") != nullptr;
  std::fprintf(stdout, "log_every_t: MARK lines=%d (expect 2: MARK1, MARK4), OTHER lines=%d (expect 1) -> %s\n",
               marks, others, ok ? "OK" : "FAILED");
  return ok ? 0 : 1;
}
