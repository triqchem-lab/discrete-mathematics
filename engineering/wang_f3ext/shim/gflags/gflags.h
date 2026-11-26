#pragma once
// gflags 垫片(手工构建用): DEFINE_bool/int32/string/uint64 + google::ParseCommandLineFlags。
// 支持 --name=value、--name value、--no{bool}、--bool=false/true; 未识别的旗标报错退出(与 gflags 一致)。
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

namespace gflags_shim {
enum Type { kBool, kInt32, kUint64, kString };
struct Flag {
  const char *name;
  Type type;
  void *val;
};
inline std::vector<Flag> &Registry() {
  static std::vector<Flag> r;
  return r;
}
inline bool Parse(int *argc, char ***argv) {
  std::vector<char *> out;
  out.push_back((*argv)[0]);
  for (int i = 1; i < *argc; ++i) {
    std::string a = (*argv)[i];
    if (a == "--") {
      for (int j = i + 1; j < *argc; ++j) out.push_back((*argv)[j]);
      break;
    }
    if (a.rfind("--", 0) != 0) {
      out.push_back((*argv)[i]);
      continue;
    }
    std::string body = a.substr(2);
    std::string name = body, value;
    bool has_value = false;
    const size_t eq = body.find('=');
    if (eq != std::string::npos) {
      name = body.substr(0, eq);
      value = body.substr(eq + 1);
      has_value = true;
    }
    bool negated = false;
    if (!name.empty() && name[0] == 'n' && name.size() > 2 && name[1] == 'o' && name[2] != '_') {
      negated = true;  // --nofoo
    }
    Flag *fl = nullptr;
    for (auto &f : Registry()) {
      if (name == f.name) {
        fl = &f;
        break;
      }
    }
    if (fl == nullptr && negated) {
      for (auto &f : Registry()) {
        if (f.type == kBool && name.substr(2) == f.name) {
          fl = &f;
          value = "false";
          has_value = true;
          break;
        }
      }
    }
    if (fl == nullptr) {
      std::fprintf(stderr, "ERROR: unknown command line flag '%s'\n", a.c_str());
      return false;
    }
    if (!has_value) {
      if (fl->type == kBool) {
        value = "true";
      } else {
        if (i + 1 >= *argc) {
          std::fprintf(stderr, "ERROR: flag '%s' needs a value\n", fl->name);
          return false;
        }
        value = (*argv)[++i];
      }
    }
    switch (fl->type) {
      case kBool:
        *static_cast<bool *>(fl->val) = (value == "true" || value == "1");
        break;
      case kInt32:
        *static_cast<int32_t *>(fl->val) = static_cast<int32_t>(std::strtol(value.c_str(), nullptr, 0));
        break;
      case kUint64:
        *static_cast<uint64_t *>(fl->val) = static_cast<uint64_t>(std::strtoull(value.c_str(), nullptr, 0));
        break;
      case kString:
        *static_cast<std::string *>(fl->val) = value;
        break;
    }
  }
  out.push_back(nullptr);
  for (size_t k = 0; k < out.size(); ++k) (*argv)[k] = out[k];
  *argc = static_cast<int>(out.size()) - 1;
  return true;
}
}  // namespace gflags_shim

#define GFLAGS_SHIM_DEFINE(cty, tid, name, val, v)                 \
  cty FLAGS_##name = static_cast<cty>(v);                           \
  static const bool gflags_shim_registered_##name =                \
      (gflags_shim::Registry().push_back({#name, tid, &FLAGS_##name}), true);
#define DEFINE_bool(name, val, txt) GFLAGS_SHIM_DEFINE(bool, gflags_shim::kBool, name, val, val)
#define DEFINE_int32(name, val, txt) GFLAGS_SHIM_DEFINE(int32_t, gflags_shim::kInt32, name, val, val)
#define DEFINE_uint64(name, val, txt) GFLAGS_SHIM_DEFINE(uint64_t, gflags_shim::kUint64, name, val, val)
#define DEFINE_string(name, val, txt) GFLAGS_SHIM_DEFINE(std::string, gflags_shim::kString, name, val, val)

namespace google {
inline void ParseCommandLineFlags(int *argc, char ***argv, bool) {
  if (!gflags_shim::Parse(argc, argv)) std::exit(1);
}
}  // namespace google
