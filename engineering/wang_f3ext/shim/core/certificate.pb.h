// core/certificate.pb.h —— 手写版 protobuf 消息层(手工构建用), 取代 protoc 生成的
// certificate.pb.h + libprotobuf。消息类型、字段号、访问器名逐字对应 certificate.proto;
// 文本格式(.pb.txt)与二进制 wire 格式(.pb)的读写按 protobuf 规范自实现。
#pragma once

#include <cctype>
#include <cstddef>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <istream>
#include <iterator>
#include <optional>
#include <ostream>
#include <string>
#include <string_view>
#include <vector>

namespace pbmini {

// ---------------------------------------------------------------------------
// 字段描述(反射表): 以 offsetof 访问成员, 嵌套消息经 MsgField / RepField 的统一接口访问。
// ---------------------------------------------------------------------------
enum Kind : uint8_t {
  kInt32,
  kUInt32,
  kFixed32,
  kBool,
  kStr,
  kBytes,
  kOptInt32,
  kUInt32Def,  // uint32 隐式存在
  kMsg,
  kRepMsg,
};

struct Desc;

struct MsgFieldBase {
  virtual ~MsgFieldBase() = default;
  virtual bool has() const = 0;
  virtual const void *get() const = 0;  // 未设置时 nullptr
  virtual void *ensure() = 0;           // 设置并返回指针
  virtual void clear_() = 0;
};

struct RepFieldBase {
  virtual ~RepFieldBase() = default;
  virtual std::size_t count() const = 0;
  virtual const void *at(std::size_t) const = 0;
  virtual void *at_mut(std::size_t) = 0;
  virtual void *append() = 0;
  virtual void clear_() = 0;
};

template <class M>
struct MsgField final : MsgFieldBase {
  std::optional<M> o;
  bool has() const override { return o.has_value(); }
  const void *get() const override { return o ? static_cast<const void *>(&*o) : nullptr; }
  void *ensure() override {
    if (!o) o.emplace();
    return &*o;
  }
  void clear_() override { o.reset(); }
  const M &get_ref() const {
    static const M kDefault;
    return o ? *o : kDefault;
  }
};

template <class M>
struct RepField final : RepFieldBase {
  std::vector<M> v;
  std::size_t count() const override { return v.size(); }
  const void *at(std::size_t i) const override { return &v[i]; }
  void *at_mut(std::size_t i) override { return &v[i]; }
  void *append() override {
    v.emplace_back();
    return &v.back();
  }
  void clear_() override { v.clear(); }
};

struct FieldDesc {
  const char *name;
  int num;   // protobuf 字段号
  Kind kind;
  std::size_t off;
  const Desc *sub;
};

struct Desc {
  const FieldDesc *fields;
  std::size_t n;
  const FieldDesc *Find(const std::string &name) const {
    for (std::size_t i = 0; i < n; ++i)
      if (name == fields[i].name) return &fields[i];
    return nullptr;
  }
  const FieldDesc *FindByNum(int num) const {
    for (std::size_t i = 0; i < n; ++i)
      if (fields[i].num == num) return &fields[i];
    return nullptr;
  }
};

template <class T>
inline T &F(void *obj, std::size_t off) {
  return *reinterpret_cast<T *>(static_cast<char *>(obj) + off);
}
template <class T>
inline const T &F(const void *obj, std::size_t off) {
  return *reinterpret_cast<const T *>(static_cast<const char *>(obj) + off);
}
inline MsgFieldBase &MF(void *obj, const FieldDesc &fd) { return F<MsgFieldBase>(obj, fd.off); }
inline const MsgFieldBase &MF(const void *obj, const FieldDesc &fd) { return F<MsgFieldBase>(obj, fd.off); }
inline RepFieldBase &RF(void *obj, const FieldDesc &fd) { return F<RepFieldBase>(obj, fd.off); }
inline const RepFieldBase &RF(const void *obj, const FieldDesc &fd) { return F<RepFieldBase>(obj, fd.off); }

// ---------------------------------------------------------------------------
// 文本格式: 转义 / 词法 / 解析 / 打印
// ---------------------------------------------------------------------------
std::string EscapeBytes(const std::string &s) {
  std::string out;
  out.reserve(s.size() + 8);
  for (unsigned char c : s) {
    switch (c) {
      case '\n': out += "\\n"; break;
      case '\r': out += "\\r"; break;
      case '\t': out += "\\t"; break;
      case '\"': out += "\\\""; break;
      case '\'': out += "\\'"; break;
      case '\\': out += "\\\\"; break;
      default:
        if (c < 0x20 || c >= 0x7f) {
          char buf[8];
          std::snprintf(buf, sizeof buf, "\\%03o", c);
          out += buf;
        } else {
          out.push_back(static_cast<char>(c));
        }
    }
  }
  return out;
}

struct Lexer {
  enum Tok : uint8_t {
    T_END,
    T_IDENT,
    T_NUMBER,
    T_STRING,
    T_LBRACE,
    T_RBRACE,
    T_LANGLE,
    T_RANGLE,
    T_LBRACKET,
    T_RBRACKET,
    T_COLON,
    T_COMMA,
    T_SEMI,
  };
  std::string_view s;
  std::size_t i = 0;
  Tok tok = T_END;
  std::string text;
  std::string err;

  bool Fail(const std::string &m) {
    if (err.empty()) err = m + " at offset " + std::to_string(i);
    return false;
  }
  static bool IsIdentChar(char c) {
    return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '.' || c == '/';
  }
  bool Next() {
    text.clear();
    while (i < s.size()) {
      const char c = s[i];
      if (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v') {
        ++i;
      } else if (c == '#') {
        while (i < s.size() && s[i] != '\n') ++i;
      } else {
        break;
      }
    }
    if (i >= s.size()) {
      tok = T_END;
      return true;
    }
    const char c = s[i];
    if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
      std::size_t j = i;
      while (j < s.size() && IsIdentChar(s[j])) ++j;
      text.assign(s.substr(i, j - i));
      i = j;
      tok = (text == "inf" || text == "nan") ? T_NUMBER : T_IDENT;
      return true;
    }
    const bool signed_number =
        (c == '-' || c == '+') && i + 1 < s.size() &&
        (std::isdigit(static_cast<unsigned char>(s[i + 1])) || s[i + 1] == '.' ||
         s[i + 1] == 'i' || s[i + 1] == 'n');
    if (std::isdigit(static_cast<unsigned char>(c)) || signed_number) {
      std::size_t j = i;
      if (s[j] == '-' || s[j] == '+') ++j;
      if (s.compare(j, 3, "inf") == 0 || s.compare(j, 3, "nan") == 0) {
        j += 3;
      } else {
        while (j < s.size() &&
               (std::isalnum(static_cast<unsigned char>(s[j])) || s[j] == '.' ||
                ((s[j] == '-' || s[j] == '+') && j > i &&
                 (s[j - 1] == 'e' || s[j - 1] == 'E'))))
          ++j;
      }
      text.assign(s.substr(i, j - i));
      i = j;
      tok = T_NUMBER;
      return true;
    }
    if (c == '"' || c == '\'') return LexString();
    switch (c) {
      case '{': tok = T_LBRACE; break;
      case '}': tok = T_RBRACE; break;
      case '<': tok = T_LANGLE; break;
      case '>': tok = T_RANGLE; break;
      case '[': tok = T_LBRACKET; break;
      case ']': tok = T_RBRACKET; break;
      case ':': tok = T_COLON; break;
      case ',': tok = T_COMMA; break;
      case ';': tok = T_SEMI; break;
      default: return Fail(std::string("unexpected character '") + c + "'");
    }
    ++i;
    return true;
  }
  bool LexString() {
    const char quote = s[i];
    ++i;
    for (;;) {
      if (i >= s.size()) return Fail("unterminated string");
      const char ch = s[i];
      if (ch == quote) {
        ++i;
        break;
      }
      if (ch == '\n') return Fail("newline in string literal");
      if (ch == '\\') {
        ++i;
        if (i >= s.size()) return Fail("bad escape");
        const char e = s[i];
        switch (e) {
          case 'a': text.push_back('\a'); ++i; break;
          case 'b': text.push_back('\b'); ++i; break;
          case 'f': text.push_back('\f'); ++i; break;
          case 'n': text.push_back('\n'); ++i; break;
          case 'r': text.push_back('\r'); ++i; break;
          case 't': text.push_back('\t'); ++i; break;
          case 'v': text.push_back('\v'); ++i; break;
          case '\\': text.push_back('\\'); ++i; break;
          case '\'': text.push_back('\''); ++i; break;
          case '"': text.push_back('"'); ++i; break;
          case '?': text.push_back('?'); ++i; break;
          case 'x':
          case 'X': {
            ++i;
            unsigned v = 0;
            int digits = 0;
            while (i < s.size() && digits < 2 && std::isxdigit(static_cast<unsigned char>(s[i]))) {
              v = v * 16 + HexDigit(s[i]);
              ++i;
              ++digits;
            }
            if (digits == 0) return Fail("bad hex escape");
            text.push_back(static_cast<char>(v));
            break;
          }
          case 'u':
          case 'U': {
            const int want = (e == 'u') ? 4 : 8;
            ++i;
            unsigned long v = 0;
            for (int k = 0; k < want; ++k) {
              if (i >= s.size() || !std::isxdigit(static_cast<unsigned char>(s[i])))
                return Fail("bad unicode escape");
              v = v * 16 + HexDigit(s[i]);
              ++i;
            }
            AppendUtf8(text, v);
            break;
          }
          default: {
            if (e >= '0' && e <= '7') {
              unsigned v = 0;
              int digits = 0;
              while (i < s.size() && digits < 3 && s[i] >= '0' && s[i] <= '7') {
                v = v * 8 + static_cast<unsigned>(s[i] - '0');
                ++i;
                ++digits;
              }
              text.push_back(static_cast<char>(v & 0xff));
            } else {
              return Fail(std::string("invalid escape '\\") + e + "'");
            }
          }
        }
      } else {
        text.push_back(ch);
        ++i;
      }
    }
    tok = T_STRING;
    return true;
  }
  static unsigned HexDigit(char c) {
    if (c >= '0' && c <= '9') return static_cast<unsigned>(c - '0');
    if (c >= 'a' && c <= 'f') return static_cast<unsigned>(c - 'a' + 10);
    return static_cast<unsigned>(c - 'A' + 10);
  }
  static void AppendUtf8(std::string &out, unsigned long cp) {
    if (cp < 0x80) {
      out.push_back(static_cast<char>(cp));
    } else if (cp < 0x800) {
      out.push_back(static_cast<char>(0xc0 | (cp >> 6)));
      out.push_back(static_cast<char>(0x80 | (cp & 0x3f)));
    } else if (cp < 0x10000) {
      out.push_back(static_cast<char>(0xe0 | (cp >> 12)));
      out.push_back(static_cast<char>(0x80 | ((cp >> 6) & 0x3f)));
      out.push_back(static_cast<char>(0x80 | (cp & 0x3f)));
    } else {
      out.push_back(static_cast<char>(0xf0 | (cp >> 18)));
      out.push_back(static_cast<char>(0x80 | ((cp >> 12) & 0x3f)));
      out.push_back(static_cast<char>(0x80 | ((cp >> 6) & 0x3f)));
      out.push_back(static_cast<char>(0x80 | (cp & 0x3f)));
    }
  }
};

inline bool ParseBool(const Lexer &lx, bool *out) {
  if (lx.tok == Lexer::T_IDENT && lx.text == "true") *out = true;
  else if (lx.tok == Lexer::T_IDENT && lx.text == "false") *out = false;
  else if (lx.tok == Lexer::T_NUMBER && lx.text == "1") *out = true;
  else if (lx.tok == Lexer::T_NUMBER && lx.text == "0") *out = false;
  else return false;
  return true;
}

bool ParseMsg(Lexer &lx, void *obj, const Desc &d, bool top, std::string * err, int depth);

inline bool ParseFieldMessage(Lexer &lx, void *obj, const FieldDesc &fd, std::string *err, int depth) {
  Lexer::Tok closer;
  if (lx.tok == Lexer::T_LBRACE) closer = Lexer::T_RBRACE;
  else if (lx.tok == Lexer::T_LANGLE) closer = Lexer::T_RANGLE;
  else {
    *err = "expected '{' after message field '" + std::string(fd.name) + "'";
    return false;
  }
  void *sub;
  if (fd.kind == kMsg) sub = MF(obj, fd).ensure();
  else sub = RF(obj, fd).append();
  if (!ParseMsg(lx, sub, *fd.sub, false, err, depth + 1)) return false;
  if (lx.tok != closer) {
    *err = "mismatched closing bracket for field '" + std::string(fd.name) + "'";
    return false;
  }
  return true;
}

inline bool ParseFieldScalar(Lexer &lx, void *obj, const FieldDesc &fd, std::string *err) {
  char *dst = static_cast<char *>(obj) + fd.off;
  switch (fd.kind) {
    case kInt32:
    case kOptInt32: {
      if (lx.tok != Lexer::T_NUMBER) {
        *err = "expected integer for '" + std::string(fd.name) + "'";
        return false;
      }
      const long v = std::strtol(lx.text.c_str(), nullptr, 0);
      if (fd.kind == kInt32) *reinterpret_cast<int32_t *>(dst) = static_cast<int32_t>(v);
      else reinterpret_cast<std::optional<int32_t> *>(dst)->emplace(static_cast<int32_t>(v));
      return true;
    }
    case kUInt32:
    case kUInt32Def:
    case kFixed32: {
      if (lx.tok != Lexer::T_NUMBER) {
        *err = "expected unsigned integer for '" + std::string(fd.name) + "'";
        return false;
      }
      const unsigned long v = std::strtoul(lx.text.c_str(), nullptr, 0);
      *reinterpret_cast<uint32_t *>(dst) = static_cast<uint32_t>(v);
      return true;
    }
    case kBool: {
      bool b;
      if (!ParseBool(lx, &b)) {
        *err = "expected true/false for '" + std::string(fd.name) + "'";
        return false;
      }
      *reinterpret_cast<bool *>(dst) = b;
      return true;
    }
    case kStr:
    case kBytes: {
      if (lx.tok != Lexer::T_STRING) {
        *err = "expected string for '" + std::string(fd.name) + "'";
        return false;
      }
      std::string &dst_s = *reinterpret_cast<std::string *>(dst);
      dst_s.append(lx.text);
      // 相邻字符串字面量拼接
      for (;;) {
        const std::size_t si = lx.i;
        const Lexer::Tok st = lx.tok;
        const std::string stext = lx.text;
        if (!lx.Next()) return false;
        if (lx.tok == Lexer::T_STRING) {
          dst_s.append(lx.text);
          continue;
        }
        // 回退一个词法单元
        lx.i = si;
        lx.tok = st;
        lx.text = stext;
        return true;
      }
    }
    default:
      *err = "unexpected scalar kind";
      return false;
  }
}

inline bool ParseMsg(Lexer &lx, void *obj, const Desc &d, bool top, std::string *err, int depth) {
  if (depth > 64) {
    *err = "message nesting too deep";
    return false;
  }
  for (;;) {
    if (!lx.Next()) {
      *err = lx.err;
      return false;
    }
    if (lx.tok == Lexer::T_END) {
      if (!top) {
        *err = "unexpected end of input inside message";
        return false;
      }
      return true;
    }
    if (lx.tok == Lexer::T_RBRACE || lx.tok == Lexer::T_RANGLE) return true;  // 交给调用方核对
    if (lx.tok == Lexer::T_COMMA || lx.tok == Lexer::T_SEMI) continue;
    if (lx.tok != Lexer::T_IDENT) {
      *err = "expected field name";
      return false;
    }
    const FieldDesc *fd = d.Find(lx.text);
    if (fd == nullptr) {
      *err = "unknown field '" + lx.text + "'";
      return false;
    }
    if (!lx.Next()) {
      *err = lx.err;
      return false;
    }
    bool has_colon = false;
    if (lx.tok == Lexer::T_COLON) {
      has_colon = true;
      if (!lx.Next()) {
        *err = lx.err;
        return false;
      }
    }
    if (fd->kind == kMsg || fd->kind == kRepMsg) {
      if (!has_colon && lx.tok == Lexer::T_COLON) {  // `field : {`
        if (!lx.Next()) {
          *err = lx.err;
          return false;
        }
      }
      if (!ParseFieldMessage(lx, obj, *fd, err, depth)) return false;
    } else {
      if (!has_colon) {
        *err = "expected ':' after field '" + std::string(fd->name) + "'";
        return false;
      }
      if (!ParseFieldScalar(lx, obj, *fd, err)) return false;
    }
  }
}

inline void PrintText(const void *obj, const Desc &d, std::string *out, int indent) {
  const std::string pad(static_cast<std::size_t>(indent) * 2, ' ');
  for (std::size_t i = 0; i < d.n; ++i) {
    const FieldDesc &fd = d.fields[i];
    const char *base = static_cast<const char *>(obj) + fd.off;
    switch (fd.kind) {
      case kInt32:
        *out += pad + fd.name + ": " + std::to_string(*reinterpret_cast<const int32_t *>(base)) + "\n";
        break;
      case kOptInt32: {
        const auto &o = *reinterpret_cast<const std::optional<int32_t> *>(base);
        if (o) *out += pad + fd.name + ": " + std::to_string(*o) + "\n";
        break;
      }
      case kUInt32:
      case kFixed32:
        *out += pad + fd.name + ": " + std::to_string(*reinterpret_cast<const uint32_t *>(base)) + "\n";
        break;
      case kUInt32Def: {
        const uint32_t v = *reinterpret_cast<const uint32_t *>(base);
        if (v != 0) *out += pad + fd.name + ": " + std::to_string(v) + "\n";
        break;
      }
      case kBool:
        *out += pad + fd.name + ": " + (*reinterpret_cast<const bool *>(base) ? "true" : "false") + "\n";
        break;
      case kStr:
      case kBytes:
        *out += pad + fd.name + ": \"" + EscapeBytes(*reinterpret_cast<const std::string *>(base)) + "\"\n";
        break;
      case kMsg: {
        const MsgFieldBase &mf = MF(obj, fd);
        if (mf.has()) {
          *out += pad + fd.name + " {\n";
          PrintText(mf.get(), *fd.sub, out, indent + 1);
          *out += pad + "}\n";
        }
        break;
      }
      case kRepMsg: {
        const RepFieldBase &rf = RF(obj, fd);
        for (std::size_t k = 0; k < rf.count(); ++k) {
          *out += pad + fd.name + " {\n";
          PrintText(rf.at(k), *fd.sub, out, indent + 1);
          *out += pad + "}\n";
        }
        break;
      }
    }
  }
}

// ---------------------------------------------------------------------------
// 二进制 wire 格式
// ---------------------------------------------------------------------------
inline void PutVarint(std::string *out, uint64_t v) {
  while (v >= 0x80) {
    out->push_back(static_cast<char>((v & 0x7f) | 0x80));
    v >>= 7;
  }
  out->push_back(static_cast<char>(v));
}
inline bool GetVarint(std::string_view s, std::size_t *pos, uint64_t *v) {
  uint64_t r = 0;
  int shift = 0;
  while (*pos < s.size() && shift < 64) {
    const unsigned char b = static_cast<unsigned char>(s[(*pos)++]);
    r |= static_cast<uint64_t>(b & 0x7f) << shift;
    if (!(b & 0x80)) {
      *v = r;
      return true;
    }
    shift += 7;
  }
  return false;
}
inline void PutTag(std::string *out, int num, int wire) { PutVarint(out, (static_cast<uint64_t>(num) << 3) | static_cast<unsigned>(wire)); }

inline bool SerializeBinary(const void *obj, const Desc &d, std::string *out) {
  for (std::size_t i = 0; i < d.n; ++i) {
    const FieldDesc &fd = d.fields[i];
    const char *base = static_cast<const char *>(obj) + fd.off;
    switch (fd.kind) {
      case kInt32: {
        const int32_t v = *reinterpret_cast<const int32_t *>(base);
        PutTag(out, fd.num, 0);
        PutVarint(out, static_cast<uint64_t>(static_cast<int64_t>(v)));
        break;
      }
      case kOptInt32: {
        const auto &o = *reinterpret_cast<const std::optional<int32_t> *>(base);
        if (o) {
          PutTag(out, fd.num, 0);
          PutVarint(out, static_cast<uint64_t>(static_cast<int64_t>(*o)));
        }
        break;
      }
      case kUInt32:
      case kBool: {
        const uint64_t v = fd.kind == kBool ? (*reinterpret_cast<const bool *>(base) ? 1 : 0)
                                            : *reinterpret_cast<const uint32_t *>(base);
        PutTag(out, fd.num, 0);
        PutVarint(out, v);
        break;
      }
      case kUInt32Def: {
        const uint32_t v = *reinterpret_cast<const uint32_t *>(base);
        if (v != 0) {
          PutTag(out, fd.num, 0);
          PutVarint(out, v);
        }
        break;
      }
      case kFixed32: {
        const uint32_t v = *reinterpret_cast<const uint32_t *>(base);
        PutTag(out, fd.num, 5);
        for (int k = 0; k < 4; ++k) out->push_back(static_cast<char>((v >> (8 * k)) & 0xff));
        break;
      }
      case kStr:
      case kBytes: {
        const std::string &v = *reinterpret_cast<const std::string *>(base);
        PutTag(out, fd.num, 2);
        PutVarint(out, v.size());
        out->append(v);
        break;
      }
      case kMsg: {
        const MsgFieldBase &mf = MF(obj, fd);
        if (mf.has()) {
          std::string sub;
          if (!SerializeBinary(mf.get(), *fd.sub, &sub)) return false;
          PutTag(out, fd.num, 2);
          PutVarint(out, sub.size());
          out->append(sub);
        }
        break;
      }
      case kRepMsg: {
        const RepFieldBase &rf = RF(obj, fd);
        for (std::size_t k = 0; k < rf.count(); ++k) {
          std::string sub;
          if (!SerializeBinary(rf.at(k), *fd.sub, &sub)) return false;
          PutTag(out, fd.num, 2);
          PutVarint(out, sub.size());
          out->append(sub);
        }
        break;
      }
    }
  }
  return true;
}

inline bool ParseBinary(void *obj, const Desc &d, std::string_view s) {
  std::size_t pos = 0;
  while (pos < s.size()) {
    uint64_t key;
    if (!GetVarint(s, &pos, &key)) return false;
    const int num = static_cast<int>(key >> 3);
    const int wire = static_cast<int>(key & 7);
    const FieldDesc *fd = d.FindByNum(num);
    uint64_t v = 0;
    if (wire == 0) {
      if (!GetVarint(s, &pos, &v)) return false;
    } else if (wire == 5) {
      if (pos + 4 > s.size()) return false;
      v = static_cast<unsigned char>(s[pos]) | (static_cast<unsigned char>(s[pos + 1]) << 8) |
          (static_cast<unsigned char>(s[pos + 2]) << 16) |
          (static_cast<uint64_t>(static_cast<unsigned char>(s[pos + 3])) << 24);
      pos += 4;
    } else if (wire == 2) {
      uint64_t len;
      if (!GetVarint(s, &pos, &len)) return false;
      if (pos + len > s.size()) return false;
      const std::string_view chunk = s.substr(pos, static_cast<std::size_t>(len));
      pos += static_cast<std::size_t>(len);
      if (fd != nullptr) {
        char *dst = static_cast<char *>(obj) + fd->off;
        if (fd->kind == kStr || fd->kind == kBytes) {
          *reinterpret_cast<std::string *>(dst) = std::string(chunk);
        } else if (fd->kind == kMsg) {
          if (!ParseBinary(MF(obj, *fd).ensure(), *fd->sub, chunk)) return false;
        } else if (fd->kind == kRepMsg) {
          if (!ParseBinary(RF(obj, *fd).append(), *fd->sub, chunk)) return false;
        } else {
          return false;
        }
      }
      continue;
    } else if (wire == 1) {
      if (pos + 8 > s.size()) return false;
      pos += 8;
      continue;
    } else {
      return false;
    }
    if (fd == nullptr) continue;  // 未知字段: 跳过
    char *dst = static_cast<char *>(obj) + fd->off;
    switch (fd->kind) {
      case kInt32: *reinterpret_cast<int32_t *>(dst) = static_cast<int32_t>(static_cast<int64_t>(v)); break;
      case kOptInt32:
        reinterpret_cast<std::optional<int32_t> *>(dst)->emplace(static_cast<int32_t>(static_cast<int64_t>(v)));
        break;
      case kUInt32:
      case kUInt32Def:
      case kFixed32: *reinterpret_cast<uint32_t *>(dst) = static_cast<uint32_t>(v); break;
      case kBool: *reinterpret_cast<bool *>(dst) = (v != 0); break;
      default: return false;
    }
  }
  return true;
}

inline void ClearFields(void *obj, const Desc &d) {
  for (std::size_t i = 0; i < d.n; ++i) {
    const FieldDesc &fd = d.fields[i];
    char *dst = static_cast<char *>(obj) + fd.off;
    switch (fd.kind) {
      case kInt32: *reinterpret_cast<int32_t *>(dst) = 0; break;
      case kOptInt32: reinterpret_cast<std::optional<int32_t> *>(dst)->reset(); break;
      case kUInt32:
      case kUInt32Def:
      case kFixed32: *reinterpret_cast<uint32_t *>(dst) = 0; break;
      case kBool: *reinterpret_cast<bool *>(dst) = false; break;
      case kStr:
      case kBytes: reinterpret_cast<std::string *>(dst)->clear(); break;
      case kMsg: MF(obj, fd).clear_(); break;
      case kRepMsg: RF(obj, fd).clear_(); break;
    }
  }
}

// ---------------------------------------------------------------------------
// 消息基类: protobuf 生成代码同名的 I/O 方法
// ---------------------------------------------------------------------------
template <class M>
struct MsgBase {
  bool ParseTextFromString(std::string_view text, std::string * err) {
    Lexer lx;
    lx.s = text;
    if (!ParseMsg(lx, static_cast<M *>(this), M::descriptor(), true, err, 0)) return false;
    if (lx.tok != Lexer::T_END) {
      *err = "unexpected closing bracket";
      return false;
    }
    return true;
  }
  bool ParseTextFromIstream(std::istream *in) {
    const std::string text((std::istreambuf_iterator<char>(*in)), std::istreambuf_iterator<char>());
    std::string err;
    if (!ParseTextFromString(text, &err)) {
      std::fprintf(stderr, "text parse error: %s\n", err.c_str());
      return false;
    }
    return true;
  }
  std::string TextDebugString() const {
    std::string out;
    PrintText(static_cast<const M *>(this), M::descriptor(), &out, 0);
    return out;
  }
  bool ParseFromIstream(std::istream *in) {
    const std::string data((std::istreambuf_iterator<char>(*in)), std::istreambuf_iterator<char>());
    return ParseBinary(static_cast<M *>(this), M::descriptor(), data);
  }
  bool SerializeToOstream(std::ostream *out) const {
    std::string data;
    if (!SerializeBinary(static_cast<const M *>(this), M::descriptor(), &data)) return false;
    out->write(data.data(), static_cast<std::streamsize>(data.size()));
    return static_cast<bool>(*out);
  }
  std::size_t ByteSizeLong() const {
    std::string data;
    SerializeBinary(static_cast<const M *>(this), M::descriptor(), &data);
    return data.size();
  }
  void Clear() { ClearFields(static_cast<M *>(this), M::descriptor()); }
};

}  // namespace pbmini

// ---------------------------------------------------------------------------
// 消息类型(逐字对应 certificate.proto)
// ---------------------------------------------------------------------------
namespace pb {

struct FlattenMatrixProof : pbmini::MsgBase<FlattenMatrixProof> {
  static const pbmini::Desc &descriptor();
  bool operator==(const FlattenMatrixProof &) const { return true; }
};

struct ForcedProductProof : pbmini::MsgBase<ForcedProductProof> {
  uint32_t projection_type_ = 0;
  uint32_t projection_type() const { return projection_type_; }
  void set_projection_type(uint32_t v) { projection_type_ = v; }
  static const pbmini::Desc &descriptor();
};

struct Transformation : pbmini::MsgBase<Transformation> {
  uint32_t query_elem_ = 0;
  uint32_t store_elem_ = 0;
  uint32_t query_elem() const { return query_elem_; }
  uint32_t store_elem() const { return store_elem_; }
  void set_query_elem(uint32_t v) { query_elem_ = v; }
  void set_store_elem(uint32_t v) { store_elem_ = v; }
  static const pbmini::Desc &descriptor();
};

struct DegenerateProof : pbmini::MsgBase<DegenerateProof> {
  uint32_t extra_constraint_ = 0;
  pbmini::MsgField<Transformation> transformation_;
  uint32_t extra_constraint() const { return extra_constraint_; }
  void set_extra_constraint(uint32_t v) { extra_constraint_ = v; }
  const Transformation &transformation() const { return transformation_.get_ref(); }
  Transformation *mutable_transformation() {
    return static_cast<Transformation *>(transformation_.ensure());
  }
  static const pbmini::Desc &descriptor();
};

struct BacktrackingProof : pbmini::MsgBase<BacktrackingProof> {
  uint32_t proof_size_ = 0;
  uint32_t proof_size() const { return proof_size_; }
  void set_proof_size(uint32_t v) { proof_size_ = v; }
  static const pbmini::Desc &descriptor();
};

struct RankLowerBoundProof : pbmini::MsgBase<RankLowerBoundProof> {
  enum ProofCase {
    PROOF_NOT_SET = 0,
    kFlattenMatrixProof = 1,
    kForcedProductProof = 2,
    kDegenerateProof = 3,
    kBacktrackingProof = 4,
  };
  pbmini::MsgField<FlattenMatrixProof> flatten_matrix_proof_;
  pbmini::MsgField<ForcedProductProof> forced_product_proof_;
  pbmini::MsgField<DegenerateProof> degenerate_proof_;
  pbmini::MsgField<BacktrackingProof> backtracking_proof_;

  ProofCase proof_case() const {
    if (flatten_matrix_proof_.has()) return kFlattenMatrixProof;
    if (forced_product_proof_.has()) return kForcedProductProof;
    if (degenerate_proof_.has()) return kDegenerateProof;
    if (backtracking_proof_.has()) return kBacktrackingProof;
    return PROOF_NOT_SET;
  }
  bool has_flatten_matrix_proof() const { return flatten_matrix_proof_.has(); }
  bool has_forced_product_proof() const { return forced_product_proof_.has(); }
  bool has_degenerate_proof() const { return degenerate_proof_.has(); }
  bool has_backtracking_proof() const { return backtracking_proof_.has(); }
  const FlattenMatrixProof &flatten_matrix_proof() const { return flatten_matrix_proof_.get_ref(); }
  const ForcedProductProof &forced_product_proof() const { return forced_product_proof_.get_ref(); }
  const DegenerateProof &degenerate_proof() const { return degenerate_proof_.get_ref(); }
  const BacktrackingProof &backtracking_proof() const { return backtracking_proof_.get_ref(); }
  FlattenMatrixProof *mutable_flatten_matrix_proof() {
    ClearOneof();
    return static_cast<FlattenMatrixProof *>(flatten_matrix_proof_.ensure());
  }
  ForcedProductProof *mutable_forced_product_proof() {
    ClearOneof();
    return static_cast<ForcedProductProof *>(forced_product_proof_.ensure());
  }
  DegenerateProof *mutable_degenerate_proof() {
    ClearOneof();
    return static_cast<DegenerateProof *>(degenerate_proof_.ensure());
  }
  BacktrackingProof *mutable_backtracking_proof() {
    ClearOneof();
    return static_cast<BacktrackingProof *>(backtracking_proof_.ensure());
  }
  static const pbmini::Desc &descriptor();

 private:
  void ClearOneof() {
    flatten_matrix_proof_.clear_();
    forced_product_proof_.clear_();
    degenerate_proof_.clear_();
    backtracking_proof_.clear_();
  }
};

struct ConstrainedTensor : pbmini::MsgBase<ConstrainedTensor> {
  uint32_t index_ = 0;  // proto3 隐式存在: 为 0 时不打印/不序列化
  std::string constraints_;
  std::string constraints_text_;
  std::string tensor_text_;
  std::optional<int32_t> rank_lower_bound_;
  pbmini::MsgField<RankLowerBoundProof> rank_lower_bound_proof_;
  std::optional<int32_t> rank_upper_bound_;
  std::string rank_upper_bound_proof_;

  uint32_t index() const { return index_; }
  void set_index(uint32_t v) { index_ = v; }
  const std::string &constraints() const { return constraints_; }
  void set_constraints(const std::string &v) { constraints_ = v; }
  const std::string &constraints_text() const { return constraints_text_; }
  void set_constraints_text(const std::string &v) { constraints_text_ = v; }
  const std::string &tensor_text() const { return tensor_text_; }
  void set_tensor_text(const std::string &v) { tensor_text_ = v; }
  bool has_rank_lower_bound() const { return rank_lower_bound_.has_value(); }
  int32_t rank_lower_bound() const { return rank_lower_bound_.value_or(0); }
  void set_rank_lower_bound(int32_t v) { rank_lower_bound_ = v; }
  void clear_rank_lower_bound() { rank_lower_bound_.reset(); }
  bool has_rank_upper_bound() const { return rank_upper_bound_.has_value(); }
  int32_t rank_upper_bound() const { return rank_upper_bound_.value_or(0); }
  void set_rank_upper_bound(int32_t v) { rank_upper_bound_ = v; }
  const std::string &rank_upper_bound_proof() const { return rank_upper_bound_proof_; }
  void set_rank_upper_bound_proof(const std::string &v) { rank_upper_bound_proof_ = v; }
  const RankLowerBoundProof &rank_lower_bound_proof() const { return rank_lower_bound_proof_.get_ref(); }
  RankLowerBoundProof *mutable_rank_lower_bound_proof() {
    return static_cast<RankLowerBoundProof *>(rank_lower_bound_proof_.ensure());
  }
  bool has_rank_lower_bound_proof() const { return rank_lower_bound_proof_.has(); }
  void clear_rank_lower_bound_proof() { rank_lower_bound_proof_.clear_(); }
  static const pbmini::Desc &descriptor();
};

struct Certificate : pbmini::MsgBase<Certificate> {
  std::string problem_name_;
  int32_t characteristic_ = 0;
  int32_t extension_degree_ = 0;
  int32_t na_ = 0;
  int32_t nb_ = 0;
  int32_t nc_ = 0;
  pbmini::RepField<ConstrainedTensor> constrained_tensors_;

  const std::string &problem_name() const { return problem_name_; }
  void set_problem_name(const std::string &v) { problem_name_ = v; }
  int32_t characteristic() const { return characteristic_; }
  void set_characteristic(int32_t v) { characteristic_ = v; }
  int32_t extension_degree() const { return extension_degree_; }
  void set_extension_degree(int32_t v) { extension_degree_ = v; }
  int32_t na() const { return na_; }
  void set_na(int32_t v) { na_ = v; }
  int32_t nb() const { return nb_; }
  void set_nb(int32_t v) { nb_ = v; }
  int32_t nc() const { return nc_; }
  void set_nc(int32_t v) { nc_ = v; }
  int constrained_tensors_size() const { return static_cast<int>(constrained_tensors_.v.size()); }
  const std::vector<ConstrainedTensor> &constrained_tensors() const { return constrained_tensors_.v; }
  std::vector<ConstrainedTensor> *mutable_constrained_tensors() { return &constrained_tensors_.v; }
  const ConstrainedTensor &constrained_tensors(int i) const {
    return constrained_tensors_.v[static_cast<std::size_t>(i)];
  }
  ConstrainedTensor *mutable_constrained_tensors(int i) {
    return &constrained_tensors_.v[static_cast<std::size_t>(i)];
  }
  ConstrainedTensor *add_constrained_tensors() {
    constrained_tensors_.v.emplace_back();
    return &constrained_tensors_.v.back();
  }
  static const pbmini::Desc &descriptor();
};


// ---------------------------------------------------------------------------
// 描述符(字段号逐字对应 certificate.proto)
// ---------------------------------------------------------------------------
#define PBMINI_OFF(M, f) offsetof(M, f)
#define PBMINI_FD(name_, num_, kind_, off_, sub_) \
  { name_, num_, kind_, off_, sub_ }

inline const pbmini::Desc &FlattenMatrixProof::descriptor() {
  static const pbmini::FieldDesc kF[] = {};
  static const pbmini::Desc kD = {kF, 0};
  return kD;
}
inline const pbmini::Desc &ForcedProductProof::descriptor() {
  static const pbmini::FieldDesc kF[] = {
      PBMINI_FD("projection_type", 1, pbmini::kUInt32, PBMINI_OFF(ForcedProductProof, projection_type_), nullptr)};
  static const pbmini::Desc kD = {kF, 1};
  return kD;
}
inline const pbmini::Desc &Transformation::descriptor() {
  static const pbmini::FieldDesc kF[] = {
      PBMINI_FD("query_elem", 1, pbmini::kFixed32, PBMINI_OFF(Transformation, query_elem_), nullptr),
      PBMINI_FD("store_elem", 2, pbmini::kFixed32, PBMINI_OFF(Transformation, store_elem_), nullptr)};
  static const pbmini::Desc kD = {kF, 2};
  return kD;
}
inline const pbmini::Desc &DegenerateProof::descriptor() {
  static const pbmini::FieldDesc kF[] = {
      PBMINI_FD("extra_constraint", 1, pbmini::kFixed32, PBMINI_OFF(DegenerateProof, extra_constraint_), nullptr),
      PBMINI_FD("transformation", 2, pbmini::kMsg, PBMINI_OFF(DegenerateProof, transformation_), &Transformation::descriptor())};
  static const pbmini::Desc kD = {kF, 2};
  return kD;
}
inline const pbmini::Desc &BacktrackingProof::descriptor() {
  static const pbmini::FieldDesc kF[] = {
      PBMINI_FD("proof_size", 1, pbmini::kUInt32, PBMINI_OFF(BacktrackingProof, proof_size_), nullptr)};
  static const pbmini::Desc kD = {kF, 1};
  return kD;
}
inline const pbmini::Desc &RankLowerBoundProof::descriptor() {
  static const pbmini::FieldDesc kF[] = {
      PBMINI_FD("flatten_matrix_proof", 1, pbmini::kMsg, PBMINI_OFF(RankLowerBoundProof, flatten_matrix_proof_), &FlattenMatrixProof::descriptor()),
      PBMINI_FD("forced_product_proof", 2, pbmini::kMsg, PBMINI_OFF(RankLowerBoundProof, forced_product_proof_), &ForcedProductProof::descriptor()),
      PBMINI_FD("degenerate_proof", 3, pbmini::kMsg, PBMINI_OFF(RankLowerBoundProof, degenerate_proof_), &DegenerateProof::descriptor()),
      PBMINI_FD("backtracking_proof", 4, pbmini::kMsg, PBMINI_OFF(RankLowerBoundProof, backtracking_proof_), &BacktrackingProof::descriptor())};
  static const pbmini::Desc kD = {kF, 4};
  return kD;
}
inline const pbmini::Desc &ConstrainedTensor::descriptor() {
  static const pbmini::FieldDesc kF[] = {
      PBMINI_FD("index", 1, pbmini::kUInt32Def, PBMINI_OFF(ConstrainedTensor, index_), nullptr),
      PBMINI_FD("constraints", 2, pbmini::kBytes, PBMINI_OFF(ConstrainedTensor, constraints_), nullptr),
      PBMINI_FD("constraints_text", 3, pbmini::kStr, PBMINI_OFF(ConstrainedTensor, constraints_text_), nullptr),
      PBMINI_FD("tensor_text", 4, pbmini::kStr, PBMINI_OFF(ConstrainedTensor, tensor_text_), nullptr),
      PBMINI_FD("rank_lower_bound", 5, pbmini::kOptInt32, PBMINI_OFF(ConstrainedTensor, rank_lower_bound_), nullptr),
      PBMINI_FD("rank_lower_bound_proof", 6, pbmini::kMsg, PBMINI_OFF(ConstrainedTensor, rank_lower_bound_proof_), &RankLowerBoundProof::descriptor()),
      PBMINI_FD("rank_upper_bound", 7, pbmini::kOptInt32, PBMINI_OFF(ConstrainedTensor, rank_upper_bound_), nullptr),
      PBMINI_FD("rank_upper_bound_proof", 8, pbmini::kStr, PBMINI_OFF(ConstrainedTensor, rank_upper_bound_proof_), nullptr)};
  static const pbmini::Desc kD = {kF, 8};
  return kD;
}
inline const pbmini::Desc &Certificate::descriptor() {
  static const pbmini::FieldDesc kF[] = {
      PBMINI_FD("problem_name", 1, pbmini::kStr, PBMINI_OFF(Certificate, problem_name_), nullptr),
      PBMINI_FD("characteristic", 2, pbmini::kInt32, PBMINI_OFF(Certificate, characteristic_), nullptr),
      PBMINI_FD("extension_degree", 3, pbmini::kInt32, PBMINI_OFF(Certificate, extension_degree_), nullptr),
      PBMINI_FD("na", 4, pbmini::kInt32, PBMINI_OFF(Certificate, na_), nullptr),
      PBMINI_FD("nb", 5, pbmini::kInt32, PBMINI_OFF(Certificate, nb_), nullptr),
      PBMINI_FD("nc", 6, pbmini::kInt32, PBMINI_OFF(Certificate, nc_), nullptr),
      PBMINI_FD("constrained_tensors", 7, pbmini::kRepMsg, PBMINI_OFF(Certificate, constrained_tensors_), &ConstrainedTensor::descriptor())};
  static const pbmini::Desc kD = {kF, 7};
  return kD;
}
#undef PBMINI_FD
#undef PBMINI_OFF

}  // namespace pb
