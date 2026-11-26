#pragma once
// boost::iostreams 垫片(手工构建用): 过滤流 + gzip 过滤器 + 源/汇设备。
// 用系统 zlib 实现整缓冲式链路: 过滤输入流在链路完整时把源数据整段读入并依次过各过滤器;
// 过滤输出流在关闭时把累积数据依次过各过滤器后写入汇。框架用到的 API:
//   io::filtering_istream in; in.push(io::gzip_decompressor()); in.push(io::file_source(path, std::ios::binary));
//   io::filtering_istream in; in.push(io::gzip_decompressor()); in.push(io::array_source(p, n));
//   io::filtering_ostream out; out.push(io::gzip_compressor()); out.push(io::back_inserter(str)); … io::close(out);
//   io::filtering_ostream out; out.push(io::gzip_compressor()); out.push(io::file_sink(path));
// 链路约定与 boost.iostreams 相同: 数据总是从后 push 的部件流向前 push 的部件。
#include <cstdio>
#include <cstring>
#include <fstream>
#include <istream>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <vector>

#include <zlib.h>

namespace boost {
namespace iostreams {

class source {
 public:
  virtual ~source() = default;
  // 读至多 n 字节到 s, 返回读到的字节数; EOF 返回 -1。
  virtual std::streamsize read(char *s, std::streamsize n) = 0;
};

class sink {
 public:
  virtual ~sink() = default;
  virtual void write(const char *s, std::streamsize n) = 0;
  virtual void flush() {}
  virtual bool ok() const { return true; }
};

class filter {
 public:
  virtual ~filter() = default;
  virtual std::string process(const std::string &in) = 0;
};

// ---- gzip(整缓冲) ----
inline std::string InflateAuto(const std::string &in) {  // 自动识别 gzip / zlib 头
  z_stream zs;
  std::memset(&zs, 0, sizeof zs);
  if (inflateInit2(&zs, 15 + 32) != Z_OK) throw std::runtime_error("inflateInit2 failed");
  zs.next_in = reinterpret_cast<Bytef *>(const_cast<char *>(in.data()));
  zs.avail_in = static_cast<uInt>(in.size());
  std::string out;
  char tmp[65536];
  for (;;) {
    zs.next_out = reinterpret_cast<Bytef *>(tmp);
    zs.avail_out = sizeof tmp;
    const int rc = inflate(&zs, Z_NO_FLUSH);
    if (rc != Z_OK && rc != Z_STREAM_END && rc != Z_BUF_ERROR) {
      const std::string msg = zs.msg ? zs.msg : "?";
      inflateEnd(&zs);
      throw std::runtime_error("inflate failed: " + msg);
    }
    out.append(tmp, sizeof tmp - zs.avail_out);
    if (rc == Z_STREAM_END) {
      if (zs.avail_in == 0) break;  // 多成员 gzip: 还有输入则重置继续
      inflateReset(&zs);
      continue;
    }
    if (rc == Z_BUF_ERROR && zs.avail_in == 0) break;
  }
  inflateEnd(&zs);
  return out;
}

inline std::string DeflateGzip(const std::string &in) {
  z_stream zs;
  std::memset(&zs, 0, sizeof zs);
  // windowBits 15 + 16 ⇒ gzip 头/尾
  if (deflateInit2(&zs, Z_DEFAULT_COMPRESSION, Z_DEFLATED, 15 + 16, 8, Z_DEFAULT_STRATEGY) != Z_OK)
    throw std::runtime_error("deflateInit2 failed");
  zs.next_in = reinterpret_cast<Bytef *>(const_cast<char *>(in.data()));
  zs.avail_in = static_cast<uInt>(in.size());
  std::string out;
  char tmp[65536];
  for (;;) {
    zs.next_out = reinterpret_cast<Bytef *>(tmp);
    zs.avail_out = sizeof tmp;
    const int rc = deflate(&zs, Z_FINISH);
    if (rc != Z_OK && rc != Z_STREAM_END && rc != Z_BUF_ERROR) {
      deflateEnd(&zs);
      throw std::runtime_error("deflate failed");
    }
    out.append(tmp, sizeof tmp - zs.avail_out);
    if (rc == Z_STREAM_END) break;
  }
  deflateEnd(&zs);
  return out;
}

class gzip_decompressor : public filter {
 public:
  std::string process(const std::string &in) override { return InflateAuto(in); }
};

class gzip_compressor : public filter {
 public:
  std::string process(const std::string &in) override { return DeflateGzip(in); }
};

// ---- 设备 ----
class file_source : public source {
 public:
  explicit file_source(const std::string &path, std::ios_base::openmode mode = std::ios_base::in)
      : f_(path, mode | std::ios_base::in | std::ios_base::binary) {}
  bool is_open() const { return f_.is_open(); }
  std::streamsize read(char *s, std::streamsize n) override {
    if (!f_) return -1;
    f_.read(s, n);
    const std::streamsize g = f_.gcount();
    return g > 0 ? g : -1;
  }

 private:
  std::ifstream f_;
};

class array_source : public source {
 public:
  array_source(const char *data, std::streamsize n) : d_(data), n_(n) {}
  std::streamsize read(char *s, std::streamsize n) override {
    const std::streamsize left = n_ - pos_;
    if (left <= 0) return -1;
    const std::streamsize k = left < n ? left : n;
    std::memcpy(s, d_ + pos_, static_cast<size_t>(k));
    pos_ += k;
    return k;
  }

 private:
  const char *d_;
  std::streamsize n_;
  std::streamsize pos_ = 0;
};

class back_inserter : public sink {
 public:
  explicit back_inserter(std::string &out) : out_(&out) {}
  void write(const char *s, std::streamsize n) override { out_->append(s, static_cast<size_t>(n)); }

 private:
  std::string *out_;
};

class file_sink : public sink {
 public:
  explicit file_sink(const std::string &path, std::ios_base::openmode mode = std::ios_base::out)
      : f_(path, mode | std::ios_base::out | std::ios_base::binary) {}
  bool is_open() const { return f_.is_open(); }
  bool ok() const override { return f_.is_open(); }
  void write(const char *s, std::streamsize n) override { f_.write(s, n); }
  void flush() override {
    if (f_.is_open()) {
      f_.flush();
      f_.close();
    }
  }

 private:
  std::ofstream f_;
};

// ---- 过滤输入流 ----
class filtering_istream : public std::istream {
  struct Buf : public std::streambuf {
    std::string data;
    std::size_t pos = 0;
    bool built = false;
    filtering_istream *owner = nullptr;
    int_type underflow() override {
      if (!built) owner->Build();
      if (pos >= data.size()) return traits_type::eof();
      return traits_type::to_int_type(data[pos]);
    }
    int_type uflow() override {
      const int_type c = underflow();
      if (!traits_type::eq_int_type(c, traits_type::eof())) ++pos;
      return c;
    }
    int_type pbackfail(int_type) override {
      if (pos == 0) return traits_type::eof();
      --pos;
      return traits_type::to_int_type(data[pos]);
    }
    std::streamsize xsgetn(char *s, std::streamsize n) override {
      if (!built) owner->Build();
      const std::size_t left = data.size() - pos;
      const std::streamsize k =
          static_cast<std::streamsize>(left < static_cast<std::size_t>(n) ? left : static_cast<std::size_t>(n));
      if (k > 0) std::memcpy(s, data.data() + pos, static_cast<size_t>(k));
      pos += static_cast<std::size_t>(k > 0 ? k : 0);
      return k;
    }
  };

 public:
  filtering_istream() : std::istream(&buf_) { buf_.owner = this; }
  template <class T>
  void push(T t) {
    if constexpr (std::is_base_of_v<source, T>) {
      if constexpr (std::is_base_of_v<file_source, T>) {
        if (!t.is_open()) this->setstate(std::ios_base::failbit);
      }
      src_ = std::make_shared<T>(std::move(t));
      Build();
    } else if constexpr (std::is_base_of_v<filter, T>) {
      filters_.push_back(std::make_shared<T>(std::move(t)));
    } else {
      static_assert(!sizeof(T), "filtering_istream: unsupported component");
    }
  }

 private:
  void Build() {
    if (!src_) {
      this->setstate(std::ios_base::badbit);
      return;
    }
    std::string raw;
    char tmp[65536];
    for (;;) {
      const std::streamsize k = src_->read(tmp, sizeof tmp);
      if (k <= 0) break;
      raw.append(tmp, static_cast<size_t>(k));
    }
    // 数据从后 push 的部件流向前 push 的部件: 源 → 逆 push 序过各过滤器
    for (auto it = filters_.rbegin(); it != filters_.rend(); ++it) {
      try {
        raw = (*it)->process(raw);
      } catch (const std::exception &e) {
        std::fprintf(stderr, "filtering_istream: %s\n", e.what());
        this->setstate(std::ios_base::badbit);
        raw.clear();
      }
    }
    buf_.data = std::move(raw);
    buf_.pos = 0;
    buf_.built = true;
  }
  std::vector<std::shared_ptr<filter>> filters_;
  std::shared_ptr<source> src_;
  Buf buf_;
};

// ---- 过滤输出流 ----
class filtering_ostream : public std::ostream {
  struct Buf : public std::streambuf {
    std::string acc;
    int_type overflow(int_type ch) override {
      if (!traits_type::eq_int_type(ch, traits_type::eof())) acc.push_back(traits_type::to_char_type(ch));
      return ch;
    }
    std::streamsize xsputn(const char *s, std::streamsize n) override {
      acc.append(s, static_cast<size_t>(n));
      return n;
    }
  };

 public:
  filtering_ostream() : std::ostream(&buf_) {}
  filtering_ostream(const filtering_ostream &) = delete;
  filtering_ostream &operator=(const filtering_ostream &) = delete;
  template <class T>
  void push(T t) {
    if constexpr (std::is_base_of_v<sink, T>) {
      if (!t.ok()) this->setstate(std::ios_base::failbit);
      sink_ = std::make_shared<T>(std::move(t));
    } else if constexpr (std::is_base_of_v<filter, T>) {
      filters_.push_back(std::make_shared<T>(std::move(t)));
    } else {
      static_assert(!sizeof(T), "filtering_ostream: unsupported component");
    }
  }
  // 冲刷链路: 累积数据按 push 序过各过滤器, 写入汇。
  void Close() {
    if (closed_) return;
    closed_ = true;
    std::string data = std::move(buf_.acc);
    buf_.acc.clear();
    // 数据从前 push 的部件流向后 push 的部件: 按 push 序过各过滤器
    for (auto &f : filters_) {
      try {
        data = f->process(data);
      } catch (const std::exception &e) {
        std::fprintf(stderr, "filtering_ostream: %s\n", e.what());
        this->setstate(std::ios_base::badbit);
        data.clear();
      }
    }
    if (sink_) {
      sink_->write(data.data(), static_cast<std::streamsize>(data.size()));
      sink_->flush();
    }
  }
  ~filtering_ostream() override { Close(); }

 private:
  std::vector<std::shared_ptr<filter>> filters_;
  std::shared_ptr<sink> sink_;
  bool closed_ = false;
  Buf buf_;
};

inline void close(filtering_ostream &out) { out.Close(); }
inline void close(filtering_istream &) {}

}  // namespace iostreams
}  // namespace boost
