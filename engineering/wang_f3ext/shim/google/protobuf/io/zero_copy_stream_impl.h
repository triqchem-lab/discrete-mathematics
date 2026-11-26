#pragma once
// protobuf io 垫片(手工构建用): IstreamInputStream / OstreamOutputStream 的最小实现。
#include <istream>
#include <iterator>
#include <ostream>
#include <string>
namespace google {
namespace protobuf {
namespace io {
class IstreamInputStream {
 public:
  explicit IstreamInputStream(std::istream *in) : in_(in) {}
  // 整段读入后分块提供
  bool Next(const void **data, int *size) {
    if (!loaded_) {
      buf_.assign(std::istreambuf_iterator<char>(*in_), std::istreambuf_iterator<char>());
      loaded_ = true;
    }
    if (pos_ >= buf_.size()) return false;
    const std::size_t left = buf_.size() - pos_;
    const int k = static_cast<int>(left < (1u << 20) ? left : (1u << 20));
    *data = buf_.data() + pos_;
    *size = k;
    pos_ += static_cast<std::size_t>(k);
    return true;
  }
  void BackUp(int count) { pos_ -= static_cast<std::size_t>(count); }
  bool Skip(int count) {
    pos_ += static_cast<std::size_t>(count);
    return pos_ <= buf_.size();
  }
  std::int64_t ByteCount() const { return static_cast<std::int64_t>(pos_); }

 private:
  std::istream *in_;
  std::string buf_;
  std::size_t pos_ = 0;
  bool loaded_ = false;
};
class OstreamOutputStream {
 public:
  explicit OstreamOutputStream(std::ostream *out) : out_(out) {}
  bool Write(const void *data, int size) {
    out_->write(static_cast<const char *>(data), size);
    return static_cast<bool>(*out_);
  }

 private:
  std::ostream *out_;
};
}  // namespace io
}  // namespace protobuf
}  // namespace google
