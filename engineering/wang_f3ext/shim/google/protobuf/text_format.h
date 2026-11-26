#pragma once
// protobuf TextFormat 垫片(手工构建用): Parse(istream 流 → 消息) / Print(消息 → ostream 流)。
#include <string>
#include "core/certificate.pb.h"
#include "google/protobuf/io/zero_copy_stream_impl.h"
namespace google {
namespace protobuf {
class TextFormat {
 public:
  template <class Msg>
  static bool Parse(io::IstreamInputStream *in, Msg *msg) {
    std::string text;
    const void *data;
    int size;
    while (in->Next(&data, &size)) text.append(static_cast<const char *>(data), static_cast<std::size_t>(size));
    std::string err;
    if (!msg->ParseTextFromString(text, &err)) {
      std::fprintf(stderr, "TextFormat::Parse: %s\n", err.c_str());
      return false;
    }
    return true;
  }
  template <class Msg>
  static bool Print(const Msg &msg, io::OstreamOutputStream *out) {
    const std::string text = msg.TextDebugString();
    return out->Write(text.data(), static_cast<int>(text.size()));
  }
};
}  // namespace protobuf
}  // namespace google
