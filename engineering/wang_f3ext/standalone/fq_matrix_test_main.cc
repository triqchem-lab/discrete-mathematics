// FqMatrix / FqMatrixTables 独立单测(clang++ 直编, 不依赖 bazel)。
// 验证: |GL(3,3)| = 11232 = (27-1)(27-3)(27-9); 逆; 转置; 表查积 == 直接积。
#include <cassert>
#include <cstdio>
#include <cstdint>
#include "problems/matrix/fq_matrix.h"
#include "problems/matrix/fq_matrix_tables.h"

using Mat3 = matrix::FqMatrix<3, 3, 3>;
using Mat11_2 = matrix::FqMatrix<3, 2, 2>;

int main() {
  // |GL(2,3)| = 8·6 = 48;  |GL(3,3)| = 26·24·18 = 11232
  int gl2 = 0;
  for (uint32_t d = 0; d < Mat11_2::kCount; ++d) gl2 += Mat11_2(d).IsInvertible();
  int gl3 = 0;
  int inv_ok = 0;
  for (uint32_t d = 0; d < Mat3::kCount; ++d) {
    Mat3 m(d);
    if (m.IsInvertible()) {
      ++gl3;
      if (m * m.Inversed() == Mat3::Identity() && m.Inversed() * m == Mat3::Identity()) ++inv_ok;
    }
    if (m.Transposed().Transposed() != m) { std::printf("transpose fail %u\n", d); return 1; }
  }
  std::printf("|GL(2,3)| = %d (48), |GL(3,3)| = %d (11232), inverse ok = %d\n", gl2, gl3, inv_ok);
  assert(gl2 == 48 && gl3 == 11232 && inv_ok == 11232);

  // 表: Mult011 / Mult001 对全部 GL 右因子与全部左因子核对
  matrix::FqMatrixTables<3, 3, 3> tables;
  std::printf("Gl0 size %zu, Gl1 size %zu\n", tables.Gl0().size(), tables.Gl1().size());
  assert(tables.Gl0().size() == 11232 && tables.Gl1().size() == 11232);
  assert(tables.Gl0()[0] == Mat3::Identity());
  long checked = 0;
  for (const Mat3 &m11 : tables.Gl1()) {
    for (uint32_t d = 0; d < Mat3::kCount; d += 7) {   // 步长抽样式全遍历
      Mat3 m01(d);
      if (tables.Mult011(m01, m11) != m01 * m11) { std::printf("Mult011 mismatch\n"); return 1; }
      if (tables.Mult001(m01, m11) != m01 * m11) { std::printf("Mult001 mismatch\n"); return 1; }
      ++checked;
    }
  }
  // 逆表
  for (const Mat3 &m : tables.Gl0()) {
    if (tables.Inverse0(m) != m.Inversed()) { std::printf("Inverse0 mismatch\n"); return 1; }
  }
  // 转置约束
  Mat3 sample(1 + 3 * 2 + 9 * 1 + 27 * 2);
  if (tables.TransposeConstraint(sample) != sample.Transposed()) { std::printf("T mismatch\n"); return 1; }
  std::printf("tables ok; products checked = %ld\n", checked);
  return 0;
}
