#pragma once

// All lookup tables the matrix-multiplication symmetry group needs, for one
// constraint shape ⟨N0, N1⟩, over the prime field 𝔽_P (M = 1, P odd). This is
// the odd-prime companion of f2_matrix_tables.h: same public API (speaking
// FqMatrix instead of F2Matrix), same table ideas, base-P digit packing
// instead of bit packing.
//
// The tables are built once in the constructor using FqMatrix algebra
// (operator*, Inversed) rather than inline digit loops.
//
//   - Gl0()/Gl1()              : GL(N0)/GL(N1) over 𝔽_P, identity first.
//   - Inverse0()/Inverse1()    : matrix inverse (from a table).
//   - Mult011(m01, m11) = m01·m11    : N0 row lookups (m01: N0×N1, m11: N1×N1).
//   - Mult001(m00, m01) = m00·m01    : N0 row lookups (m00: N0×N0, m01: N0×N1).
//   - TransposeConstraint(m01)   : the N0×N1 → N1×N0 transpose (cubic action).
//
// Row lookups: a product's row i is (row i of the left factor)·(right factor),
// so each table maps a 1×N row (index < P^N) through every right factor.

#include <cstdint>
#include <vector>

#include "problems/matrix/fq_matrix.h"

namespace matrix {

template <int P, int N0, int N1> class FqMatrixTables {
  static_assert(N0 >= 1 && N1 >= 1);
  static_assert(N0 <= 4 && N1 <= 4, "GL lookup tables cap N0, N1 ≤ 4");
  static_assert(N0 * N1 <= 16, "constraint must fit in the packed index");

 public:
  using Mat00 = FqMatrix<P, N0, N0>;
  using Mat01 = FqMatrix<P, N0, N1>;
  using Mat11 = FqMatrix<P, N1, N1>;
  using Row0 = FqMatrix<P, 1, N0>;
  using Row1 = FqMatrix<P, 1, N1>;

  static constexpr uint32_t kRows0 = Row0::kCount;  // = P^N0
  static constexpr uint32_t kRows1 = Row1::kCount;  // = P^N1

  FqMatrixTables() {
    gl0_ = EnumerateGL<N0>();
    gl1_ = EnumerateGL<N1>();
    inverse0_ = BuildInverse<N0>();
    inverse1_ = BuildInverse<N1>();

    // v1: 1×N1 row; m11: N1×N1 matrix.
    // v1_x_m11_[m11][v1] = v1·m11
    v1_x_m11_.resize(static_cast<std::size_t>(Mat11::kCount) * kRows1);
    for (uint32_t m11d = 0; m11d < Mat11::kCount; ++m11d) {
      const Mat11 m11(m11d);
      for (uint32_t v1d = 0; v1d < kRows1; ++v1d) {
        const Row1 v1(v1d);
        v1_x_m11_[static_cast<std::size_t>(m11d) * kRows1 + v1d] =
            (v1 * m11).Data();
      }
    }

    // v0: 1×N0 row; m01: N0×N1 matrix.
    // v0_x_m01_[m01][v0] = v0·m01
    v0_x_m01_.resize(static_cast<std::size_t>(Mat01::kCount) * kRows0);
    for (uint32_t m01d = 0; m01d < Mat01::kCount; ++m01d) {
      const Mat01 m01(m01d);
      for (uint32_t v0d = 0; v0d < kRows0; ++v0d) {
        const Row0 v0(v0d);
        v0_x_m01_[static_cast<std::size_t>(m01d) * kRows0 + v0d] =
            (v0 * m01).Data();
      }
    }
  }

  // GL(N) over 𝔽_P, identity first.
  const std::vector<FqMatrix<P, N0, N0>> &Gl0() const { return gl0_; }
  const std::vector<FqMatrix<P, N1, N1>> &Gl1() const { return gl1_; }

  FqMatrix<P, N0, N0> Identity0() const { return Mat00::Identity(); }
  FqMatrix<P, N1, N1> Identity1() const { return Mat11::Identity(); }

  FqMatrix<P, N0, N0> Inverse0(const FqMatrix<P, N0, N0> &m) const {
    return FqMatrix<P, N0, N0>(inverse0_[m.Data()]);
  }
  FqMatrix<P, N1, N1> Inverse1(const FqMatrix<P, N1, N1> &m) const {
    return FqMatrix<P, N1, N1>(inverse1_[m.Data()]);
  }

  // m01·m11: N0 row lookups through the m11 table.
  FqMatrix<P, N0, N1> Mult011(const FqMatrix<P, N0, N1> &m01,
                              const FqMatrix<P, N1, N1> &m11) const {
    FqMatrix<P, N0, N1> out;
    for (int i = 0; i < N0; ++i) {
      uint32_t row = 0;
      for (int j = 0; j < N1; ++j) {
        row += m01.Get(i, j) * FqPowC(P, j);
      }
      const uint32_t prod =
          v1_x_m11_[static_cast<std::size_t>(m11.Data()) * kRows1 + row];
      for (int j = 0; j < N1; ++j) {
        out.Set(i, j, static_cast<uint8_t>((prod / FqPowC(P, j)) % P));
      }
    }
    return out;
  }

  // m00·m01: N0 row lookups through the m01 table.
  FqMatrix<P, N0, N1> Mult001(const FqMatrix<P, N0, N0> &m00,
                              const FqMatrix<P, N0, N1> &m01) const {
    FqMatrix<P, N0, N1> out;
    for (int i = 0; i < N0; ++i) {
      uint32_t row = 0;
      for (int k = 0; k < N0; ++k) {
        row += m00.Get(i, k) * FqPowC(P, k);
      }
      const uint32_t prod =
          v0_x_m01_[static_cast<std::size_t>(m01.Data()) * kRows0 + row];
      for (int j = 0; j < N1; ++j) {
        out.Set(i, j, static_cast<uint8_t>((prod / FqPowC(P, j)) % P));
      }
    }
    return out;
  }

  FqMatrix<P, N1, N0> TransposeConstraint(const FqMatrix<P, N0, N1> &m) const {
    return m.Transposed();
  }

 private:
  template <int n> static std::vector<FqMatrix<P, n, n>> EnumerateGL() {
    std::vector<FqMatrix<P, n, n>> out;
    const FqMatrix<P, n, n> id = FqMatrix<P, n, n>::Identity();
    out.push_back(id);
    for (uint32_t d = 0; d < FqMatrix<P, n, n>::kCount; ++d) {
      const FqMatrix<P, n, n> mm(d);
      if (!(mm == id) && mm.IsInvertible()) {
        out.push_back(mm);
      }
    }
    return out;
  }

  template <int n> static std::vector<uint32_t> BuildInverse() {
    std::vector<uint32_t> inv(FqMatrix<P, n, n>::kCount);
    for (uint32_t d = 0; d < FqMatrix<P, n, n>::kCount; ++d) {
      inv[d] = FqMatrix<P, n, n>(d).Inversed().Data();
    }
    return inv;
  }

  std::vector<FqMatrix<P, N0, N0>> gl0_;
  std::vector<FqMatrix<P, N1, N1>> gl1_;
  std::vector<uint32_t> inverse0_;
  std::vector<uint32_t> inverse1_;
  std::vector<uint32_t> v1_x_m11_;
  std::vector<uint32_t> v0_x_m01_;
};

} // namespace matrix
