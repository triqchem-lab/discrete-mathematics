#pragma once

// A small, dense matrix over the prime field 𝔽_P (M = 1), packed into one
// integer: the base-P digit at place (i*N1 + j) is the entry at row i, column j
// (row-major; the same layout convention as F2Matrix, whose bit-packing is the
// P = 2 case). Only P^(N0*N1) ≤ 2^32 is supported (one uint32). This is a plain
// value type used to build the symmetry-group lookup tables
// (problems/matrix/fq_matrix_tables.h) and to make the small-matrix algebra
// (transpose, product, inverse) explicit instead of inline digit loops.
//
// This is the odd-prime companion of f2_matrix.h: the matrix problem's
// symmetry group (problems/matrix/symmetry.h) uses F2MatrixTables for P = 2 and
// FqMatrixTables for P = 3, 5, …, so that ⟨N0,N1,N2⟩ matrix multiplication can
// be instantiated over 𝔽₃ (the paper's matrix results are over 𝔽₂; the 𝔽₃
// matrix instantiation is the extension this file enables).

#include <array>
#include <cstdint>
#include <utility>

#include "core/gf.h"

namespace matrix {

// constexpr base^exp for uint32 (no overflow guard: callers are bounded by the
// static_assert on kCount below).
constexpr uint32_t FqPowC(uint32_t base, int exp) {
  uint32_t r = 1;
  for (int i = 0; i < exp; ++i) {
    r *= base;
  }
  return r;
}

template <int P, int N0, int N1 = N0> class FqMatrix {
  static_assert(N0 >= 1 && N1 >= 1);
  static_assert(P >= 2);
  static_assert(FqPowC(P, N0 * N1) <= 0xFFFFFFFFu,
                "FqMatrix must fit in a uint32");

 public:
  using Field = GF<P, 1>;

  static constexpr uint32_t kCells = static_cast<uint32_t>(N0 * N1);
  // Number of N0×N1 matrices over 𝔽_P = P^(N0*N1); Data() ranges below it.
  static constexpr uint32_t kCount = FqPowC(P, N0 * N1);

  FqMatrix() = default;
  explicit constexpr FqMatrix(uint32_t data) : data_(data) {}

  uint32_t Data() const { return data_; }

  // Entry at row i, column j: the base-P digit at place (i*N1 + j).
  uint8_t Get(int i, int j) const {
    return static_cast<uint8_t>((data_ / FqPowC(P, i * N1 + j)) % P);
  }
  void Set(int i, int j, uint8_t digit) {
    const uint32_t place = FqPowC(P, i * N1 + j);
    const uint32_t old = (data_ / place) % P;
    data_ = data_ - old * place + static_cast<uint32_t>(digit) * place;
  }

  static constexpr FqMatrix Identity() {
    static_assert(N0 == N1, "Identity requires a square matrix");
    uint32_t d = 0;
    for (int i = 0; i < N0; ++i) {
      d += FqPowC(P, i * N1 + i);
    }
    return FqMatrix(d);
  }

  FqMatrix<P, N1, N0> Transposed() const {
    FqMatrix<P, N1, N0> out;
    for (int i = 0; i < N0; ++i) {
      for (int j = 0; j < N1; ++j) {
        out.Set(j, i, Get(i, j));
      }
    }
    return out;
  }

  // Standard matrix product (N0×N1)·(N1×N2) = (N0×N2) over 𝔽_P.
  template <int N2>
  FqMatrix<P, N0, N2> operator*(const FqMatrix<P, N1, N2> &m12) const {
    FqMatrix<P, N0, N2> out;
    for (int i = 0; i < N0; ++i) {
      for (int j = 0; j < N2; ++j) {
        Field acc = Field::Zero();
        for (int k = 0; k < N1; ++k) {
          acc = acc + Field(Get(i, k)) * Field(m12.Get(k, j));
        }
        out.Set(i, j, acc.value);
      }
    }
    return out;
  }

 private:
  // Entries as plain digit rows, for the eliminations below.
  using Digits = std::array<std::array<uint8_t, N1>, N0>;

  Digits ToDigits() const {
    Digits rows{};
    for (int i = 0; i < N0; ++i) {
      for (int j = 0; j < N1; ++j) {
        rows[i][j] = Get(i, j);
      }
    }
    return rows;
  }

  // In-place forward elimination on digit rows. Returns the rank; `aug` (N0×NA,
  // may be null) undergoes the same row operations.
  template <int NA>
  static int Eliminate(Digits &rows, std::array<std::array<uint8_t, NA>, N0> *aug) {
    int rank = 0;
    int row = 0;
    int col = 0;
    while (row < N0 && col < N1) {
      int pivot = -1;
      for (int r = row; r < N0; ++r) {
        if (rows[r][col] != 0) {
          pivot = r;
          break;
        }
      }
      if (pivot < 0) {
        ++col;
        continue;
      }
      std::swap(rows[row], rows[pivot]);
      if (aug) {
        std::swap((*aug)[row], (*aug)[pivot]);
      }
      // Normalize the pivot row so the pivot is 1.
      const Field inv = Field::Inverse(Field(rows[row][col]));
      for (int j = 0; j < N1; ++j) {
        rows[row][j] = (inv * Field(rows[row][j])).value;
      }
      if (aug) {
        for (int j = 0; j < NA; ++j) {
          (*aug)[row][j] = (inv * Field((*aug)[row][j])).value;
        }
      }
      // Clear the pivot column from every other row.
      for (int r = 0; r < N0; ++r) {
        if (r != row && rows[r][col] != 0) {
          const Field f(rows[r][col]);
          for (int j = 0; j < N1; ++j) {
            rows[r][j] = (Field(rows[r][j]) - f * Field(rows[row][j])).value;
          }
          if (aug) {
            for (int j = 0; j < NA; ++j) {
              (*aug)[r][j] = (Field((*aug)[r][j]) - f * Field((*aug)[row][j])).value;
            }
          }
        }
      }
      ++rank;
      ++row;
      ++col;
    }
    return rank;
  }

 public:
  // Rank over 𝔽_P via Gaussian elimination on the N0 row-vectors.
  int Rank() const {
    Digits rows = ToDigits();
    return Eliminate<1>(rows, nullptr);
  }

  bool IsInvertible() const {
    static_assert(N0 == N1, "IsInvertible requires a square matrix");
    return Rank() == N0;
  }

  // Gauss-Jordan inverse over 𝔽_P. Returns the zero matrix if singular (a valid
  // inverse is never zero, so 0 is an unambiguous sentinel).
  FqMatrix Inversed() const {
    static_assert(N0 == N1, "Inversed requires a square matrix");
    Digits rows = ToDigits();
    std::array<std::array<uint8_t, N0>, N0> inv{};
    for (int i = 0; i < N0; ++i) {
      inv[i][i] = 1;
    }
    if (Eliminate<N0>(rows, &inv) != N0) {
      return FqMatrix(0);
    }
    // After full elimination rows is the identity permuted by the pivot
    // order; row `row` obtained pivot column `col`, so inv[row] is the inverse
    // row for output row `col`.
    FqMatrix out;
    for (int r = 0; r < N0; ++r) {
      for (int j = 0; j < N0; ++j) {
        // Find which pivot column this row now owns: rows[r] is a unit vector.
        if (rows[r][j] != 0) {
          for (int c = 0; c < N0; ++c) {
            out.Set(j, c, inv[r][c]);
          }
        }
      }
    }
    return out;
  }

  bool operator==(const FqMatrix &other) const { return data_ == other.data_; }
  bool operator<(const FqMatrix &other) const { return data_ < other.data_; }

private:
  uint32_t data_ = 0;
};

} // namespace matrix
