// FqMatrix / FqMatrixTables / F₃ matrix symmetry group tests (odd prime field
// path of problems/matrix). Mirrors f2_matrix_test.cc / symmetry_test.cc.
#include "gtest/gtest.h"

#include "core/symmetry.h"
#include "problems/matrix/fq_matrix.h"
#include "problems/matrix/fq_matrix_tables.h"
#include "problems/matrix/problem.h"

namespace {

using Mat3 = matrix::FqMatrix<3, 3, 3>;
using Mat2 = matrix::FqMatrix<3, 2, 2>;

TEST(FqMatrixTest, GroupOrdersMatchFormula) {
  // |GL(2,3)| = (9-1)(9-3) = 48;  |GL(3,3)| = (27-1)(27-3)(27-9) = 11232.
  int gl2 = 0;
  for (uint32_t d = 0; d < Mat2::kCount; ++d) {
    gl2 += Mat2(d).IsInvertible();
  }
  int gl3 = 0;
  for (uint32_t d = 0; d < Mat3::kCount; ++d) {
    gl3 += Mat3(d).IsInvertible();
  }
  EXPECT_EQ(gl2, 48);
  EXPECT_EQ(gl3, 11232);
  EXPECT_EQ(Mat3::kCount, 19683);
}

TEST(FqMatrixTest, EveryInvertibleMatrixInverts) {
  for (uint32_t d = 0; d < Mat3::kCount; ++d) {
    Mat3 m(d);
    if (!m.IsInvertible()) {
      EXPECT_EQ(m.Inversed().Data(), 0u);  // singular → zero sentinel
      continue;
    }
    EXPECT_EQ(m * m.Inversed(), Mat3::Identity());
    EXPECT_EQ(m.Inversed() * m, Mat3::Identity());
  }
}

TEST(FqMatrixTest, TransposeAndEntryAccessors) {
  for (uint32_t d = 0; d < Mat3::kCount; d += 3) {
    Mat3 m(d);
    EXPECT_EQ(m.Transposed().Transposed(), m);
    Mat3 copy;
    for (int i = 0; i < 3; ++i) {
      for (int j = 0; j < 3; ++j) {
        copy.Set(i, j, m.Get(i, j));
      }
    }
    EXPECT_EQ(copy, m);
  }
  // Get/Set address the base-3 digit at place (i*N1 + j).
  Mat3 e;
  e.Set(1, 2, 2);
  EXPECT_EQ(e.Data(), 2u * 9u);
  EXPECT_EQ(e.Get(1, 2), 2);
  EXPECT_EQ(e.Get(0, 0), 0);
}

TEST(FqMatrixTablesTest, TablesAgreeWithDirectProducts) {
  matrix::FqMatrixTables<3, 3, 3> tables;
  EXPECT_EQ(tables.Gl0().size(), 11232u);
  EXPECT_EQ(tables.Gl1().size(), 11232u);
  EXPECT_EQ(tables.Gl0().front(), Mat3::Identity());
  for (const Mat3 &m11 : tables.Gl1()) {
    for (uint32_t d = 0; d < Mat3::kCount; d += 7) {
      Mat3 m01(d);
      EXPECT_EQ(tables.Mult011(m01, m11), m01 * m11);
      EXPECT_EQ(tables.Mult001(m01, m11), m01 * m11);
    }
  }
  for (const Mat3 &m : tables.Gl0()) {
    EXPECT_EQ(tables.Inverse0(m), m.Inversed());
  }
}

using P3 = matrix::Problem<3, 1, 3, 3, 3>;
using G3 = typename P3::SymmetryGroup;
static_assert(SymmetryGroupConcept<G3>);

TEST(F3SymmetryGroupTest, SizesAndConcept) {
  G3 g;
  // Query = GL(3,3) × {id, transpose} = 2·11232;  Store = GL(3,3).
  EXPECT_EQ(g.query.Size(), 2 * 11232);
  EXPECT_EQ(g.store.Size(), 11232);
  EXPECT_TRUE(g.query.Contains(g.query.Identity()));
  EXPECT_TRUE(g.store.Contains(g.store.Identity()));
  EXPECT_FALSE(g.query.Contains(typename G3::QuerySet::Elem{0, 0}));
  EXPECT_FALSE(g.store.Contains(0));
  EXPECT_EQ(P3::Name(), "matrix_q03_n333");
}

TEST(F3SymmetryGroupTest, ActionsAreInvertibleOnConstraints) {
  G3 g;
  for (int vstep = 1; vstep < 300; vstep += 29) {
    G3::Vec v;
    uint32_t x = static_cast<uint32_t>(vstep);
    for (int k = 0; k < P3::kNA; ++k) {
      v.Set(k, matrix::FqMatrix<3, 3, 3>::Field(static_cast<uint8_t>(x % 3)));
      x /= 3;
    }
    for (int qi = 0; qi < g.query.Size(); qi += 997) {
      auto e = g.query.At(qi);
      EXPECT_EQ(g.query.ApplyInverse(e, g.query.Apply(e, v)), v);
    }
    for (int si = 0; si < g.store.Size(); si += 991) {
      auto r = g.store.At(si);
      EXPECT_EQ(g.store.ApplyInverse(r, g.store.Apply(r, v)), v);
    }
  }
}

TEST(F3SymmetryGroupTest, WitnessPackingRoundTrips) {
  G3 g;
  for (int qi = 0; qi < g.query.Size(); qi += 13) {
    auto e = g.query.At(qi);
    const uint32_t packed = static_cast<uint32_t>(e);
    EXPECT_EQ(static_cast<uint32_t>(typename G3::QuerySet::Elem(packed)), packed);
  }
  for (int si = 0; si < g.store.Size(); si += 13) {
    EXPECT_EQ(static_cast<uint32_t>(g.store.At(si)), g.store.At(si));
  }
}

TEST(F3SymmetryGroupTest, TensorHas27Units) {
  auto T = P3::MakeTensor();
  int nz = 0;
  for (int i = 0; i < P3::kNA; ++i) {
    for (int j = 0; j < P3::kNB; ++j) {
      for (int k = 0; k < P3::kNC; ++k) {
        nz += (T[i][j][k] != matrix::FqMatrix<3, 3, 3>::Field::Zero());
      }
    }
  }
  EXPECT_EQ(nz, 27);
}

}  // namespace
