// F₃ 矩阵问题实例化的独立检查(clang++ 直编)。
// F₂ 回归 + F₃: SymmetryGroupConcept、群作用可逆性、见证编码往返、张量形状。
#include <cassert>
#include <cstdio>
#include "core/symmetry.h"
#include "problems/matrix/problem.h"

using P2 = matrix::Problem<2, 1, 3, 3, 3>;
using P3 = matrix::Problem<3, 1, 3, 3, 3>;
static_assert(SymmetryGroupConcept<typename P2::SymmetryGroup>);
static_assert(SymmetryGroupConcept<typename P3::SymmetryGroup>);

template <class Pr> int Check(const char *tag) {
  using G = typename Pr::SymmetryGroup;
  using Vec = typename G::Vec;
  G g;
  std::printf("[%s] %s: query.Size=%d store.Size=%d NA=%d\n", tag, Pr::Name().c_str(),
              g.query.Size(), g.store.Size(), Pr::kNA);
  auto T = Pr::MakeTensor();
  int nz = 0;
  for (int i = 0; i < Pr::kNA; ++i)
    for (int j = 0; j < Pr::kNB; ++j)
      for (int k = 0; k < Pr::kNC; ++k) nz += (T[i][j][k] != GF<Pr::kP, 1>::Zero());
  assert(nz == 27);
  // 群作用可逆: 对若干约束向量 v 与群元素 e/r
  long checked = 0;
  for (int vstep = 1; vstep < 200; vstep += 19) {
    Vec v;
    uint32_t x = static_cast<uint32_t>(vstep);
    for (int k = 0; k < Pr::kNA; ++k) {
      v.Set(k, GF<Pr::kP, 1>(static_cast<uint8_t>(x % static_cast<uint32_t>(Pr::kQ))));
      x /= static_cast<uint32_t>(Pr::kQ);
    }
    for (int qi = 0; qi < g.query.Size(); qi += 997) {
      auto e = g.query.At(qi);
      assert(g.query.Contains(e));
      assert(g.query.ApplyInverse(e, g.query.Apply(e, v)) == v);
      // 见证编码往返(CanonicalFromWitness 的 uint32 往返)
      assert(static_cast<uint32_t>(static_cast<typename G::QuerySet::Elem>(
                 static_cast<uint32_t>(e))) == static_cast<uint32_t>(e));
      ++checked;
    }
    for (int si = 0; si < g.store.Size(); si += 991) {
      auto r = g.store.At(si);
      assert(g.store.Contains(r));
      assert(g.store.ApplyInverse(r, g.store.Apply(r, v)) == v);
      ++checked;
    }
  }
  std::printf("[%s] group inverse round-trips ok: %ld\n", tag, checked);
  return 0;
}

int main() {
  Check<P2>("F2");
  Check<P3>("F3");
  return 0;
}
