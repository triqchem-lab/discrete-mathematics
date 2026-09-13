
## Summary

Constructor injectivity via orthogonal retract decomposition and parallel de Bruijn lifting for Cubical Agda.

### Issues Resolved

**Eliminated `UnsupportedIndexedMatch` warnings (11):**
- Issue1115, Issue1775, Issue3034, Issue4725 — `.warn` files cleared
- Issue5577 — moved from Fail to Succeed
- Issue1408b, Issue3966, Issue4172-2, Issue6492 — `.err` updated (warnings eliminated)
- Issue4769, NewUnifierTooRestrictive — warnings cleared

**Bugs fixed:**
- Fix #8090 — unifyIndices with `Just __IMPOSSIBLE__` deterministic boundary
- Fix CRT thunk evaluation hang
- Fix makeTau telescope expansion
- Fix erased constructor field boundary check

### Code Changes

| File | Change |
|---|---|
| `Substitute.hs` | Guard nullary Con + Lam projections (prevent `__IMPOSSIBLE__` from transpR clause body) |
| `Cubical.hs` | Guard transp dispatch for interval endpoints (i0/i1) |
| `LeftInverse.hs` | `hasConstructorPathFields` guard + `hasErasedConstructorFields` |
| `Unify.hs` + `Datatypes.hs` | `isIntervalCons` guard |

### Test Evidence (30+ files)

- 6 `.warn` files cleared
- 1 Fail→Succeed migration (Issue5577)
- 3 new regression tests (InjectivityWith, InjectivityIndexed, InjectivityPartial)
- 5 `.err` golden updates
- 15 interaction `.out` golden updates

### Known Limitations

- `stdlib-test` OOM on CI 7GB runner — documented capacity boundary, not code regression. Local cabal 2.29GB passes. Stack-built binary on 7GB runner hits memory limit.

