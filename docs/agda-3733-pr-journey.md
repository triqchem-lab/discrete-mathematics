# Agda #3733: Cubical Constructor Injectivity — PR 技术攻关全记录

> **PR**: https://github.com/agda/agda/pull/8611
> **分支**: `fix/cubical-injectivity-retract`
> **日期**: 2026-07-06 → 2026-07-11 (5天)
> **commits**: 102
> **CI**: 33/33 green + 1 SKIPPED

## 根因

`compareAtom` 逐字比较 QName。cubical 理论下 `_≡_` (EQUALITY) 和 `PathP` (PATH) 语义等价但 QName 不同，导致 heads 不等时跳过参数比较，误判 injectivity。

## 解决 issues

| 类型 | # | 说明 |
|------|---|------|
| Bug | #3733 | cubical constructor injectivity（部分修复） |
| Bug | #8090 | unifyIndices 边界修复 |
| Bug | #8619 | haskell-actions/setup CI bug |
| CI | — | ghcup 0.1.50.2→0.2.6.2（stack 3.9.3 可下载） |
| CI | — | GHCRTS=-M6G 默认（Makefile + CI workflow） |
| Test | 3 | InjectivityPartial/Indexed/With |
| Test | Issue5577 | Fail→Succeed |
| Test | 11 | golden 值更新 |

## 语义收敛路线

```
初始方案（300+ 行）:
  ├─ Builtin.hs stLocalBuiltins     ❌ 崩溃 (NoBindingForBuiltin)
  ├─ primEqualityName               ❌ 抛异常
  ├─ defName 穿透 re-export        ❌ 过度解析
  ├─ path-unify 5 注入点            ❌ UnsolvedMetaVariables
  └─ canonicalEqName 1 注入点       ✅ 收敛
```

## 核心修复

```haskell
canonicalEqName :: QName -> TCM QName
canonicalEqName q = do
  eq <- getBuiltinName' builtinEquality  -- 非抛异常
  case eq of
    Nothing -> return q
    Just eqName ->
      if q /= eqName then return q else do
        p <- getBuiltinName' builtinPathP
        case p of
          Just pn -> return pn
          Nothing -> return q
```

## 关键教训

1. **`make test` 不依赖 `make install-bin`** → stale binary 假阳性
2. **`.agdai` 缓存掩盖 bug** → `rm -rf cubical/_build` 强制重编
3. **GHCRTS 用 `$(origin)` 判断** → `?=` 不检查环境变量
4. **容器内接受 golden 值** → 宿主机路径污染
