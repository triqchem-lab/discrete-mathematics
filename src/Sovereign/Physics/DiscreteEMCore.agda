{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteEMCore
-- 78 电磁学 — 离散 Maxwell 核心定理层 (0 postulate, 无洞)
--
-- 定位: 建立在 DiscreteEMField (3×3 环面, 第一基石) 与 DiscreteEMField3D
-- ((Fin 3)³ 环面, 第二基石) 之上的"核心定理层"。GF(3) 域律、三对混合
-- 偏导交换性、差分可加性/负号引理均已在两基石中穷举/符号证明, 本模块
-- 直接复用 (open import), 不重复展开。
--
-- 本模块新增三个可证核心:
--   §1 div (curl A) ≡ 0 —— 旋度的散度为零 (全形式!)
--      补完 DiscreteEMField3D §6 的诚实边界: 此前只证到"成对形式"
--      div-curl-zero-paired; 展开链 (dx/dy/dz-add + dx/dy/dz-neg) 与
--      六项重排未收尾。本模块给出完整展开 + six-rotate 重排, 全程符号证明。
--   §2 curl (A + grad φ) ≡ curl A —— 3D 规范不变性
--      旋度线性 curl-linear (三分量, shuffle22 重排) + curl-grad-zero
--      + 零元引理; 2D 版本在 DiscreteEMField, 3D 版本在此 (允许重复)。
--   §3 零场零通量 —— Chern 链接的可证部分
--      通量 = 环绕平面 k = 0 的 9 个面上 B 的 z 分量有限求和 (具体表,
--      非 postulate); 磁单极非平凡构型 (通量 = 陈数 ±2) 需要非平凡
--      U(1) 主丛, 对接 DiscreteKTheory — 诚实边界以注释给出, 不写虚假证明。
--
-- 关键重排引理 shuffle22 / pair-swap / six-rotate 均为 GF(3) 加法的
-- 交换律 + 结合律符号链 (0 postulate), 与第二基石的 shuffle23 同族。
--
-- 后续路线: 离散 Faraday/Ampère 定律 (Fin n 时间步进) + 电荷守恒
-- (∂ρ/∂t + div J = 0 相容性), 依赖本模块的 div-curl-zero 作为
-- Maxwell 方程组的可积性条件。

module Sovereign.Physics.DiscreteEMCore where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

-- 复用第二基石的场运算与已证引理:
--   GF3, Point3D, add3, neg3, add3-comm/assoc/identity/inverse,
--   neg3-involutive, neg3-add, next, ScalarField, VectorField,
--   dx, dy, dz, dy-dx-comm, dz-dx-comm, dz-dy-comm,
--   dx-neg, dy-neg, dz-neg, dx-add, dy-add, dz-add,
--   grad, vx, vy, vz, div, curl, curl-grad-zero,
--   pair-cancel-1/2/3, div-curl-zero-paired, shuffle23
open import Sovereign.Physics.DiscreteEMField3D

------------------------------------------------------------------------------
-- §0a. 向量加法与零元
------------------------------------------------------------------------------

-- 分量投影实现 (不模式匹配三元组): 使 vz (λ q → addVec3 (A q) (B q))
-- 对任意场 A B 定义等价于 λ q → add3 (vz A q) (vz B q), 供 curl-linear 归约
-- (与第二基石 vx/vy/vz 投影同款技术: VectorField 是函数, 不能模式匹配)。
addVec3 : GF3 × GF3 × GF3 → GF3 × GF3 × GF3 → GF3 × GF3 × GF3
addVec3 u v = add3 (proj₁ u) (proj₁ v)
            , add3 (proj₁ (proj₂ u)) (proj₁ (proj₂ v))
            , add3 (proj₂ (proj₂ u)) (proj₂ (proj₂ v))

addVec3-right-unit : ∀ v → addVec3 v (fz , fz , fz) ≡ v
addVec3-right-unit v =
  cong₂ _,_ (add3-identity (proj₁ v))
    (cong₂ _,_ (add3-identity (proj₁ (proj₂ v))) (add3-identity (proj₂ (proj₂ v))))

------------------------------------------------------------------------------
-- §0b. 重排引理 (GF(3) 交换+结合律的符号链, 0 postulate)
--   三个引理覆盖 div-curl-zero 与 curl-linear 所需的全部六项/四项重排。
------------------------------------------------------------------------------

-- (x+y)+(z+w) ≡ (x+z)+(y+w) —— 四元素换位 (6 步)
shuffle22 : ∀ x y z w → add3 (add3 x y) (add3 z w) ≡ add3 (add3 x z) (add3 y w)
shuffle22 x y z w = begin
  add3 (add3 x y) (add3 z w)
    ≡⟨ sym (add3-assoc (add3 x y) z w) ⟩
  add3 (add3 (add3 x y) z) w
    ≡⟨ cong (λ t → add3 t w) (add3-assoc x y z) ⟩
  add3 (add3 x (add3 y z)) w
    ≡⟨ cong (λ t → add3 t w) (cong (add3 x) (add3-comm y z)) ⟩
  add3 (add3 x (add3 z y)) w
    ≡⟨ cong (λ t → add3 t w) (sym (add3-assoc x z y)) ⟩
  add3 (add3 (add3 x z) y) w
    ≡⟨ add3-assoc (add3 x z) y w ⟩
  add3 (add3 x z) (add3 y w) ∎

-- (x+y)+(z+w) ≡ (x+w)+(z+y) —— 四元素 2↔4 换位 (12 步)
pair-swap : ∀ x y z w → add3 (add3 x y) (add3 z w) ≡ add3 (add3 x w) (add3 z y)
pair-swap x y z w = begin
  add3 (add3 x y) (add3 z w)
    ≡⟨ sym (add3-assoc (add3 x y) z w) ⟩
  add3 (add3 (add3 x y) z) w
    ≡⟨ cong (λ t → add3 t w) (add3-assoc x y z) ⟩
  add3 (add3 x (add3 y z)) w
    ≡⟨ cong (λ t → add3 t w) (cong (add3 x) (add3-comm y z)) ⟩
  add3 (add3 x (add3 z y)) w
    ≡⟨ cong (λ t → add3 t w) (sym (add3-assoc x z y)) ⟩
  add3 (add3 (add3 x z) y) w
    ≡⟨ add3-assoc (add3 x z) y w ⟩
  add3 (add3 x z) (add3 y w)
    ≡⟨ cong (add3 (add3 x z)) (add3-comm y w) ⟩
  add3 (add3 x z) (add3 w y)
    ≡⟨ sym (add3-assoc (add3 x z) w y) ⟩
  add3 (add3 (add3 x z) w) y
    ≡⟨ cong (λ t → add3 t y) (add3-assoc x z w) ⟩
  add3 (add3 x (add3 z w)) y
    ≡⟨ cong (λ t → add3 t y) (cong (add3 x) (add3-comm z w)) ⟩
  add3 (add3 x (add3 w z)) y
    ≡⟨ cong (λ t → add3 t y) (sym (add3-assoc x w z)) ⟩
  add3 (add3 (add3 x w) z) y
    ≡⟨ add3-assoc (add3 x w) z y ⟩
  add3 (add3 x w) (add3 z y) ∎

-- 六元素换位: (a+b)+((c+d)+(e+f)) ≡ (a+d)+((c+f)+(e+b))
-- div-curl-zero 的关键重排: 把展开六项从 (ab)(cd)(ef) 配对
-- 重排为 (ad)(cf)(eb) 配对, 使 pair-cancel-1/2/3 直接可用 (11 步)。
six-rotate : ∀ a b c d e f →
  add3 (add3 a b) (add3 (add3 c d) (add3 e f))
    ≡ add3 (add3 a d) (add3 (add3 c f) (add3 e b))
six-rotate a b c d e f = begin
  add3 (add3 a b) (add3 (add3 c d) (add3 e f))
    ≡⟨ cong (add3 (add3 a b)) (pair-swap c d e f) ⟩
  add3 (add3 a b) (add3 (add3 c f) (add3 e d))
    ≡⟨ sym (add3-assoc (add3 a b) (add3 c f) (add3 e d)) ⟩
  add3 (add3 (add3 a b) (add3 c f)) (add3 e d)
    ≡⟨ pair-swap (add3 a b) (add3 c f) e d ⟩
  add3 (add3 (add3 a b) d) (add3 e (add3 c f))
    ≡⟨ cong (λ t → add3 t (add3 e (add3 c f))) (add3-assoc a b d) ⟩
  add3 (add3 a (add3 b d)) (add3 e (add3 c f))
    ≡⟨ cong (λ t → add3 t (add3 e (add3 c f))) (cong (add3 a) (add3-comm b d)) ⟩
  add3 (add3 a (add3 d b)) (add3 e (add3 c f))
    ≡⟨ cong (λ t → add3 t (add3 e (add3 c f))) (sym (add3-assoc a d b)) ⟩
  add3 (add3 (add3 a d) b) (add3 e (add3 c f))
    ≡⟨ add3-assoc (add3 a d) b (add3 e (add3 c f)) ⟩
  add3 (add3 a d) (add3 b (add3 e (add3 c f)))
    ≡⟨ cong (add3 (add3 a d)) (sym (add3-assoc b e (add3 c f))) ⟩
  add3 (add3 a d) (add3 (add3 b e) (add3 c f))
    ≡⟨ cong (add3 (add3 a d)) (cong (λ t → add3 t (add3 c f)) (add3-comm b e)) ⟩
  add3 (add3 a d) (add3 (add3 e b) (add3 c f))
    ≡⟨ cong (add3 (add3 a d)) (add3-comm (add3 e b) (add3 c f)) ⟩
  add3 (add3 a d) (add3 (add3 c f) (add3 e b)) ∎

------------------------------------------------------------------------------
-- §0c. 混合偏导交换性 (草稿方向的封装, 一行转置自第二基石)
------------------------------------------------------------------------------

dx-dy-comm : ∀ φ p → dx (dy φ) p ≡ dy (dx φ) p
dx-dy-comm φ p = sym (dy-dx-comm φ p)

dy-dz-comm : ∀ φ p → dy (dz φ) p ≡ dz (dy φ) p
dy-dz-comm φ p = sym (dz-dy-comm φ p)

dx-dz-comm : ∀ φ p → dx (dz φ) p ≡ dz (dx φ) p
dx-dz-comm φ p = sym (dz-dx-comm φ p)

------------------------------------------------------------------------------
-- §1. 核心恒等式 1: div (curl A) ≡ 0 (全形式)
--   div (curl A)
--   = dx(dy Az − dz Ay) + dy(dz Ax − dx Az) + dz(dx Ay − dy Ax)
--   展开后六个二阶差分项按混合偏导交换性两两抵消;
--   six-rotate 将六项重排到 pair-cancel-1/2/3 的成对形式。
------------------------------------------------------------------------------

div-curl-zero : ∀ A p → div (curl A) p ≡ fz
div-curl-zero A (i , j , k) = begin
  div (curl A) (i , j , k)
    ≡⟨ refl ⟩
  add3 (dx (λ q → add3 (dy (vz A) q) (neg3 (dz (vy A) q))) (i , j , k))
       (add3 (dy (λ q → add3 (dz (vx A) q) (neg3 (dx (vz A) q))) (i , j , k))
             (dz (λ q → add3 (dx (vy A) q) (neg3 (dy (vx A) q))) (i , j , k)))
    ≡⟨ cong₂ add3
         (dx-add (dy (vz A)) (λ q → neg3 (dz (vy A) q)) (i , j , k))
         (cong₂ add3
           (dy-add (dz (vx A)) (λ q → neg3 (dx (vz A) q)) (i , j , k))
           (dz-add (dx (vy A)) (λ q → neg3 (dy (vx A) q)) (i , j , k))) ⟩
  add3 (add3 (dx (dy (vz A)) (i , j , k)) (dx (λ q → neg3 (dz (vy A) q)) (i , j , k)))
       (add3 (add3 (dy (dz (vx A)) (i , j , k)) (dy (λ q → neg3 (dx (vz A) q)) (i , j , k)))
             (add3 (dz (dx (vy A)) (i , j , k)) (dz (λ q → neg3 (dy (vx A) q)) (i , j , k))))
    ≡⟨ cong₂ add3
         (cong (λ t → add3 (dx (dy (vz A)) (i , j , k)) t) (dx-neg (dz (vy A)) (i , j , k)))
         (cong₂ add3
           (cong (λ t → add3 (dy (dz (vx A)) (i , j , k)) t) (dy-neg (dx (vz A)) (i , j , k)))
           (cong (λ t → add3 (dz (dx (vy A)) (i , j , k)) t) (dz-neg (dy (vx A)) (i , j , k)))) ⟩
  add3 (add3 (dx (dy (vz A)) (i , j , k)) (neg3 (dx (dz (vy A)) (i , j , k))))
       (add3 (add3 (dy (dz (vx A)) (i , j , k)) (neg3 (dy (dx (vz A)) (i , j , k))))
             (add3 (dz (dx (vy A)) (i , j , k)) (neg3 (dz (dy (vx A)) (i , j , k)))))
    ≡⟨ six-rotate (dx (dy (vz A)) (i , j , k)) (neg3 (dx (dz (vy A)) (i , j , k)))
                  (dy (dz (vx A)) (i , j , k)) (neg3 (dy (dx (vz A)) (i , j , k)))
                  (dz (dx (vy A)) (i , j , k)) (neg3 (dz (dy (vx A)) (i , j , k))) ⟩
  add3 (add3 (dx (dy (vz A)) (i , j , k)) (neg3 (dy (dx (vz A)) (i , j , k))))
       (add3 (add3 (dy (dz (vx A)) (i , j , k)) (neg3 (dz (dy (vx A)) (i , j , k))))
             (add3 (dz (dx (vy A)) (i , j , k)) (neg3 (dx (dz (vy A)) (i , j , k)))))
    ≡⟨ cong₂ add3
         (pair-cancel-1 (vz A) (i , j , k))
         (cong₂ add3 (pair-cancel-2 (vx A) (i , j , k)) (pair-cancel-3 (vy A) (i , j , k))) ⟩
  add3 fz (add3 fz fz)
    ≡⟨ refl ⟩
  fz ∎

------------------------------------------------------------------------------
-- §2. 核心恒等式 2: 3D 规范不变性 curl (A + grad φ) ≡ curl A
--   先证旋度线性 (三分量, 差分可加性 + neg3-add + shuffle22),
--   再组合 curl-grad-zero 与零元引理。
------------------------------------------------------------------------------

curl-linear-x : ∀ A B p →
  add3 (dy (λ q → add3 (vz A q) (vz B q)) p)
       (neg3 (dz (λ q → add3 (vy A q) (vy B q)) p))
    ≡ add3 (add3 (dy (vz A) p) (neg3 (dz (vy A) p)))
           (add3 (dy (vz B) p) (neg3 (dz (vy B) p)))
curl-linear-x A B p = begin
  add3 (dy (λ q → add3 (vz A q) (vz B q)) p)
       (neg3 (dz (λ q → add3 (vy A q) (vy B q)) p))
    ≡⟨ cong (λ t → add3 t (neg3 (dz (λ q → add3 (vy A q) (vy B q)) p)))
            (dy-add (vz A) (vz B) p) ⟩
  add3 (add3 (dy (vz A) p) (dy (vz B) p))
       (neg3 (dz (λ q → add3 (vy A q) (vy B q)) p))
    ≡⟨ cong (add3 (add3 (dy (vz A) p) (dy (vz B) p)))
            (trans (cong neg3 (dz-add (vy A) (vy B) p))
                   (neg3-add (dz (vy A) p) (dz (vy B) p))) ⟩
  add3 (add3 (dy (vz A) p) (dy (vz B) p))
       (add3 (neg3 (dz (vy A) p)) (neg3 (dz (vy B) p)))
    ≡⟨ shuffle22 (dy (vz A) p) (dy (vz B) p)
                 (neg3 (dz (vy A) p)) (neg3 (dz (vy B) p)) ⟩
  add3 (add3 (dy (vz A) p) (neg3 (dz (vy A) p)))
       (add3 (dy (vz B) p) (neg3 (dz (vy B) p))) ∎

curl-linear-y : ∀ A B p →
  add3 (dz (λ q → add3 (vx A q) (vx B q)) p)
       (neg3 (dx (λ q → add3 (vz A q) (vz B q)) p))
    ≡ add3 (add3 (dz (vx A) p) (neg3 (dx (vz A) p)))
           (add3 (dz (vx B) p) (neg3 (dx (vz B) p)))
curl-linear-y A B p = begin
  add3 (dz (λ q → add3 (vx A q) (vx B q)) p)
       (neg3 (dx (λ q → add3 (vz A q) (vz B q)) p))
    ≡⟨ cong (λ t → add3 t (neg3 (dx (λ q → add3 (vz A q) (vz B q)) p)))
            (dz-add (vx A) (vx B) p) ⟩
  add3 (add3 (dz (vx A) p) (dz (vx B) p))
       (neg3 (dx (λ q → add3 (vz A q) (vz B q)) p))
    ≡⟨ cong (add3 (add3 (dz (vx A) p) (dz (vx B) p)))
            (trans (cong neg3 (dx-add (vz A) (vz B) p))
                   (neg3-add (dx (vz A) p) (dx (vz B) p))) ⟩
  add3 (add3 (dz (vx A) p) (dz (vx B) p))
       (add3 (neg3 (dx (vz A) p)) (neg3 (dx (vz B) p)))
    ≡⟨ shuffle22 (dz (vx A) p) (dz (vx B) p)
                 (neg3 (dx (vz A) p)) (neg3 (dx (vz B) p)) ⟩
  add3 (add3 (dz (vx A) p) (neg3 (dx (vz A) p)))
       (add3 (dz (vx B) p) (neg3 (dx (vz B) p))) ∎

curl-linear-z : ∀ A B p →
  add3 (dx (λ q → add3 (vy A q) (vy B q)) p)
       (neg3 (dy (λ q → add3 (vx A q) (vx B q)) p))
    ≡ add3 (add3 (dx (vy A) p) (neg3 (dy (vx A) p)))
           (add3 (dx (vy B) p) (neg3 (dy (vx B) p)))
curl-linear-z A B p = begin
  add3 (dx (λ q → add3 (vy A q) (vy B q)) p)
       (neg3 (dy (λ q → add3 (vx A q) (vx B q)) p))
    ≡⟨ cong (λ t → add3 t (neg3 (dy (λ q → add3 (vx A q) (vx B q)) p)))
            (dx-add (vy A) (vy B) p) ⟩
  add3 (add3 (dx (vy A) p) (dx (vy B) p))
       (neg3 (dy (λ q → add3 (vx A q) (vx B q)) p))
    ≡⟨ cong (add3 (add3 (dx (vy A) p) (dx (vy B) p)))
            (trans (cong neg3 (dy-add (vx A) (vx B) p))
                   (neg3-add (dy (vx A) p) (dy (vx B) p))) ⟩
  add3 (add3 (dx (vy A) p) (dx (vy B) p))
       (add3 (neg3 (dy (vx A) p)) (neg3 (dy (vx B) p)))
    ≡⟨ shuffle22 (dx (vy A) p) (dx (vy B) p)
                 (neg3 (dy (vx A) p)) (neg3 (dy (vx B) p)) ⟩
  add3 (add3 (dx (vy A) p) (neg3 (dy (vx A) p)))
       (add3 (dx (vy B) p) (neg3 (dy (vx B) p))) ∎

-- 旋度线性: curl (A + B) ≡ curl A + curl B (三分量合成)
curl-linear : ∀ A B p →
  curl (λ q → addVec3 (A q) (B q)) p ≡ addVec3 (curl A p) (curl B p)
curl-linear A B p = begin
  curl (λ q → addVec3 (A q) (B q)) p
    ≡⟨ refl ⟩
  add3 (dy (λ q → add3 (vz A q) (vz B q)) p)
       (neg3 (dz (λ q → add3 (vy A q) (vy B q)) p))
  , add3 (dz (λ q → add3 (vx A q) (vx B q)) p)
         (neg3 (dx (λ q → add3 (vz A q) (vz B q)) p))
  , add3 (dx (λ q → add3 (vy A q) (vy B q)) p)
         (neg3 (dy (λ q → add3 (vx A q) (vx B q)) p))
    ≡⟨ cong₂ _,_ (curl-linear-x A B p)
                 (cong₂ _,_ (curl-linear-y A B p) (curl-linear-z A B p)) ⟩
  add3 (add3 (dy (vz A) p) (neg3 (dz (vy A) p)))
       (add3 (dy (vz B) p) (neg3 (dz (vy B) p)))
  , add3 (add3 (dz (vx A) p) (neg3 (dx (vz A) p)))
         (add3 (dz (vx B) p) (neg3 (dx (vz B) p)))
  , add3 (add3 (dx (vy A) p) (neg3 (dy (vx A) p)))
         (add3 (dx (vy B) p) (neg3 (dy (vx B) p)))
    ≡⟨ refl ⟩
  addVec3 (curl A p) (curl B p) ∎

-- 规范不变性: 规范势 A 加梯度场不改变旋度 (即不改变磁场)
gauge-invariance : ∀ A φ p →
  curl (λ q → addVec3 (A q) (grad φ q)) p ≡ curl A p
gauge-invariance A φ p = begin
  curl (λ q → addVec3 (A q) (grad φ q)) p
    ≡⟨ curl-linear A (grad φ) p ⟩
  addVec3 (curl A p) (curl (grad φ) p)
    ≡⟨ cong (λ v → addVec3 (curl A p) v) (curl-grad-zero φ p) ⟩
  addVec3 (curl A p) (fz , fz , fz)
    ≡⟨ addVec3-right-unit (curl A p) ⟩
  curl A p ∎

------------------------------------------------------------------------------
-- §3. Chern 链接的可证部分: 零场零通量
--   通量 = 环绕平面 k = 0 的 9 个格面上磁场 B 的 z 分量之和
--   (具体有限表求和, 非 postulate)。磁单极非平凡构型 (通量 = 陈数)
--   需要非平凡 U(1) 主丛, 对接 DiscreteKTheory — 诚实边界, 不写虚假证明。
------------------------------------------------------------------------------

sum9 : (GF3 → GF3) → GF3
sum9 g = add3 (add3 (g fz) (g (fs fz))) (g (fs (fs fz)))

flux : VectorField → GF3
flux B = sum9 (λ i → sum9 (λ j → proj₂ (proj₂ (B (i , j , fz)))))

-- 零场穿过环绕平面 k = 0 的通量恒为零 (闭合项, 直接归约)
zero-flux : flux (λ p → (fz , fz , fz)) ≡ fz
zero-flux = refl

-- 零矢量势的磁场 (curl = 0) 通量为零 —— "零磁单极" 的可证实例
zero-monopole-flux : flux (curl (λ p → (fz , fz , fz))) ≡ fz
zero-monopole-flux = refl

-- 0 postulate.
