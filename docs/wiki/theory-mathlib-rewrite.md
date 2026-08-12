---
title: 狄拉克桥与最小核心的 mathlib 重写版
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [mathlib, dirac, minimal-core, gamma-matrices, chiral, anchoring]
status: current
---

# 狄拉克桥与最小核心的 mathlib 重写版

> leo（2026-08-11）：继续其他文件更新，mathlib 要用到每一个可以进行的地方。

## 1. DiracMathlib（DB1'–DB6'）

对应代码：[`ProjectionPhysics/DiracMathlib.lean`](../../ProjectionPhysics/DiracMathlib.lean)

用 mathlib 的 **4×4 复矩阵**（`Matrix (Fin 4) (Fin 4) ℂ`）+ **Fin 4 旋量**
重写狄拉克桥（对照 core 版 `DiracBridge.lean` 的 2×2 分块手写）：

| 定理 | 内容 | 物理意义 |
|---|---|---|
| `gamma0_sq` | γ⁰² = 1 | 时间方向平方 = +1（度规时间签名） |
| `gamma1_sq`/`gamma2_sq`/`gamma3_sq` | γⁱ² = −1 | **空间方向平方 = −1（度规空间签名）——"时间特殊"的代数内容** |
| `gamma0_gamma1_anticommute` 等 6 个 | γ⁰γⁱ+γⁱγ⁰ = 0；γⁱγʲ+γʲγⁱ = 0 | Clifford 反交换在 4×4 层 |
| `mass_equation_couples_chiralities` | γ⁰ψ = ψ ⟺ ψ_L = ψ_R | **★ 质量 = 手征耦合**（DB5'，同 core DB4） |
| `zero_mass_has_chiral_asymmetry` | ∃ψ 手征不对称 | m=0 ⟹ Weyl（DB6'，光子边界） |

**新收获（core 版没有的）**：γⁱ² = −1 明确证明了"时间特殊"的代数内容——
时间方向平方 +1、三个空间方向平方 −1，这正是闵可夫斯基度规签名。

## 2. MinimalCoreMathlib（MC1'–MC4'）

对应代码：[`ProjectionPhysics/MinimalCoreMathlib.lean`](../../ProjectionPhysics/MinimalCoreMathlib.lean)

用 mathlib 的 2×2 复矩阵 + Fin 2 旋量 + `Complex.normSq` 重写最小核心：

| 定理 | 内容 | 物理意义 |
|---|---|---|
| `anchorMassSq_pos_of_nonzero` | 非零旋量 ⟹ m² > 0 | **★ 核心命题：自旋非零 ⟹ 质量非零**（MC2'） |
| `anchorMassSq_zero_of_zero` | 零旋量 ⟹ m² = 0 | 光子边界（MC3'） |
| `anchorMassSq_component` | m² = |ψ₁|² + |ψ₀|² | σ₁ 只交换分量不改变量（MC4'） |

## 3. mathlib 化的收益（对照 core 版）

| 方面 | core 版 | mathlib 版 |
|---|---|---|
| 矩阵 | 手写 Mat2/Mat4 + 分量展开 | `Matrix (Fin n) (Fin n) ℂ` |
| 证明 | re/im 展开到 Int + omega | `ext` + `fin_cases` + `ring` |
| 范数 | 手写分量范数 | `Complex.normSq`（`normSq_pos`/`normSq_nonneg`） |
| γ 平方 | 只有 γ⁰²=1 | γ⁰²=1 且 γⁱ²=−1（度规签名完整） |

## 4. 诚实边界

- 两版证明同一组核心命题（质量=手征耦合、自旋非零⟹m>0），
  结论一致——mathlib 版是**证明方法的现代化**，不是新物理
- γⁱ² = −1 是新形式化出来的（core 版未做），但它对应的是
  标准闵可夫斯基签名，非新预言
- mathlib 版用 ℂ（mathlib 内建）替代 core 版手写 ℂ——
  抽象层更高、证明更短，但底层数学相同
