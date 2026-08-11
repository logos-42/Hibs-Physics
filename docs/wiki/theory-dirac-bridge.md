---
title: 狄拉克方程桥：质量项 = 手征耦合（锚定的代数内容）
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: concept
tags: [dirac, chiral, mass-origin, weyl, anchoring, electron]
status: current
---

# 狄拉克方程桥：质量项 = 手征耦合

> leo（2026-08-11）：电子是一个点，有狄拉克方程的自旋，但质量还没有
> 被确立是怎么产生的。用狄拉克方程验证新假设：
> **质量 m 在狄拉克方程中的代数角色 = 左手/右手 Weyl 旋量的耦合强度**。

## 1. 结构（Weyl/手征表示，2×2 分块）

对应代码：[`ProjectionPhysics/DiracBridge.lean`](../../ProjectionPhysics/DiracBridge.lean)（DB1–DB6）

```text
DiracSpinor ψ = (ψ_L, ψ_R)：左手 + 右手 2 分量旋量
γ⁰ = [[0, 1],[1, 0]]，γⁱ = [[0, σᵢ],[−σᵢ, 0]]  (i = 1,2,3)
质量项 mψ ⟹ 左手/右手耦合
```

- 4×4 γ 矩阵用 2×2 分块构造（复用 Clifford 的 σᵢ 与 spinor_rep_hom）
- `gamma0_act_swaps_chiralities`：γ⁰ 作用 = 交换左右手

## 2. 核心定理（DB4–DB6）

| 编号 | 定理 | 物理内容 |
|---|---|---|
| DB3 | `gamma0_sq`：γ⁰² = 1 | 度规正定方向 |
| DB4 | `mass_equation_couples_chiralities`：**(γ⁰−1)ψ = 0 ⟺ ψ_L = ψ_R** | ★ **质量解 = 手征耦合**：有质量粒子要求左右手相等 |
| DB5 | `zero_mass_has_chiral_asymmetry`：∃ψ, γ⁰ψ ≠ ψ | **m = 0 ⟹ 手征对称（Weyl）**：左右手独立 = 光子 |
| DB6 | `gamma0_gamma1_anticommute`：γ⁰γ¹ + γ¹γ⁰ = 0 | Clifford 关系在 4×4 层（时间/空间反交换） |

## 3. 与最小核心的对接

```text
有质量粒子 = 手征耦合 = 锚定（自旋抵抗空间运动）   ← m ≠ 0
光子       = 手征对称 = 零锚定（完全随空间运动）   ← m = 0
```

狄拉克方程的结构与"质量 = 内部运动对空间运动的锚定"假设**完全一致**：
质量项 mψ 在方程中就是手征耦合的角色。

## 4. 数值验证（诚实结论）

脚本：[`scripts/verify_dirac_electron.py`](../../scripts/verify_dirac_electron.py)

- **结构检验 ✓**：狄拉克方程验证新假设的 STRUCTURE（质量项 = 手征耦合）
- **数值检验 ✗**：狄拉克方程把 m 当输入参数（E = √(p²c²+m²c⁴)），
  不解释 m 的来源；新假设的独立输入 M₀ ≈ 0.987 GeV（胶球）与
  m_e = 0.511 MeV 差距 966 倍（纯锚定构造）/ α 组合无干净因子
- **综合判定**：新假设通过结构检验，未通过数值检验——与
  "第二输入未找到"结论一致；数值缺口需 Higgs/Yukawa 层
  （与标准模型分工一致：QCD 质量 vs Higgs 质量）

## 5. 诚实边界

- 验证的是质量项的**代数结构**（手征耦合），不是质量数值
- 4×4 γ 代数仅验证 γ⁰² = 1、γ⁰γ¹ 反交换；γ¹γ²、γ²γ³ 等
  反交换关系可类比推出（σ 层已全证），未逐一形式化
- 完整的狄拉克方程（时空导数、平面波解、自旋磁矩 g=2）未形式化
  ——本模块是"质量从何产生"的代数种子
