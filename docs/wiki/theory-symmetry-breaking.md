---
title: 理论概念：对称性破缺（核平移 = 规范对称，核纤维 = 真空流形）
source: session
source_note: 2026-08-05 问答澄清
created: 2026-08-05
last_confirmed: 2026-08-05
audience: self
stage: current
schema_version: 2
confidence: medium
---

# 理论概念：对称性破缺（隐数框架内可实现）

> 2026-08-05 会话问答编译（compile-first）。leo 问：物理的对称性破缺推导（Z₂ 势 → 真空选择 → Goldstone → Higgs）能否在隐数推导里实现？
> 结论：**能，且已证三个定理（SB1–SB3）**。对称性破缺的静态结构全部落在已有框架内——它比微积分（差商 D7'）更早可达，因为**核平移只需加法，不需要乘法逆元**。
> 所有引用定理见 SPEC.md 与各 .lean 模块；状态标记：✅ 已证 / 📋 草案 / ❌ 未做。

## 1. 核心主张：核平移对称性 = 隐数里的规范对称性

物理：规范对称 = 变换下规律（拉格朗日量）不变。
隐数：变换 ζ ↦ ζ ⊕ κ（κ ∈ ker π），观测不变——**这是已证的 K3**：

```
observables_depend_only_on_image : π(s_im + s_ker) = π s_im   -- Kernel.lean
```

ker π 作为加法群平移作用在 S 上，就是规范变换群。
theory-time-emergence.md 曾写"没有对称群 ⟹ 谈不上破缺"——现在对称群有了：**ker π**。

## 2. 势的构造：经投影因子化 ⟹ 对称是定理不是假设

定义势 V : S → Int 经投影因子化：

```
V(ζ) := Ṽ(π ζ)
```

- ✅ **SB1** `factorized_potential_is_kernel_shift_symmetric`：因子化势自动核平移对称
  `V(s⊕κ) = V(s)` 对一切核元素 κ——直接由 K3 推出。"规律对称"是定理。
- 对比物理 V(φ) = −½μ²φ² + ¼λφ⁴ 的 V(φ)=V(−φ)：Z₂ 是离散对称；
  核平移是**连续**对称（加法群作用），更强。

## 3. 真空流形 = 整条核纤维

物理：真空满足 dV/dφ = 0，真空流形 = 势的最小值流形。
隐数（无导数，用全局最小定义真空）：

- ✅ **SB2** `kernel_fiber_is_ground`：若 v₀ = π ζ 是 Ṽ 的最小点，
  则整条核纤维 π⁻¹(v₀) = v₀ ⊕ ker π 上每个点都是 V 的全局最小。
- ✅ **SB2'** `shifted_vacuum_is_ground`：真空的核平移仍是真空——
  **沿核方向移动真空不付出势能**。这就是 Goldstone 模式的代数种子。

## 4. 破缺 = 选择真空（定义句逐字成立）

物理定义句：规律对称，状态不对称。
隐数定理（✅ **SB3** `broken_vacua_observationally_equivalent`）：

```
非平凡核 ⟹ ∃ a b, a ≠ b ∧ π a = π b ∧ V a = V b
```

即存在观测等价（π 相同）、势相等（V 相同）、但状态不同（a ≠ b）的两个真空。
"规律对称（势相等）+ 状态不对称（态不同）"不是口号，是 Lean 定理。

## 5. Goldstone 定理的隐数对应：核模式 = 无质量模式

| 物理 | 隐数 | 状态 |
|---|---|---|
| 沿真空流形平坦方向（无质量） | 沿核纤维移动无势能变化（SB2'） | ✅ 已证 |
| Goldstone 玻色子 | 核模式：改变 ζ_κ 不改观测 | ✅ K4（内部自由度） |
| 质量 ∝ 真空期望值 | m² = κ(ζ_κ)，ζ_κ = 真空的核分量（Mass.lean 草案） | 📋 |
| Higgs 吃掉 Goldstone → 玻色子质量 | ⊗ 泄漏：i⊗i = −1 ∈ ℝ，核元素相乘逃出核 | ✅ 环事实（ℂ 乘法） |

关键张力与出路：核模式沿核方向平坦（无质量），但质量草案说"质量 = 核上的不变量"。
物理里同样的张力由 Higgs 机制解决：Goldstone 被规范场"吃掉"。
隐数候选出路：**乘法 ⊗ 把核分量混进观测分量**（i·i = −1），
即 ℤ[i] 的核 ker(Re) = iR **不是环的理想**（ideal）——核元素相乘泄漏到观测空间。
这是"规范玻色子吸收 Goldstone 获得质量"的代数原型（D8 开放问题）。

## 6. 剩余对称性（对应 U(1)_em 保持无质量）

- 物理：SU(2)×U(1) → U(1)_em，剩余对称 ⟹ 光子无质量。
- 隐数：完全破缺 = 核平移群全破（稳定子只剩单位元）；
  部分破缺 = 真空在某个子群（如 ℂ 单位群 {±1, ±i} 的作用）下不动。
  注：±i 作用把纯实真空移出实轴（i·v = iv ∈ iR），只有 {±1} 保持——离散 Z₂ 剩余。
  连续剩余对称（U(1) 型）需要乘法作用 + 复结构，尚未形式化。📋

## 7. 与 D7' 差商的关键对比：破缺更早可达

| | D7' 差商 | D8 对称性破缺 |
|---|---|---|
| 需要的结构 | 乘法逆元（h⁻¹） | 只需加法 + 核 |
| ℤ[i] 实例 | ❌ 卡死（非域） | ✅ 完全满足 |
| 已证 | E9 差分（分子），D7' 开放 | SB1–SB3 全证 |
| 原因 | 除法 = 乘以逆元，ℤ[i] 无 Inv | 核平移是加法层，不需要 Field |

结论：**对称性破缺比微积分更早进入隐数框架**——这是 D8 的卖点。

## 8. 已证 / 草案 / 未做

- ✅ SB1 因子化势核平移对称 · ✅ SB2 核纤维都是真空 · ✅ SB2' 真空平移仍真空 · ✅ SB3 破缺真空存在
- ✅ 复用：K3 核不可观测 · K4 内部自由度 · L5 rank-nullity（iR = ker Re）
- 📋 D8 `SymmetryBreaking` 结构（SymmetryBreaking.lean，axiom-like）
- 📋 质量 = 真空核分量（接 Mass.lean KernelRepresentation）
- ❌ 动态破缺（T > T_c 相变、时间演化中的破缺）——无时间（同 theory-time-emergence）
- ❌ 连续剩余对称（U(1) 型稳定子）——需乘法作用 + 复结构
- ❌ ℤ[i] 实例化 is_ground 验证——Int 平方非负需非线性工具（omega 不够），升级系数环可解

## 9. 相关链接

- 草案：D8 SymmetryBreaking（SPEC.md）· Mass.lean KernelRepresentation · D5 FlowRepresentation
- 已证：K3/K4（Kernel.lean）· L5（LinearAlgebra.lean）· E1–E16（Differential.lean）
- 概念：theory-kernel-mass.md（核/质量）· theory-time-emergence.md（时间/破缺的旧结论）
