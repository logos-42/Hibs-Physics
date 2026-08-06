---
title: 理论概念：隐数四元数（比较对象：i²=-1 从反交换涌现）
source: session
source_note: 2026-08-06 任务 Prompt 执行
created: 2026-08-06
last_confirmed: 2026-08-06
audience: self
stage: current
schema_version: 2
confidence: medium
---

# 理论概念：隐数四元数（比较对象）

> **2026-08-06 方向修正**：本页内容已降级为**比较对象**。隐数主线是
> [theory-projection-algebra.md](./theory-projection-algebra.md)（第一性 = 投影幂等 P²=P）。
> 四元数回答的问题是"空间已有时旋转如何代数化"，不是"无状态对象如何产生状态"。
> 保留本页：隐数空间若存在内部乘法，会产生类似四元数的非交换结构（Q3 已证）。

> 2026-08-06 会话编译（compile-first）。leo 的任务：无状态万向向量 u ∈ H 如何经投影产生状态？
> 隐数空间是否存在满足 i²=-1 或 a·b·c=-1 的"隐数单元"？隐数结构是否类似复数/四元数？
> 结论：**全部落在已有框架内，且已证**。无状态向量 = `HiddenVector.observed = none`；
> 投影产生状态 = H1；幂等投影 = H4（"观测塌缩"）；**四元数关系 i²=j²=k²=ijk=-1 是 Clifford 反交换的必然表示，不是新公理**。
> 所有引用定理见 SPEC.md 与各 .lean 模块；状态标记：✅ 已证 / 📋 草案 / ❌ 未做。

## 1. 无状态万向向量的形式化（H1–H5, HiddenSpace.lean）

物理直觉：u ∈ H 无固定方向，包含所有可能方向；投影 P : H → V 产生具体状态。
隐数形式化：`HiddenVector (S V : Type) (π : S → V)`，字段 `source : S`（载体）、`observed : Option V`（状态标签）、`consistency`（标签真实性）。

```
state = none   ⟹ 无状态（方向未定，万向）      -- hvUnprojected
state = some v ⟹ 已投影，状态 v（方向已定）     -- hvProjected
```

- ✅ **H1 投影产生状态**：`projection_generates_state`：∀ s : S，(hvProjected π s).observed = some (π s)——任何源元素经投影获得状态，且状态 = 观测值。**"量子态坍缩"的代数骨架：投影 = 从 Option none 到 some v 的转变。**
- ✅ **H2 状态真实性**：`state_consistency`：标签 Some v ⟹ π(source) = v（标签是事实，不是装饰）。
- ✅ **H3 不同投影 ⟹ 不同状态**：`distinct_projections_distinct_states`：π₁s ≠ π₂s ⟹ 状态不同。实例：cI 在 Re 下为 0、在 Im 下为 1（`cI_has_two_states`）——**同一万向向量，两种观测给出两个不同状态**。
- ✅ **H4 幂等投影**：Π = ι∘Re : ℂ → ℂ（先观测再嵌入），`hiddenReProj_idempotent`（P(P(x)) = P(x)，观测后再观测不变）、`hiddenReProj_linear`、`hiddenReProj_kernel_iff`（ker Π = 虚轴）。**"坍缩不可逆"的代数形式：一旦观测，再观测不变。**
- ✅ **H5 方向涌现**：`direction_emerges_from_projection`：z = Re(z)·1 + Im(z)·i——可观测方向（实轴）+ 核方向（虚轴，不可观测）。

## 2. 隐数四元数：i²=j²=k²=ijk=-1 从反交换涌现（Q1–Q5, Quaternion.lean）

物理直觉：四元数把二维复数乘法扩展到三维旋转。
隐数答案：四元数单位 {i, j, k} ↔ 反交换生成元 {iσ₁, iσ₂, iσ₃}（Pauli 复化），全部关系是 Clifford 定理的推论：

```
i² = j² = k² = -1   ⟸  C1（σᵢ² = I）+ E14（标量层中心）   -- Q1
ijk = -1            ⟸  C6（σ₁σ₂ = -iσ₃）+ C1              -- Q2
ij = k ≠ -k = ji    ⟸  C2（反交换）                        -- Q3
```

- ✅ **Q1** `quat_i_sq`/`quat_j_sq`/`quat_k_sq`：每个生成元平方 = -1（C3 的 i 涌现的推广）。
- ✅ **Q2** `quat_ijk_minus_one`（ℍ 环内）+ `iSigmas_ijk`（矩阵表示内）+ `triple_product_square`（纯 Clifford：(σ₁σ₂σ₃)² = -1）——**"a·b·c = -1"猜想的已证实例**。
- ✅ **Q3** `quat_ij_ne_ji`：**隐数代数必然非交换**（与 ℂ 的本质区别）。
- ✅ **Q4** `quat_mul_assoc`：ℍ 是结合环。
- ✅ **Q5** `quatToMat_mul`：Φ(a+bi+cj+dk) = aI + b(iσ₁) + c(iσ₂) + d(iσ₃) 保加法保乘法——**四元数完全落入 Mat2 = Cℓ(3) 表示，无需新代数对象**。
- ✅ **Q6** `cToQuat_mul`：ℂ ⊂ ℍ 子环（二维 → 四维扩展不丢结构）。
- ✅ **Q7** `quatHiddenUnit`/`cliffordHiddenUnit`：`HiddenUnit` 草案（a²=-1 ∧ abc=-1 ∧ ab≠ba）双实例化——**"隐数单元"存在且有两个自然实例**。

## 3. 回答 Q1–Q5

| 问题 | 答案 | 证据 |
|---|---|---|
| Q1 无状态向量可否数学定义 | **可以**：Option 状态标签，none = 无状态 | HiddenSpace H1/H2 |
| Q2 投影是否产生状态 | **可以**：状态 = 观测值，且不同投影给不同状态 | H1, H3, cI_has_two_states |
| Q3 隐数空间是否需要新代数结构 | **不需要**：复数（已有 ℂ）→ 四元数（Q1–Q5）→ 矩阵（Mat2）全部是已有表示的推论 | Q5 |
| Q4 隐数四元数是否存在 | **存在**：{i,j,k} = {iσ₁,iσ₂,iσ₃}，i²=j²=k²=ijk=-1 全部已证 | Q1–Q3, Q7 |
| Q5 能否描述空间间关系 | 旋转表示（单位四元数共轭作用）是**草案**：需范数+逆元，ℤ 无逆元（D7' 同款卡点） | QuatRotation 📋 |

## 4. 诚实边界

- **3D 旋转表示未证**（`QuatRotation` 📋）：单位四元数 v ↦ q·v·q⁻¹ 需 |q|²=1 与逆元，ℤ 系数无逆元——升级系数环到 ℚ[i]/ℝ 后可达（与 D7' 差商同款卡点）。
- **无概率公理**："类量子坍缩"仅取代数骨架（投影产生状态 + 幂等 + 核不可观测 K3），不声称 Born 规则。
- 四元数乘法表在 ℤ 系数上验证（`quat_mul_assoc` 等），连续/域版本未做。
- 下一障碍：**系数环升级**（ℚ[i]/ℝ）解锁差商（D7'）+ 旋转（QuatRotation）；或先做 Clifford 偶子代数 = ℍ 的表示论陈述（D6 延伸）。
