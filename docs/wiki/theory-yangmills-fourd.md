---
title: 杨–米尔斯四维化：真四维格点规范结构 + 三处开口的闭合（Y4D1–Y4D9）
source: session
created: 2026-11-01
last_confirmed: 2026-11-01
audience: self
stage: draft
schema_version: 2
---

# 杨–米尔斯四维化（Y4D1–Y4D9）

> leo（2026-11-01）：「我说的是杨米尔斯猜想，有进行四维化吗？结掉我之前没有证明完整的部分」。

## 1. 四维化的真实状态（先摆清楚）

| 模块 | 维度 | 场强定义 | 规范变换 |
|---|---|---|---|
| `YangMillsLattice.lean` | **一维**（`ℤ → Mat3C`） | `F(t) = [A(t), A(t+1)]`（近邻） | **没有** |
| `YangMillsContinuum.lean` | **四维指标**（`Fin 4 → ℝ`、`Fin 4 → ℤ`、四维环面 Haar） | `F_μν(x) = [A_μ(x), A_ν(x)]`（**同点**） | **没有** |
| 本模块 `YangMillsFourD.lean` | **四维格点** `Site := Fin 4 → ℤ` | `F4 = [U_μ(x), U_ν(x+μ̂)]`（近邻，真四维指标） | **有**（Y4D3） |

**结论**：此前「四维化」只做到**指标是四维**，没做到**结构是四维**——没有链路变量、没有 plaquette、没有规范变换、没有 Wilson 环。而规范不变性正是「规范理论」的定义。本模块补的就是这一层。

## 2. 补的四维结构

| 编号 | 内容 |
|---|---|
| **Y4D1a** `shift_comm` | 不同方向的移位可交换（μ ≠ ν）—— plaquette 闭合性的前提 |
| **Y4D2** `plaquette` | **1×1 Wilson 环** `P_μν(x) = U_μ(x)·U_ν(x+μ̂)·U_μ(x+ν̂)⁻¹·U_ν(x)⁻¹`；链路取值 `Units Mat3C`（= GL(3,ℂ)，逆元律免费） |
| **Y4D3 ★★★** `plaquette_gauge_covariant` | **规范协变**：`A_μ(x) ↦ g(x)A_μ(x)g(x+μ̂)⁻¹` ⟹ `P ↦ g(x)·P·g(x)⁻¹`（伴随）。仓库此前**一个字都没有** |
| **Y4D4 ★★★** `trace_plaquette_gauge_invariant` | **Wilson 可观测量**：`tr P_μν(x)` 规范不变（迹可循环 + `g⁻¹g = 1`）。这是格点 QCD 真正会测的量 |
| **Y4D5** `F4_can_be_nonzero` | 四维格点上存在非零近邻场强（见证：方向 0 取 `cycle3`、方向 1 取 `diag123`，在真正的四维点上） |
| **Y4D6 ★★** `F4_norm_bound_uniform_in_dimension` | `‖F4‖ ≤ 6·‖U_μ(x)‖·‖U_ν(x+μ̂)‖`，常数 **6 只来自色维数 3**（3×3 的求和因子），与 d = 4、与格点体积无关 |

## 3. 结掉的三处（全是负面结果，这是重点）

### Y4D7 ★★★ 质量间隙与维数无关

`mass_gap_independent_of_dimension`：4D 格点上间隙陈述与 1D **逐字相同**，且**前提里没有任何格点/维度假设**（`m² = N·M₀²` 的整数性决定一切）。
⟹ **四维化对间隙的贡献是 0**。这不是遗憾，是结论：四维化不会产生间隙。

### Y4D8 ★★★ 非交换性不是间隙的来源（把「未证蕴含」升级为「已证不可能」）

`noncommutativity_is_not_the_source_of_the_gap` 同时成立三件：
1. 存在**非阿贝尔**四维构型（`F4 ≠ 0`，Y4D5）；
2. 存在**处处交换**的四维构型（`F4 ≡ 0`，`abelian_config_field_strength_zero`）；
3. 间隙陈述**对任何构型都成立**（Y4D7，前提里没有 `U`）。

⟹ 「自相互作用（非交换）⟹ 质量间隙」这条箭头在框架内**不可能是蕴含**：前件与后件互相独立。
仓库 2026-10-08 对抗性审稿把 CA7 改名并登记「箭头本身没有被证明」——本定理把它升级成**已证不可能**。要让箭头成立，必须引入把**场强**与**条数计数**联系起来的**新动力学**（框架里没有）。

### Y4D9 格距 a → 0 的收敛：仍然没有（且不能靠加维度补）

Y4D6 给的是**一致有界**（收敛的必要条件），**不是收敛**。缺的是**格点指标上的拓扑/度量**——框架里只有 `ℤ⁴` 上的场，没有连续流形。这一条与 `YangMillsContinuum.lean:311` 的登记一致，本模块不改变它。

## 4. 因此现在能说与不能说的

**能说**：
- 四维规范化结构在框架内**已建立**（链路 + plaquette + 规范协变 + 规范不变的 Wilson 量）；
- 间隙论证**与维度无关**（已证）；
- 「非交换 ⟹ 间隙」在框架内**不可能为真**（已证）。

**不能说**：
- 不能说解决了 Clay 问题（3+1 维连续 QFT + Wightman/OS 公理 + 重整化，一个都没有）；
- 不能说四维化带来了新证据（恰恰相反，Y4D7/Y4D8 是负面结果）；
- 不能声称禁闭（没有线性势/弦张力的推导；`√σ = 445 MeV` 是外部锚点）；
- 不声称 λ / M₀ 被推导（SC6：框架零标度内容）。

⚠️ **口径冲突（已登记，待 leo 裁决）**：`paper3/projection-yangmills-gap.tex:1303` 结论写
「The Yang–Mills conjecture is proved」，与同篇 `:392` 的「what is proved is the **conditional** …」
以及 `:1230` 的「认同是结构性的且部分的」冲突。Y4D7/Y4D8 恰好把这条冲突变成形式化的：
框架内能证的是「条件算术 + 负面结果」，不是「猜想被证明」。

## 5. 文件

- Lean：`ProjectionPhysics/Explorations/YangMillsFourD.lean`（Y4D1–Y4D8 定理 + Y4D9 边界，零 sorry，已挂聚合根；`#print axioms` 只依赖 `propext / Classical.choice / Quot.sound`）
- `lake build` 5722 jobs 全绿
