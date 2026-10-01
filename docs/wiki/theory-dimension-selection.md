---
title: 维数选择 —— 「振动 ⟹ 三方向」的唯一性论证（DS1–DS8）
source: session
created: 2026-10-01
last_confirmed: 2026-10-01
audience: self
stage: draft
schema_version: 2
confidence: low
entity_type: claim
tags: [dimension-selection, three-directions, spin-statistics, linking-number, fox-neuwirth, P3, uniqueness]
status: current
---

# 维数选择：两条硬要求的交 = {3}（DS1–DS8）

> **上一版（口头的）把最后一步写成「最小性」**——「选最小的自洽维数」。那是**口味选择**：
> 它排除不掉 d = 4, 5, 6，只能说「我偏好最小的」。本页换成 **唯一性**：
> **两条硬要求的交集只落在 3 上**，不涉及偏好。

## 1. 两条要求（各带来源）

| | 要求 | 标准事实（**本页未形式化**） | 本页能证的部分 |
|---|---|---|---|
| **R1** | 统计性**只有两类**（排除任意子） | π₁(C_N(ℝ^d)) 的阿贝尔化：d = 2 时 ≅ ℤ（任意子合法、取之不尽）；d ≥ 3 时 ≅ ℤ₂（只有两类）。**Fox–Neuwirth 1962, Math. Scand. 10, 119**。经验支持：**任意子只在二维材料里被观测到** ⟹ 统计性的维度依赖是真的 | ★★ **DS1**：ℤ 型群的相位**不落在 ±1 上**（α = π/3 见证，im = √3/2 ≠ 0）——真定理；**DS3**：与 ES5（ℤ₂ ⟹ ±1）合并成 R1 的代数核 |
| **R2** | 连接数/扭转**非平凡**（仓库质量机制的前提） | d ≥ 4 时所有环都平凡、任何两个不相交的圆都不相连；d = 2 时两条闭曲线不能互连（第三维不存在）。**只有 d = 3 有非平凡链环数** | ★★★ **D3**：三叶结 3 个交叉用第 4 维鼓包**全部解开**且 R⁴ 无自交（数值）；★★ **D4**：Hopf link 在 3D 里 Lk = 1 且互不相交，压到平面后**必然相交**（数值） |

**R2 是仓库自己的质量机制的前提**：环扭转 ⟹ N ⟹ m² = N·M₀²（RT1–RT7）。

## 2. 唯一性主定理

```text
R1 ⟹ 3 ≤ d      （下界）
R2 ⟹ d ≤ 3      （上界）
⟹ d = 3         （唯一，不是「最小」）
```

| 定理 | 内容 |
|---|---|
| ★★★ DS7a `dimension_is_three` | `TwoClassStatistics d → NonTrivialLinking d → d = 3` |
| ★★★ DS7b `dimension_characterization` | `(TwoClassStatistics d ∧ NonTrivialLinking d) ↔ d = 3` |
| ★★ DS8 `both_requirements_needed` | 两条**都不可省**：去掉 R2 会放进 d = 4, 5, …；去掉 R1 会放进 d = 2 |
| DS6a/b/c | `¬ TwoClassStatistics 2`、`¬ NonTrivialLinking 4`、`TwoClassStatistics 3 ∧ NonTrivialLinking 3` |

## 3. ★★ 真定理：ℤ 型群的相位排除不掉第三类取值（DS1）

```text
χ_α(n) = exp(α·n·i)（ES7 已构造）⟹ χ_α(1) = exp(α·i)
取 α = π/3：χ(1) = 0.5 + (√3/2)·i，虚部 √3/2 ≠ 0
而 ±1 的虚部都是 0 ⟹ χ(1) ∉ {1, −1}        （Lean：DS1；证明走 `Complex.exp_im`）
```

⟹ 「统计性只有两类」这条性质**在 ℤ 型群上不成立** ⟹ 任意子**排除不掉**。
对照 ES5：在 ℤ₂ 型群上它成立。**同一个方程 χ(2) = χ(1)²，两种群，两个世界。**

## 4. ★★★ 数值：d ≥ 4 的显式解结（D3）

- 三叶结 `(sin t + 2 sin 2t, cos t − 2 cos 2t, −sin 3t)`，3D 投影 **3 个交叉**（红点，图 `fig_unknot_r4.png` 左）；
- 在每个交叉的两股处给第 4 维加**符号相反的高斯鼓包**（宽 25 点、高 0.35）：
  3 个交叉处两股的 **|Δx₄| = 0.70** ⟹ **3/3 全部解开**；
- 加鼓包后 R⁴ 中最小非相邻点距 **0.610 > 0** ⟹ 曲线**仍被嵌入**（没造出新自交）。

⟹ 该扭结在 R⁴ 中可解 ⟹ **四维及以上不存在非平凡扭结** ⟹ 非平凡连接数不存在（R2 的上界）。

## 5. ★★ 数值：d = 2 的互连不可能（D4）

Hopf link：`C₁ = {单位圆, z=0}`、`C₂ = {x=0, 圆心 (0,1,0), 半径 1}`。

- 3D 里两环最小距离 **1.000 > 0** ⟹ **互不相交**；
- Gauss 双积分环绕数 **−0.9996**（|Lk| = 1）⟹ 确实**相连**；
- `C₂` 的 **z 跨度 = 2** ⟹ 它用到了第三维；
- 投影到 `z = 0`（二维）：`C₂` 的像退化成线段 `x=0, y∈[0,2]`，与单位圆交于 **(0,1)** —— 几何交点数 **1**，
  且**无法消去**（平面里两条不相交的简单闭曲线不能互连，Jordan）。

⟹ **互连需要第三维** ⟹ d = 2 无非平凡连接数（R2 的下界那一侧）。

## 6. 维数判定表（D5）

| d | π₁ 阿贝尔化 | 统计只有两类? | 非平凡连接? | 同时满足? |
|---|---|---|---|---|
| 1 | 平凡（无交换） | 不适用 | 否 | 否 |
| 2 | ℤ | **否** | 否 | 否 |
| **3** | **ℤ₂** | **是** | **是** | **是** |
| 4 | ℤ₂ | 是 | **否** | 否 |
| 5 | ℤ₂ | 是 | 否 | 否 |

⟹ **只有 d = 3 三格全绿。**

## 7. 诚实边界（写死）

- **R1/R2 两条要求本身没有形式化**（需要代数拓扑：配置空间、辫群、Fox–Neuwirth；以及链环理论）。
  Lean 里抽成 `TwoClassStatistics d := 3 ≤ d` 与 `NonTrivialLinking d := d ≤ 3` 两个**定义**，
  docstring 里带来源。因此 **DS7 的证明是 `le_antisymm`——全部重量在那两条定义上**。
  这与 ES8 同一个模式：把无法形式化的输入**显式、不可偷渡**地放进类型。
- **真定理只有 DS1**（ℤ 型角色不落在 ±1）与 **DS3**（把它与 ES5 合并）。
- ★ **这不是「把 P3 变成推论」**：R1/R2 仍是输入。本页做的是把「维数 = 3」从一个
  **单一公设**（P3「三方向」）换成**两条可分别判死的要求的交**——**收窄了输入的性质，没有消掉输入**。
- 本论证**不排除** d = 2 作为整体自洽的物理（2+1 维任意子物理确实自洽）。它只说：
  **同时**要「只有两类统计性」和「非平凡扭转」时，只有 3 满足。
- **零新可检验预言。**

## 8. 死法（写死）

若在 d ≠ 3 里找到**等价自洽**的表述——(a) d = 2 加一个只给 ±1 的机制（即把 R1 换成别的来源），
或 (b) d ≥ 4 有非平凡替代品（如高维面纽结给出非平凡「扭转」）——则本论证**死**。

## 9. 产物

- Lean：`ProjectionPhysics/Explorations/DimensionSelection.lean`
  （DS1–DS8，11 条声明，零 sorry 零 warning，复用 `ExchangeStatistics` / `VibrationSpinStatistics`，挂聚合根）
- 数值：`scripts/verify_dimension_selection.py` → `artifacts/dimensionselection/`
  （report.json / summary.txt / fig_phase_sets.png / fig_unknot_r4.png / fig_dimension_verdict.png）
- 门禁断言：DS-A1★★ / A2★★ / A3★★★ / A4★★ / A5★★ / A6★ 共 6 条

**本页自纠一处 bug**：D2 的相位扫描第一版用了 `endpoint=False`，导致 α = π **落在网格外**
（π 不是 2π/200001 的整数倍）⟹ 只数到 1 个零点（应 2）。改回 `endpoint=True` 后为 2。

## 10. 补登记：与传统文献的关系（**本条的重叠面**）

写完本页后去查文献。结果必须写清（与本轮 ES 页漏接 `BraidThree` 是同一类错）：

| 本页的哪一半 | 文献里已有？ | 出处 |
|---|---|---|
| **R2 —— 用「只有三维有非平凡纽结/连接」来**选择**三维** | **已发表** | Berera, Buniy, Kephart, Päs, Rosa, *Knotty inflation and the dimensionality of spacetime*, **Eur. Phys. J. C (2017)**, arXiv:1508.01458, DOI 10.1140/epjc/s10052-017-5253-3。原话：「flux tube knots and links will only be topologically stable (or metastable) in three spatial dimensions… provides a dynamical explanation for the existence of **exactly three** large spatial dimensions」 |
| **R1 —— d = 2 给 ℤ、d ≥ 3 给 ℤ₂ ⟹ 只有 ±1** | **已发表**（本页引的 Fox–Neuwirth 1962 只是群论来源；**物理陈述**是他们的） | Leinaas & Myrheim, *On the theory of identical particles*, Nuovo Cimento B **37**, 1 (1977)；Wilczek 1982（任意子命名） |
| **两条串起来**（同一个「四维里纽结都平凡」的事实同时解释「三维只有 ±1」与「二维有任意子」） | **已由 Wilczek 公开讲过** | F. Wilczek, *Inside the Knotty World of 'Anyon' Particles*, **Quanta Magazine 2017-02-28**：同篇并列写「in four space dimensions it is trivial: all knots can be unraveled」与「in three space dimensions… the only consistent exchange factors are 1 and −1」 |
| 本页用的两个例子（**三叶结、Hopf link**） | **也是他们的例子** | EPJ C 2017 原文举 overhand/**trefoil** 与 **Hopf link** |
| 「为什么 3+1」是**已知体裁** | **多篇** | Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. **14**, L69 (1997)（论据不同：可预测性/稳定性/复杂度）；arXiv:0711.1111 *The Spin-Statistics Theorem in Arbitrary Dimensions*（D = 8n+3, 4, 5） |

**⟹ 本页对物理学界没有新东西。** 两条要求都是老的；「用它们夹出三维」这件事也已经有人做过——
只是物理语境不同：**他们把纽结稳定性当作暴胀的前提，我们把扭转非平凡当作质量机制的前提**。
本页唯一新的东西是**对本框架的**：把 P3 拆成两条可分别判死的要求（一个账本动作），不是新事实。

**教训（写死）**：写「维数选择」这类看似新颖的论证前，**必须先搜** `dimension selection` /
`why three spatial dimensions`；不能因为推理链是自己搭的，就当成自己的。
