---
title: 空间延拓性：折叠 / 密度压缩 / 边界维持能量（度规层 + 能量预算层）
source: session
created: 2026-08-19
last_confirmed: 2026-08-20
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: concept
tags: [space-extensibility, fold, density, metric, boundary-energy, spiral-field, anchoring, fold-continuation, potential-coupling]
status: current
---

# 空间延拓性：折叠 / 密度压缩 / 边界维持能量

> leo 的新假设（2026-08-19）：空间是可折叠、可压缩的（"延拓橡皮泥"）。
> 一个边界把内部高密度空间域与外部隔开，内部空间比外部"大"（延拓性）。
> 边界维持"空间域差值"（两种势差），需要能量；空间一直运动（动态），
> 但如同橡皮泥可压缩密度。维持边界的是一个类似螺旋旋转的巨大场，
> 把整个内部空间看成一个统一系统。

## 0. 分层总览（两层互补，不重复）

这个方向有两层 Lean 形式化，各司其职：

| 层 | 模块 | 内容 |
|---|---|---|
| **度规层**（本页新增） | `SpaceFold.lean` SF1–SF11 | 密度度规 `det(g)=−ρ²/c²+v²(ρ²−1)/c⁴`、延拓性、势差 ΔΦ、流动×压缩耦合、褶皱数延拓（SF8）、势差-密度耦合（SF9–SF10）、自维持上限（SF11） |
| **能量预算层**（上轮已有） | `Explorations/SpaceExtensibility.lean` SE1–SE5 | 弹性压缩能 `½κ(r−1)²`、边界能 `σS`、旋转能 `½νB²`、螺旋场维持 |

两层的关系：能量预算层回答"**维持需要多少能量**"（用弹性模型），
度规层回答"**密度如何嵌入时空结构**"（放松保体积，接到 GR 入口）。

## 1. 核心命题（度规层）

对应代码：[`ProjectionPhysics/SpaceFold.lean`](../../ProjectionPhysics/SpaceFold.lean)

```text
既有主线（SM5/SG2）：det(g) = −1/c²（保体积 = 流动是坐标变换层面）
新假设：空间密度 ρ 可变 ⟹ det(g) = −ρ²/c² + v²(ρ²−1)/c⁴
       └── 流动 × 压缩 的耦合项（新）
```

### SF1. 密度度规（放松保体积）

- `densityMetric ρ v c`：`g = [[1−v²/c², v/c²], [v/c², −ρ²/c²]]`
- `density_metric_unity_is_gordon`：ρ=1 ⟹ 退化为主线 `SpaceGravity.gordonMetric`
- **★ `density_metric_det`**：`det(g) = −ρ²/c² + v²(ρ²−1)/c⁴`
  - 关键结构：交叉项 `v²(ρ²−1)/c⁴` = **"流动 × 压缩"的耦合**
  - ρ=1（未压缩）⟹ `−1/c²`（SG2 保体积）
  - v=0（静态折叠）⟹ `−ρ²/c²`（纯密度贡献，`density_metric_det_static`）

### SF2. 延拓性（内部空间比外部大）

- **★ `interior_domain_larger`**：`ρ_out < ρ_in`（内部密度更高）⟹
  `|det(g_in)| > |det(g_out)|`——内部空间被压缩 ⟹ 局部体积元更大 ⟹
  "一个边界内部的空间比外部大"（leo 的延拓性，Lean 全证）。

### SF3. 空间域差值（势差）

- `flowPotential v = v²/2`（主线 SG 的 Gordon 弱场匹配 Φ = ½v²）
- `domainPotentialDifference v_in v_out = ½(v_in² − v_out²)`
- **这就是 leo 说的"两种势差 / 空间域差值"**：同一边界两侧，
  空间流动速度不同 ⟹ 势不同；`potential_difference_sign`：
  `|v_out| < |v_in|` ⟹ 势差为正。

### SF4–SF5. 压缩流动空间的能量

- `compressEnergy k ρ ρ₀ = ½·k·((ρ−ρ₀)/ρ₀)²`（密度应变能，k = 空间刚度）
- `boundaryEnergy k ρ_in ρ_out = ½·k·((ρ_in−ρ_out)/ρ_out)²`（边界维持能量）
- `compress_energy_nonneg` / `boundary_energy_nonneg`：非负（折叠耗能不产能）
- `compress_energy_zero_at_rest` / `boundary_energy_zero_no_difference`：
  无折叠（ρ=ρ₀）⟹ 零维持成本

### SF6. 螺旋旋转场维持（动态，非静态墙）

- `hasHelicalBoundary vx vy`：两方向都参与 ⟺ 环流非零
- `helical_boundary_iff_circulation_nonzero`：环流非零 ⟺ 螺旋边界存在
- `unidirectional_not_helical`：单方向流动不是螺旋边界（无旋转）
- 接 `SpaceField3D.SF5`（B = curl C = 自旋涡旋）：边界是持续旋转的空间流，
  "类似螺旋旋转的巨大的场"。

### SF7. 统一（三者同源）

- **★ `boundary_energy_is_compress_energy`**：边界维持能量 = 压缩能量
  （用密度比重写）——"密度域差 ⟺ 势差 ⟺ 维持能量"三者同源，
  都由内部密度相对外部的比值决定。

## 1.5 第二轮（2026-08-20）：内部继续折叠（Q1）+ 边界势差放大（Q2）

leo 两个新问题：
1. 能否在拓扑上**继续折叠**（更多褶皱）⟹ 内部空间更大？
2. 让边界的**整个势能差**变大 ⟹ 内部空间能否更大？

**Lean `SpaceFold.lean` SF8–SF11（全证零 sorry）**：

### SF8. 褶皱数延拓（Q1 回答）

- `foldedDensity ρ₀ N = N·ρ₀`：叠 N 层 ⟹ 有效密度 = N 倍基线密度
  （橡皮泥对折一次 = 两层……"拓扑结构的继续折叠"= 层数 N 的加法累积）
- `folded_density_additive`（SF8a）：褶皱数可加——先叠 N₁ 层再叠 N₂ 层
  = 叠 N₁+N₂ 层（继续折叠是加法结构）
- `folded_density_mono`（SF8b）：N₁ < N₂ ⟹ ρ(N₁) < ρ(N₂)
- **★ `more_folds_more_space`（SF8）**：N₁ < N₂ ⟹
  `|det g(ρ(N₂))| > |det g(ρ(N₁))|`——**褶皱更多 ⟹ 内部空间更大**。
  链条：褶皱数 N↑（SF8b）→ 密度 ↑ → SF2 延拓性。
- **Q1×Q2 汇合 `more_folds_larger_potential`**：褶皱越多 ⟹ 边界势差越大
  ——折叠既是"内部空间更大"也是"势差更大"，同一件事的两面（印证 SF7）。

### SF9. 势差-密度耦合（新物理内容，显式公设）

- `domainPotentialFromDensity α ρ_in ρ_out = ½α(ρ_in²−ρ_out²)`
- 物理图像：**压缩空间流动更快**（v = β·ρ，α = β²）——密度差本身产生
  势差。这把 SF3（势差，速度语言）与 SF2（延拓性，密度语言）接起来，
  是 SF7"三者同源"的定量化。
- `potential_difference_coupling_eq`（SF9a 显式形式）；
  `potential_mono_density`（SF9b）：α>0 时 ρ_in↑ ⟹ ΔΦ↑（链条第一跳）
- **诚实标注：α 的数值来源是第二输入缺口**（同 k/κ/ν/B）。

### SF10. 边界势差放大 ⟹ 内部空间更大（Q2 回答）

- **★ `larger_potential_larger_space`（SF10）**：ΔΦ₁ < ΔΦ₂ ⟹
  `|det g(ρ_in₂)| > |det g(ρ_in₁)|`。链条（全 Lean 证）：
  ΔΦ↑ → ρ_in↑（SF9 耦合逆）→ |det|↑（SF2 延拓性）。
- `totalBoundaryPotential ΔΦ S = ΔΦ·S`："**整个**边界"积累的总势差；
  `total_potential_mono`（SF10b）S 固定时 ΔΦ↑ ⟹ 总势差↑；
  **★ `larger_total_potential_larger_space`（SF10c）**：边界面积固定、
  单位势差放大 ⟹ 总势差放大 ⟹ 内部更大（Q2 完整版）。

### SF11. 自维持上限 ∝ 旋转强度（势差驱动的预算侧）

- `selfSustainLimit ν B κ g2 V = B·√(ν·V/(κ·∫g²dV))`：SE5 自维持上限
- `self_sustain_limit_mono_in_B`（SF11a）：B↑ ⟹ δ_max↑（线性）；
  `self_sustain_limit_sq`（SF11b）：δ_max² = νB²V/(κ∫g²)（SE5 边界等式）
- 物理：**势差驱动（B）放大 ⟹ 可支撑更大折叠比 ⟹ 内部空间更大**，
  但 E_rot ∝ B² 增长（势差驱动本身耗能，SE5 框架内自洽）。

### 数值测量（`scripts/measure_fold_topology.py`，本轮入门禁）

多褶皱径向包络叠加（g(r)=Σaₖ·exp(−((r−rₖ)/wₖ)²)）+ 固定能量预算反解：

| 问题 | 测量 | 答案 |
|---|---|---|
| Q1 | 固定外部投入能量预算，反解可达 δ | **N=5 褶皱内部空间 14.647 vs 单褶皱 2.874（5.10x）——拓扑继续折叠确实让内部更多** |
| Q1 机制 | 多褶皱增大 ∫g²dV 与 V_fold | 更多褶皱层装更多空间；代价 E_bdry 略增，净收益为正 |
| Q2 | 边界势差驱动 B 放大（δ_max ∝ B） | **δ_max 1.682 → 13.454 线性增——势差放大 ⟹ 自维持范围内可支撑更大折叠比 ⟹ 内部更大** |
| Q2 代价 | E_rot ∝ B² | 势差驱动本身耗能，SE5 框架内自洽 |
| Q2 反例 | 单纯加硬边界层 γ | E_bdry 单调增但 **δ_max 不变**（δ_max 与 γ 无关）——要放大驱动强度而非刚度 |

## 2. 能量预算层（上轮已有，SE1–SE5）

对应代码：[`ProjectionPhysics/Explorations/SpaceExtensibility.lean`](../../ProjectionPhysics/Explorations/SpaceExtensibility.lean)
+ 数值 [`scripts/verify_space_extensibility.py`](../../scripts/verify_space_extensibility.py)

- **SE1** 压缩能密度 `½κ(r−1)² ≥ 0`，为 0 ⟺ 无折叠（r=1）
- **SE2** 内部空间更大 ⟺ 域差 δ>0 ⟺ 压缩能为正
- **SE3** 总压缩能对体积可加、随折叠比/体积单调
- **SE4** 统一系统总能 = 压缩 + 边界 + 旋转，总能 ≥ 每项
- **SE5** ★ 螺旋旋转场维持：旋转强度 B 足够大（`κ(r−1)²V ≤ νB²`）⟹
  旋转能覆盖压缩维持成本——**边界维持能量的可计算答案**：
  `δ ≤ δ_max` 螺旋场自维持（外补=0），`δ > δ_max` 需外能 `E_req = E_comp − E_rot`

数值答案（`δ_max = 1.6818`）：折叠比在自维持上限内，螺旋场**内建**维持边界，
不需要额外能量；超过上限后外补能量随 δ 单调增长。

## 3. 数值验证

| 项 | 结果 |
|---|---|
| SF1 det 公式（200 随机） | 机器精度（< 1e-12） |
| SF1s 静态折叠 det = −ρ²/c² | 机器精度 |
| SF1 ρ=1 退化保体积（SG2 接轨） | 精确 0 |
| SF2 延拓性（内部 \|det\| 更大） | ✓ |
| SF3 势差 ΔΦ = ½(v_in²−v_out²) | ✓ |
| SF7 边界能 = 压缩能 | ✓ |
| SE5 螺旋场自维持 δ_max | 1.6818 |
| SF8 褶皱更多 ⟹ 内部空间更大（N=1..20 严格递增，N=20 → 400×） | ✓ |
| SF9 势差-密度耦合（ΔΦ 随 ρ_in 单调，α=1） | ✓ |
| SF10 势差大 ⟹ 内部空间大（链条成对样本） | ✓ |
| SF10b 总势差 ΔΦ·S 单调 | ✓ |
| SF11 δ_max ∝ B（δ_max² = νB²V/(κg2) 机器精度） | ✓ |
| FOLD-Q1 固定预算下多褶皱内部更多（N=5 vs N=1） | 14.647 vs 2.874（5.10x） |
| FOLD-Q2 势差驱动 B 放大 δ_max 线性增 | 1.682 → 13.454 |
| FOLD-Q2a 加硬边界层 γ 不改变 δ_max | ✓（需放大驱动强度而非刚度） |

## 4. 与主线的接轨

| 主线概念 | 本方向的对应 |
|---|---|
| SM5/SG2 保体积 `det=−1/c²` | 放松为 `−ρ²/c²+v²(ρ²−1)/c⁴`（SF1） |
| SG11 Φ=½v² 弱场匹配 | 势差 ΔΦ = ½(v_in²−v_out²)（SF3） |
| SF5 B=curl C 自旋涡旋 | 螺旋边界环流（SF6） |
| MC 质量=锚定 | 折叠域 = 质量锚定的几何来源（候选，解释层） |

## 5. 诚实边界

- 严格证明 = **代数恒等 + 序关系**（行列式公式、非负性、单调性、势差）——
  真但平凡（线性代数 + 实数序）。
- 概念重构 = "空间可压缩密度 ⟹ 折叠域"——**解释层**，不可证伪
  （与标准 GR 在 ρ=1 时数值全同，无实验可区分）。
- **ρ 的动力学方程（如何驱动折叠）未给出**——这是最大的缺口。
- **能量常数数值（k/κ/ν/σ/α）仍是第二输入缺口**（与 ℏ/e/m_e 同源）；
  SF9 的耦合常数 α = β²（压缩空间流动更快 v=βρ）是显式公设，数值来源未定。
- **多褶皱 = 径向包络叠加，非严格拓扑**（未建同调/连通数）；
  Q1 的"5.10x"依赖具体的褶皱分布选择（rₖ/wₖ/aₖ），换分布数字会变、方向不变。
- 连续场论、拓扑、能量守恒动力学未形式化。
- 诚实 4 层判定：① 数学恒等（真但平凡）② 结构对应（弹性介质压缩能，
  经典连续介质力学重述）③ 数值匹配（机器精度）④ 概念重构（不可证伪）。
  **无新物理预言**——价值 = 给"空间延拓性"一个可计算的语言，
  与空间流动（SLS/SM）、自旋涡旋（SF）、质量锚定（MC）同体系。

## 6. 下一步候选

1. ρ 的动力学方程（什么驱动空间折叠？接 GQF4 电荷=流散度 / MaxwellSpace 源项）——
   本轮新增线索：**势差-密度耦合 α 与驱动强度 B 的关系**（SF9/SF11 的动力学来源）
2. "质量 = 折叠域"的定量桥（折叠比 δ ⟷ 锚定质量 m，接 MinimalCore）
3. 3D 度规的密度推广（当前 1+1 维）
4. 能量常数 k/κ/α/ν 的第一性来源（第二输入）
5. 多褶皱的严格拓扑化（当前是径向包络叠加，未建同调/连通数——诚实边界）
6. 边界弥散梯度层的积分模型（∫|∇ρ|² dV，SE 层 v2 计划）
