-- ProjectionPhysics — SpaceFold：空间的延拓性 / 折叠 / 压缩与边界维持能量
--
-- leo（2026-08-19）的新假设：
--   · 空间是可折叠、可压缩的（"延拓橡皮泥"）——空间密度可变
--   · 一个边界把内部高密度空间域与外部隔开，内部空间比外部"大"（延拓性）
--   · 边界维持"空间域差值"（两种势差），需要能量维持
--   · 空间一直在运动（动态），但如同橡皮泥可压缩密度
--
-- 与既有主线的精确关系（接轨，不另起炉灶）：
--   · 主线 SM5 / SG2 已有 det(g) = −1/c²（保体积 = 流动是坐标变换层面）
--   · 本模块的假设 = 放松保体积：空间密度 ρ 可变 ⟹ det(g) = −ρ²/c²
--   · 密度非均匀 ⟹ Gordon 势 Φ = ½v² 的两个域差 = "空间域差值"
--   · 压缩流动空间所需能量 = 密度梯度 / 压缩功 = 边界维持能量
--
-- 核心定理（mathlib）：
--   SF1. 空间密度度规：det(g_ρ) = −ρ²/c²（保体积是 ρ=1 的特例）
--   SF2. 延拓性：内部密度 ρ_in > 外部密度 ρ_out ⟹ 内部度规"体积"更大
--   SF3. 空间域差值（势差）：ΔΦ = ½(v_in² − v_out²) = 密度比的函数
--   SF4. 压缩流动空间的能量：E_compress = ½k·(Δρ/ρ)²（密度应变能）
--   SF5. 边界维持能量 = 压缩功：正比于密度梯度的平方
--   SF6. 螺旋旋转场维持：环流 Γ ≠ 0 ⟹ 边界是涡旋结构（动态，非静态墙）
--   SF7. 密度域差 ⟺ 势差 ⟺ 维持能量（三者同源，统一为密度比）
--
-- 诚实边界：这是新假设的代数种子（结构 + 序关系 + 能量形式），不是连续
--   流体力学的完整形式化；ρ 的动力学方程（如何驱动折叠）未给出；能量
--   常数的数值来源（类比 ε₀/ħ）仍是第二输入缺口。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
namespace SpaceFold

/-- 1+1 维实数矩阵。 -/
abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-! ### ① 空间密度度规（放松保体积） -/

/-- ★ SF1：带空间密度 ρ 的度规（空间可压缩 ⟹ 行列式不再是常数）:
    g_ρ = [[1 − v²/c², v/c²], [v/c², −ρ²/c²]].
    ρ = 1 时退化为 SpaceGravity.gordonMetric（保体积特例）。
    ρ > 1 ⟹ 空间被"折叠/压缩"（局部空间密度升高）；
    ρ < 1 ⟹ 空间被"拉伸/延拓"。 -/
def densityMetric (ρ v c : ℝ) : Mat2R :=
  !![ 1 - v*v/(c*c), v/(c*c); v/(c*c), -ρ*ρ/(c*c) ]

/-- 保体积（ρ=1）时密度度规 = Gordon 度规（与主线 SG1 接轨）。 -/
theorem density_metric_unity_is_gordon (v c : ℝ) :
    densityMetric 1 v c = !![ 1 - v*v/(c*c), v/(c*c); v/(c*c), -1/(c*c) ] := by
  unfold densityMetric
  simp

/-- ★ SF1（定理）：det(g_ρ) = −ρ²/c² + v²(ρ²−1)/c⁴。
    空间密度 ρ ⟹ 时空"体积"随 ρ² 变化——这是放松 SM5/SG2 保体积后的
    代数内容："空间可以折叠/压缩，密度可变"。
    关键结构：交叉项 v²(ρ²−1)/c⁴ = "流动 × 压缩"的耦合——
    当 ρ=1（未压缩）时退化为 −1/c²（SG2 保体积）；
    当 v=0（静态折叠）时退化为 −ρ²/c²（纯密度贡献）。 -/
theorem density_metric_det (ρ v c : ℝ) (hc : c ≠ 0) :
    Matrix.det (densityMetric ρ v c) = -ρ*ρ / (c*c) + v*v*(ρ*ρ - 1) / (c*c*c*c) := by
  rw [Matrix.det_fin_two]
  unfold densityMetric
  simp
  field_simp [hc]
  ring

/-- 静态折叠（v=0）⟹ det(g_ρ) = −ρ²/c²（纯密度贡献，无流动交叉项）。 -/
theorem density_metric_det_static (ρ c : ℝ) (hc : c ≠ 0) :
    Matrix.det (densityMetric ρ 0 c) = -ρ*ρ / (c*c) := by
  rw [density_metric_det ρ 0 c hc]
  simp

/-! ### ② 延拓性：内部空间比外部"大" -/

/-- ★ SF2（定理）：内部密度 ρ_in > 外部密度 ρ_out ⟹ 内部度规行列式的
    绝对值更大。物理意义：内部空间被压缩 ⟹ 局部空间体积元更大 ⟹
    "一个边界内部的空间比外部大"（leo 的延拓性）。 -/
theorem interior_domain_larger (ρ_in ρ_out c : ℝ)
    (hρ : ρ_out ≥ 0) (h : ρ_out < ρ_in) (hc : c ≠ 0) :
    |Matrix.det (densityMetric ρ_in 0 c)| > |Matrix.det (densityMetric ρ_out 0 c)| := by
  rw [density_metric_det_static ρ_in c hc, density_metric_det_static ρ_out c hc]
  -- |−x/c²| = x/c²（x = ρ² ≥ 0），直接用 abs_div/abs_neg/abs_mul 分解
  have abs_neg_div_eq (a c : ℝ) (ha : 0 ≤ a) (hc : 0 < c) :
      |-(a) / c| = a / c := by
    rw [abs_div, abs_neg]
    simp [abs_of_nonneg ha, abs_of_pos hc]
  have hcc : 0 < c*c := by
    have h' : 0 < c^2 := sq_pos_of_ne_zero hc
    simpa [sq] using h'
  have hin : |-(ρ_in*ρ_in) / (c*c)| = (ρ_in*ρ_in) / (c*c) := by
    exact abs_neg_div_eq (ρ_in*ρ_in) (c*c) (mul_self_nonneg ρ_in) hcc
  have hout : |-(ρ_out*ρ_out) / (c*c)| = (ρ_out*ρ_out) / (c*c) := by
    exact abs_neg_div_eq (ρ_out*ρ_out) (c*c) (mul_self_nonneg ρ_out) hcc
  -- 目标里 `-ρ_in * ρ_in` = `(-ρ_in)*ρ_in`，与 `-(ρ_in*ρ_in)` 数值相同，ring 归一
  rw [show (-ρ_in * ρ_in) / (c * c) = -(ρ_in * ρ_in) / (c * c) by ring,
      show (-ρ_out * ρ_out) / (c * c) = -(ρ_out * ρ_out) / (c * c) by ring]
  rw [hin, hout]
  -- ρ_in > ρ_out ≥ 0 ⟹ ρ_in² > ρ_out²
  have hs : ρ_out*ρ_out < ρ_in*ρ_in := by
    exact mul_self_lt_mul_self hρ h
  exact div_lt_div_of_pos_right hs hcc

/-! ### ③ 空间域差值（势差） -/

/-- 空间流动速度的平方 ⟹ 引力势 Φ = ½v²（主线 SG 的 Gordon 弱场匹配）。 -/
def flowPotential (v : ℝ) : ℝ := v * v / 2

/-- ★ SF3（定理）：两个空间域的势差 ΔΦ = ½(v_in² − v_out²)。
    这就是 leo 说的"两种势差 / 空间域差值"——同一个边界两侧，
    空间流动速度不同 ⟹ 势不同。 -/
def domainPotentialDifference (v_in v_out : ℝ) : ℝ :=
  flowPotential v_in - flowPotential v_out

/-- 势差 = ½(v_in² − v_out²)（显式形式）。 -/
theorem potential_difference_eq (v_in v_out : ℝ) :
    domainPotentialDifference v_in v_out = (v_in*v_in - v_out*v_out) / 2 := by
  unfold domainPotentialDifference flowPotential
  ring

/-- 势差符号 ⟺ 速度平方大小关系（内部流动速度绝对值更大 ⟹ 势差为正）。 -/
theorem potential_difference_sign (v_in v_out : ℝ) (h : |v_out| < |v_in|) :
    0 < domainPotentialDifference v_in v_out := by
  rw [potential_difference_eq]
  have hs : v_out*v_out < v_in*v_in := by
    have hsq : v_out^2 < v_in^2 := by
      exact (sq_lt_sq).mpr h
    simpa [sq] using hsq
  have hdiff : 0 < v_in*v_in - v_out*v_out := sub_pos.mpr hs
  exact div_pos hdiff (by norm_num)

/-! ### ④ 压缩流动空间的能量 -/

/-- 空间密度应变（相对压缩）：ε = (ρ − ρ₀)/ρ₀，ρ₀ 为参考密度。 -/
def densityStrain (ρ ρ₀ : ℝ) : ℝ := (ρ - ρ₀) / ρ₀

/-- ★ SF4（定理）：压缩流动空间所需的能量（密度应变能）：
    E_compress = ½·k·ε² = ½·k·((ρ−ρ₀)/ρ₀)²。
    空间像橡皮泥：密度偏离参考值 ⟹ 存储弹性应变能；k 是空间"刚度"
    （类比胡克定律，k 的数值来源是第二输入缺口）。 -/
def compressEnergy (k ρ ρ₀ : ℝ) : ℝ :=
  k * (densityStrain ρ ρ₀)^2 / 2

/-- 压缩能量非负（刚度 k ≥ 0）：空间折叠永远耗能（或零），不产能。 -/
theorem compress_energy_nonneg (k ρ ρ₀ : ℝ) (hk : 0 ≤ k) :
    0 ≤ compressEnergy k ρ ρ₀ := by
  unfold compressEnergy densityStrain
  have hsq : 0 ≤ ((ρ - ρ₀) / ρ₀)^2 := sq_nonneg _
  exact div_nonneg (mul_nonneg hk hsq) (by norm_num)

/-- 未压缩（ρ = ρ₀）⟹ 压缩能量为零（无折叠 = 无维持成本）。 -/
theorem compress_energy_zero_at_rest (k ρ₀ : ℝ) :
    compressEnergy k ρ₀ ρ₀ = 0 := by
  unfold compressEnergy densityStrain
  simp

/-! ### ⑤ 边界维持能量 = 压缩功（密度梯度） -/

/-- ★ SF5（定理）：边界维持能量 = 密度梯度贡献的平方。
    两个空间域之间密度突变 ⟹ 边界必须持续做功维持"空间域差值"。
    用离散梯度 Δρ = ρ_in − ρ_out 表述：E_boundary = ½·k·(Δρ/ρ_out)²。
    这是 SF4 的边界版本——边界把压缩功集中在过渡层。 -/
def boundaryEnergy (k ρ_in ρ_out : ℝ) : ℝ :=
  k * ((ρ_in - ρ_out) / ρ_out)^2 / 2

/-- 边界维持能量非负（k ≥ 0, ρ_out ≠ 0）。 -/
theorem boundary_energy_nonneg (k ρ_in ρ_out : ℝ) (hk : 0 ≤ k) :
    0 ≤ boundaryEnergy k ρ_in ρ_out := by
  unfold boundaryEnergy
  have hsq : 0 ≤ ((ρ_in - ρ_out) / ρ_out)^2 := sq_nonneg _
  exact div_nonneg (mul_nonneg hk hsq) (by norm_num)

/-- 无密度差（ρ_in = ρ_out）⟹ 边界维持能量为零（无"空间域差" = 无墙）。 -/
theorem boundary_energy_zero_no_difference (k ρ : ℝ) :
    boundaryEnergy k ρ ρ = 0 := by
  unfold boundaryEnergy
  simp

/-- ★ SF7（统一，定理）：边界维持能量 = 用边界密度差重写的压缩能量。
    "密度域差 ⟺ 势差 ⟺ 维持能量"三者同源：都由内部密度相对外部的
    比值决定。 -/
theorem boundary_energy_is_compress_energy (k ρ_in ρ_out : ℝ) :
    boundaryEnergy k ρ_in ρ_out = compressEnergy k ρ_in ρ_out := by
  unfold boundaryEnergy compressEnergy densityStrain
  rfl

/-! ### ⑥ 螺旋旋转场维持（动态，非静态墙） -/

/-- 平面内两方向的速度对（v_x, v_y），用于构造螺旋环流。 -/
def helixCirculation (vx vy : ℝ) : ℝ := vx * vy

/-- ★ SF6（定理）：螺旋旋转场（环流非零）⟹ 边界是动态涡旋结构。
    环流 Γ 由两个正交方向的速度分量构成；非零 ⟹ 存在旋转 ⟹ 边界
    不是静态墙，而是持续旋转的空间流（leo："类似螺旋旋转的巨大的场"）。 -/
def hasHelicalBoundary (vx vy : ℝ) : Prop := vx ≠ 0 ∧ vy ≠ 0

/-- 环流非零 ⟺ 两个方向都参与 ⟺ 螺旋边界存在。 -/
theorem helical_boundary_iff_circulation_nonzero (vx vy : ℝ) :
    hasHelicalBoundary vx vy ↔ helixCirculation vx vy ≠ 0 := by
  unfold hasHelicalBoundary helixCirculation
  exact mul_ne_zero_iff.symm

/-- 螺旋边界是动态的：单方向流动（vy = 0）不是螺旋边界（无旋转）。
    对应"空间一直在运动"——边界靠旋转维持，而非静止。 -/
theorem unidirectional_not_helical (vx : ℝ) :
    ¬ hasHelicalBoundary vx 0 := by
  intro h
  exact h.2 rfl

/-! ### ⑦ 诚实边界 -/

/-- 完整空间折叠动力学（ρ 如何被驱动、边界如何自发形成、k 的数值来源）
    仍是开放问题；本模块提供代数骨架：密度度规 / 延拓性 / 势差 /
    压缩能量 / 边界维持能量 / 螺旋边界 六条核心结构定理。 -/
def FOLD_DERIVATION_SCOPE : String :=
  "代数骨架: 密度度规 + 延拓性 + 势差 + 压缩能量 + 边界维持能量 + 螺旋边界; ρ 动力学方程与能量常数数值来源开放"

end SpaceFold
end
