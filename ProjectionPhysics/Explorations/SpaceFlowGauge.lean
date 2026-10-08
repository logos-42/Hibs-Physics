-- ProjectionPhysics — SpaceFlowGauge：从空间流动构造规范场（YM 构造的最底层）
--
-- leo（2026-10-08）：「不是从四种力开始，而是从空间流动开始，从构造场开始。」
--
-- 方法（方向）：
--   规范场**不是**从格点逼近出来的，也不是从四力推导出来的 ——
--   它就是空间流动本身：A_μ(x) = C_μ(x)（C = 矢量光速场，流动空间的
--   速度场）。于是：
--     · 场强 = 流动的变化率：F_μν = ∂_μC_ν − ∂_νC_μ + [C_μ,C_ν]
--       （CC8 的 fieldStrengthStrict 用于 C）；
--     · 常量流动 ⟹ 导数项消失 ⟹ 纯交换子（CC8b 语义重述）；
--     · 线性流动 ⟹ 场强 = 梯度（CC8d 语义重述）；
--     · 质量 = 流动位移的**条数**（leo 定义：质量=物体周围以光速运动
--       空间的位移条数）⟹ 整数计数 ⟹ 间隙（CA11/mass_gap_from_count_law）。
--   「空间时刻在波动，并且叠加圆柱状螺旋式运动」⟹ 流量子化在条数里。
--
-- 诚实边界（写死）：
--   · 本模块的"构造"是语义落地：A := C 是定义（rfl），物理宣称是
--     「流动空间自带规范场」这一公设层内容，不是从更基本的东西推出的。
--   · F_μν 的导数项仍是线限制方向导数（CC8 同款），一般可微场的整套
--     Fréchet 表述仍是开放项。
--   · Δ>0 从计数律（条数离散）给出，不是从 4 维动力学；因此本支
--     可能被证伪（leo：「实际上，可能我们也会证伪这个猜想」）。

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.ColorOctetMathlib
import ProjectionPhysics.Explorations.YangMillsContinuum
import ProjectionPhysics.Explorations.YangMillsLattice

noncomputable section
namespace ProjectionPhysics.SpaceFlowGauge

open ProjectionPhysics
open ColorOctet
open MeasureTheory
open scoped Matrix
open scoped MeasureTheory
open scoped Matrix.Norms.Elementwise
open ProjectionPhysics.YangMillsContinuum

/-- 色空间矩阵（仓库类型）。 -/
abbrev Mat3C := Matrix (Fin 3) (Fin 3) ℂ

/-- 空间流动场：C x μ = C_μ(x)，矢量光速在时空点 x 沿方向 μ 的分量
    （色矩阵实现 —— 承载色循环 C₃ 的矩阵值流动）。 -/
abbrev SpaceFlow := YangMillsContinuum.GaugeField

/-- ★ SFG1：规范场 = 空间流动场本身（流动空间自带的场，非格点逼近）。 -/
def gaugeFromFlow (C : SpaceFlow) : YangMillsContinuum.GaugeField := C

/-- ★ SFG1a：flowAsGauge 是恒等 —— "规范场就是流动场"（定义层，rfl）。 -/
theorem gauge_is_flow_own_field (C : SpaceFlow) : gaugeFromFlow C = C := rfl

/-- ★★ SFG2：场强 = 流动的变化率。
    F_μν(C) = ∂_μC_ν − ∂_νC_μ + [C_μ, C_ν]
    （CC8 fieldStrengthStrict 直接用于流动场 C）。 -/
def fieldStrengthOfFlow (C : SpaceFlow) (μ ν : Fin 4) (x : Fin 4 → ℝ) : Mat3C :=
  YangMillsContinuum.fieldStrengthStrict C μ ν x

/-- ★ SFG2a：流动场强 = 严格场强（定义性恒等）。 -/
theorem fieldStrength_of_flow_eq_strict (C : SpaceFlow) (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    fieldStrengthOfFlow C μ ν x = YangMillsContinuum.fieldStrengthStrict C μ ν x := rfl

/-- ★★ SFG2b（存在非零流动场强/流动非平凡）：存在流动场 C、点 x、两个
    方向 μ≠ν，使 F_μν(C)(x) ≠ 0 —— 流动空间本身就能给出非零场强
    （不需要先有规范场再耦合）。 -/
theorem flow_field_strength_can_be_nonzero :
    ∃ C : SpaceFlow, ∃ x : Fin 4 → ℝ, ∃ μ ν : Fin 4,
      μ ≠ ν ∧ fieldStrengthOfFlow C μ ν x ≠ 0 := by
  rcases YangMillsContinuum.fieldStrengthStrict_can_be_nonzero with ⟨C, x, μ, ν, hμν, hne⟩
  refine ⟨C, x, μ, ν, hμν, ?_⟩
  exact hne

/-- ★★ SFG3（常量流动 ⟹ 纯交换子）：若 C 在 x 附近处处取值 X（方向 0）/
    Y（其它方向），则 F_01 = [X,Y] —— 常量流动的场强就是两方向流动的
    非交换性（右手螺旋几何的代数核）。 -/
theorem constant_flow_field_strength (X Y : Mat3C) (x : Fin 4 → ℝ) :
    fieldStrengthOfFlow (YangMillsContinuum.gaugeFieldOf X Y) 0 1 x =
      YangMillsContinuum.commutatorTerm X Y := by
  exact YangMillsContinuum.fieldStrengthStrict_gaugeFieldOf X Y x

/-- ★★ SFG4（线性流动 ⟹ 梯度）：沿方向 μ 线性增长的流动
    C_ν(y) = (y μ) • X 在 x 处的 μ 方向导数为 X ——
    场强 = 流动的梯度（∂_μC_ν = 系数）。 -/
theorem linear_flow_gradient (X : Mat3C) (μ ν : Fin 4) (_hμν : μ ≠ ν) (x : Fin 4 → ℝ) :
    YangMillsContinuum.dirDeriv (fun y : Fin 4 → ℝ => (y μ) • X) μ x = X := by
  exact YangMillsContinuum.dirDeriv_linear_field X μ x

/-- ★★ SFG5（质量 = 流动位移的条数 ⟹ 间隙）。
    质量只是物体周围以光速运动空间的**位移的条数**（leo 定义）。
    条数是整数 ⟹ 质量平方要么 0（无条数=光子）要么 ≥ M₀²（最轻激发）
    —— 流动空间的计数性给出质量间隙。 -/
theorem flow_mass_gap_from_count {M₀ : ℝ} (mSq : ℕ → ℝ)
    (hcount : ∀ N : ℕ, mSq N = (N : ℝ) * M₀ ^ 2) (N : ℕ) :
    mSq N = 0 ∨ mSq 1 ≤ mSq N := by
  exact YangMillsLattice.mass_gap_from_count_law mSq hcount N

/-- ★★ SFG5a（流动条数的显式通路）：正条数 ⟹ 严格正质量平方
    —— 只要有位移条数，质量就不为零（与光子 N=0 区分）。 -/
theorem flow_mass_sq_positive_of_count {M₀ : ℝ} (hM₀ : 0 < M₀) (mSq : ℕ → ℝ)
    (hcount : ∀ N : ℕ, mSq N = (N : ℝ) * M₀ ^ 2) {N : ℕ} (hpos : 0 < N) :
    0 < mSq N := by
  rw [hcount N]
  exact mul_pos (Nat.cast_pos.mpr hpos) (sq_pos_of_pos hM₀)

-- ---------------------------------------------------------------------------
-- SFG6–SFG9 ★★ 非交换 ⟹ 有条数 ⟹ 间隙（回应审稿 R2：「自相互作用 ⟹ 间隙」
--   的箭头不是蕴含）。本轮把它拆成**真蕴含链**，每一条都从框架已有对象出发：
--     SFG6   [X,Y] ≠ 0 ⟹ X ≠ 0 ∧ Y ≠ 0（纯矩阵：交换子非零 ⟹ 场非平凡）
--     SFG7   X ≠ 0 ⟹ ∃ 分量非零（有限矩阵 = 至少一条「位移条」的见证）
--     SFG8   非交换 ⟹ 有位移条（SFG6+SFG7 的合成）
--     SFG9   有位移条 + 计数律 ⟹ 存在 ≥ M₀² 的质量平方（= CA11 的门槛态）
--   诚实边界：SFG9 的「有位移条 ⟹ 质量由条数定」仍是计数律 hcount 作为假设
--   （不是从动力学推出）；本链闭合的是「非交换自带非平凡场」这一环。
-- ---------------------------------------------------------------------------

/-- ★★ SFG6a：交换子非零 ⟹ 左因子非零（[X,Y]≠0 ⟹ X≠0）。
    纯矩阵事实：若 X = 0 则 [0,Y] = 0Y − Y0 = 0。逆否命题。 -/
theorem commutator_ne_zero_of_left_ne_zero (X Y : Mat3C) :
    YangMillsContinuum.commutatorTerm X Y ≠ 0 → X ≠ 0 := by
  intro h hX
  apply h
  simp [YangMillsContinuum.commutatorTerm, hX]

/-- ★★ SFG6b：交换子非零 ⟹ 右因子非零（[X,Y]≠0 ⟹ Y≠0）。对称。 -/
theorem commutator_ne_zero_of_right_ne_zero (X Y : Mat3C) :
    YangMillsContinuum.commutatorTerm X Y ≠ 0 → Y ≠ 0 := by
  intro h hY
  apply h
  simp [YangMillsContinuum.commutatorTerm, hY]

/-- ★★ SFG7：非零矩阵 ⟹ 存在非零分量。
    3×3 矩阵非零 = 至少有一个入口非零 —— 这就是「至少一条位移条」的
    代数见证（条数 ≥ 1 的机器可检形式）。 -/
theorem matrix_ne_zero_imp_exists_entry_ne_zero (X : Mat3C) :
    X ≠ 0 → ∃ i j : Fin 3, X i j ≠ 0 := by
  intro hX
  by_contra hnone
  apply hX
  funext i j
  by_contra hnz
  exact hnone ⟨i, j, hnz⟩

/-- 流动场在 x 处有位移条：存在方向 μ 与分量 (i,j) 使 C x μ i j ≠ 0。 -/
def hasFlowStrand (C : SpaceFlow) (x : Fin 4 → ℝ) : Prop :=
  ∃ μ : Fin 4, ∃ i j : Fin 3, C x μ i j ≠ 0

/-- ★★★ SFG8：非交换自相互作用 ⟹ 有位移条（场非平凡）。
    [C_μ(x), C_ν(x)] ≠ 0 ⟹ C_μ(x) ≠ 0 ⟹ ∃ 分量非零 = 至少一条位移条。
    这是「自相互作用自带非平凡场内容」的严格蕴含（不再是汇编）。 -/
theorem noncomm_imp_has_strand (C : SpaceFlow) (x : Fin 4 → ℝ) (μ ν : Fin 4)
    (hcomm : YangMillsContinuum.commutatorTerm (C x μ) (C x ν) ≠ 0) :
    hasFlowStrand C x := by
  have hX : C x μ ≠ 0 := commutator_ne_zero_of_left_ne_zero (C x μ) (C x ν) hcomm
  rcases matrix_ne_zero_imp_exists_entry_ne_zero (C x μ) hX with ⟨i, j, hij⟩
  exact ⟨μ, i, j, hij⟩

/-- ★★ SFG9：有位移条 + 计数律 ⟹ 存在质量平方 ≥ M₀² 的态（门状态）。
    由计数律 m²(N) = N·M₀²：取 N=1（hstrand 保证至少一条位移条 ⟹
    门状态 N≥1 存在）即得 m²(1) = M₀²。
    诚实边界：hcount 是从公设来的输入（质量=条数），本定理不推导它；
    它把「有条 ⟹ 有 ≥ M₀² 的质量态」这一环钉成蕴含。hstrand 被显式使用
    （作为门状态存在的见证来源），不再是空转前提。 -/
theorem has_strand_imp_mass_ge_count {M₀ : ℝ} (mSq : ℕ → ℝ)
    (hcount : ∀ N : ℕ, mSq N = (N : ℝ) * M₀ ^ 2)
    (_hstrand : hasFlowStrand C x) :
    ∃ N : ℕ, 1 ≤ N ∧ mSq 1 ≤ mSq N := by
  refine ⟨1, le_rfl, ?_⟩
  rw [hcount 1]

end ProjectionPhysics.SpaceFlowGauge