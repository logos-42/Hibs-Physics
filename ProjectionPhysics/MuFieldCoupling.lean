-- ProjectionPhysics — MuFieldCoupling：μ 动力学 ↔ 场控制代数的桥（TD11–TD18）
--
-- 行动手册（2026-09-24）第 2、3 步：把 GravityControl 的 flatten 接进 μ 的状态
-- 更新，并计算交换子——判断控制顺序是否改变 μ 的演化。
--
-- ── 桥的定义（本模块的全部内容） ──────────────────────────────────────
--   μ 的单步增益 η 不从天上掉下来，而由**抹平进展**给出——起伏被消掉的相对比例：
--
--       η = flattenProgress A v v₀ = 1 − Q_A(v) / Q_A(v₀)
--
--   于是"控制场"与"改 μ"不再是两件事：
--     · 抹平一次 ⟹ Q_A = 0 ⟹ η = 1 ⟹ μ 一步到 1（TD12，复用 GCA2c）
--     · 没抹平   ⟹ η = 1 − Q/Q₀ < 1 ⟹ 走不满一步（TD14a）
--     · 顺序差 = (1 − μ)·(1 − η_before)（TD15/TD16）——所以非交换性**不是**
--       抹平本身带来的，而是"μ 更新读场"这一反馈耦合带来的。
--
-- ── 与 GCA6 的关系（两件事，别混） ────────────────────────────────────
--   GCA6：两个**抹平**算子部分重叠 ⟹ 不可交换（两个都改场）；
--   本模块：抹平与 **μ 更新** 的顺序依赖 ⟺ μ 更新读场（反馈耦合）。
--   两者都是"不可交换"，来源不同——这一条是新加的。
--
-- ── 诚实边界 ─────────────────────────────────────────────────────────
--   把 η **定义**成抹平进展是一个**模型选择**，不是从物理推出的。
--   它把第二输入缺口从"η 是哪来的"重述为"抹平功率是哪来的"（TD18）——
--   缺口位置移动了，缺口本身还在。无新物理预言。

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import ProjectionPhysics.GravityControl
import ProjectionPhysics.PlasmaDynamics

set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators
namespace ProjectionPhysics.MuFieldCoupling

open ProjectionPhysics.GravityControl
open PlasmaDynamics

variable {ι : Type} [DecidableEq ι]

/-! ### TD11. 桥：μ 的单步增益 = 抹平进展 -/

/-- ★ TD11（桥）：单步控制增益 η = 起伏被消掉的相对比例。
    Q_A(v) = 现在的起伏能量，Q_A(v₀) = 未控制时的参照起伏能量。
    物理读法：v 是一个离散环/层上的场变量，A 是控制区域（环、层、分离面），
    η 就是"这一步把该区域的褶皱抹掉了多少"。 -/
def flattenProgress (A : Finset ι) (v v₀ : ι → ℝ) : ℝ :=
  1 - fluctuationEnergy A v / fluctuationEnergy A v₀

/-- TD11a：未抹平（v = v₀）⟹ 进展为零（η = 0，μ 原地不动）。 -/
theorem flattenProgress_self (A : Finset ι) (v₀ : ι → ℝ)
    (h0 : fluctuationEnergy A v₀ ≠ 0) : flattenProgress A v₀ v₀ = 0 := by
  unfold flattenProgress
  rw [div_self h0, sub_self]

/-- TD11b：已平坦（Q_A v = 0）⟹ 进展 = 1（满增益 η = 1）。 -/
theorem flattenProgress_flat (A : Finset ι) (v v₀ : ι → ℝ)
    (_h0 : fluctuationEnergy A v₀ ≠ 0) (h : fluctuationEnergy A v = 0) :
    flattenProgress A v v₀ = 1 := by
  unfold flattenProgress
  rw [h, zero_div, sub_zero]

/-- ★★ TD12（核心桥）：抹平一次 ⟹ 进展 = 1。这是把 GravityControl 的投影控制
    接进 μ 状态更新的那一步——直接复用 GCA2c（抹平杀死起伏能量）。 -/
theorem flattenProgress_after_flatten (A : Finset ι) (hA : A.Nonempty) (v v₀ : ι → ℝ)
    (h0 : fluctuationEnergy A v₀ ≠ 0) :
    flattenProgress A (flatten A v) v₀ = 1 :=
  flattenProgress_flat A _ v₀ h0 (flatten_kills_energy A hA v)

/-- ★ TD13（单调）：起伏越小，进展越大（Q 与 η 反向）。 -/
theorem flattenProgress_antitone (A : Finset ι) (v₁ v₂ v₀ : ι → ℝ)
    (h0 : 0 < fluctuationEnergy A v₀)
    (h : fluctuationEnergy A v₁ < fluctuationEnergy A v₂) :
    flattenProgress A v₂ v₀ < flattenProgress A v₁ v₀ := by
  unfold flattenProgress
  have := div_lt_div_of_pos_right h h0
  linarith

/-! ### TD14. 控制顺序：先抹平再更新 μ  vs  先更新 μ 再抹平 -/

/-- 时序 A：先抹平场，再按**抹平后**的场更新 μ。 -/
def muAfterFlatten (A : Finset ι) (v₀ v : ι → ℝ) (μ : ℝ) : ℝ :=
  muStep μ (flattenProgress A (flatten A v) v₀)

/-- 时序 B：先按**当前**场更新 μ（μ 的结果不受之后抹平的影响）。 -/
def muBeforeFlatten (A : Finset ι) (v₀ v : ι → ℝ) (μ : ℝ) : ℝ :=
  muStep μ (flattenProgress A v v₀)

/-- ★★ TD14a（时序 A 的结果）：先抹平 ⟹ 增益被拉到 1 ⟹ μ 一步到 1，
    与初值 μ 和当时的场都无关（只要参照起伏 Q_A(v₀) ≠ 0）。
    这是"控制一次就满"的代数内容；它的代价见 TD18。 -/
theorem muAfterFlatten_eq_one (A : Finset ι) (hA : A.Nonempty) (v₀ v : ι → ℝ)
    (μ : ℝ) (h0 : fluctuationEnergy A v₀ ≠ 0) :
    muAfterFlatten A v₀ v μ = 1 := by
  unfold muAfterFlatten
  rw [flattenProgress_after_flatten A hA v v₀ h0, muStep_full_gain]

/-- ★★ TD15（顺序差，一般形式）：两个时序的差 = 增益差 × 剩余容量：
    muStep μ η₁ − muStep μ η₂ = (η₁ − η₂)(1 − μ)。
    所以**顺序效应只来自增益的差**——增益不读场（η₁ = η₂）⟹ 差为零 ⟹ 可交换。 -/
theorem mu_order_gap (μ η₁ η₂ : ℝ) :
    muStep μ η₁ - muStep μ η₂ = (η₁ - η₂) * (1 - μ) := by
  unfold muStep
  ring

/-- ★★ TD16（顺序效应，显式）：时序 A 给 1、时序 B 给 muStep μ η_before，
    差 = (1 − μ)·(1 − η_before)。场完全没抹平（η_before = 0）时差最大 = 1 − μ。 -/
theorem mu_order_difference (A : Finset ι) (hA : A.Nonempty) (v₀ v : ι → ℝ)
    (μ : ℝ) (h0 : fluctuationEnergy A v₀ ≠ 0) :
    muAfterFlatten A v₀ v μ - muBeforeFlatten A v₀ v μ =
      (1 - μ) * (1 - flattenProgress A v v₀) := by
  unfold muAfterFlatten muBeforeFlatten
  rw [flattenProgress_after_flatten A hA v v₀ h0]
  rw [mu_order_gap]
  ring

/-- ★★★ TD17（不可交换见证——手册第 3 步的直接答案）：
    A = {0,1}（Fin 2 上的"单环"），参照场 v₀ = ![1,0]（初始起伏 = 1/2 ≠ 0），
    当前场 v = v₀（尚未抹平），μ = 0。
      · 先抹平再更新 μ ⟹ μ' = 1（满增益一步到）
      · 先更新 μ 再抹平 ⟹ μ' = 0（增益为零，原地不动）
    **控制顺序改变 μ 的演化**。 -/
theorem mu_order_matters :
    muAfterFlatten ({0, 1} : Finset (Fin 2)) ![1, 0] ![1, 0] 0 ≠
      muBeforeFlatten ({0, 1} : Finset (Fin 2)) ![1, 0] ![1, 0] 0 := by
  have hA : ({0, 1} : Finset (Fin 2)).Nonempty := ⟨0, by simp⟩
  have h0 : fluctuationEnergy ({0, 1} : Finset (Fin 2)) ![1, 0] ≠ 0 := by
    simp [fluctuationEnergy, regionMean]
    norm_num
  have hL := muAfterFlatten_eq_one ({0, 1} : Finset (Fin 2)) hA ![1, 0] ![1, 0] 0 h0
  have hR : muBeforeFlatten ({0, 1} : Finset (Fin 2)) ![1, 0] ![1, 0] 0 = 0 := by
    unfold muBeforeFlatten
    have hp : flattenProgress ({0, 1} : Finset (Fin 2)) ![1, 0] ![1, 0] = 0 :=
      flattenProgress_self _ _ h0
    rw [hp]
    unfold muStep
    ring
  rw [hL, hR]
  norm_num

/-! ### TD18. 诚实落点：缺口移动了，但没有消失 -/

/-- ★★★ TD18（满增益 ⟺ 零代价）：μ 的满增益（η = 1）⟺ 区域内起伏为零，
    而"起伏为零"恰恰是**抹平代价为零**的情形（GCA7b）。
    合并读法：μ 一步到位所需的代价为零，**当且仅当该区域已经平坦**——
    而让区域平坦本身要先付 Q_A(v₀) 的代价（GCA7a）。
    于是第二输入缺口没有消失，它**移动**了：从"η 是哪来的"变成"抹平功率是哪来的"。 -/
theorem full_gain_iff_zero_cost (A : Finset ι) (v v₀ : ι → ℝ) (κ : ℝ)
    (h0 : fluctuationEnergy A v₀ ≠ 0) (hκ : κ ≠ 0) :
    flattenProgress A v v₀ = 1 ↔ flattenCost A v κ = 0 := by
  constructor
  · intro h
    unfold flattenProgress at h
    have hq : fluctuationEnergy A v / fluctuationEnergy A v₀ = 0 := by linarith
    have hQ : fluctuationEnergy A v = 0 := (div_eq_zero_iff.mp hq).resolve_right h0
    exact (flattenCost_eq_zero_iff A v κ hκ).mpr
      ((fluctuationEnergy_eq_zero_iff A v).mp hQ)
  · intro h
    exact flattenProgress_flat A v v₀ h0
      ((fluctuationEnergy_eq_zero_iff A v).mpr ((flattenCost_eq_zero_iff A v κ hκ).mp h))

/-! ### TD19–TD21. 接到 FRC 的窗口判定与锁定关系（手册第 4 步）

μ 动力学不是孤立的：FRC 的两条已证结论直接读 μ 的**轨道**——
FC11b（RMF 窗口存在 ⟺ m_e < m_eff，窗口关闭 ⟺ μ ≥ 1 − m_e/m_i）与
FC5b（μ 标度因子 = 1/√(1−μ)，同时作用于 S* 与 τ_E）。

本节的接法：把 μ_n 的轨道代入这两条，得到**单调性与良定义性**两个可算结论。 -/

/-- ★ TD19（窗口余量单调收窄）：m_eff,n = m_i(1−μ_n) 沿轨道**严格递减**。
    接 FC11b：RMF 窗口的余量每步都更小，**不会自行恢复**——
    想让窗口重新打开只能靠反向控制（η < 0 或重设 μ）。 -/
theorem rmf_margin_strictly_decreasing (m_i μ η : ℝ) (hmi : 0 < m_i)
    (hμ : μ < 1) (hη0 : 0 < η) (hη1 : η < 1) :
    ∀ n : ℕ, m_i * (1 - muChain μ η (n + 1)) < m_i * (1 - muChain μ η n) := by
  intro n
  have hlt := muChain_strict_mono μ η hμ hη0 hη1 n
  nlinarith [hmi]

/-- ★★ TD20（锁定因子良定义）：FC5b 的 μ 标度因子 1/√(1−μ_n) 在整个轨道上
    **分母永不为零**（TD8 的直接后果）——锁定的"死点"是渐近的，不可达。 -/
theorem mu_scaling_well_defined (μ η : ℝ) (hμ : μ < 1) (hη0 : 0 < η) (hη1 : η < 1) :
    ∀ n : ℕ, 0 < 1 - muChain μ η n := by
  intro n
  have hlt := muChain_lt_one μ η hμ hη0 hη1 n
  linarith

/-- ★★ TD20b（锁定因子单调递增）：1/√(1−μ_n) 每步都更大——轨道**单调逼近**
    S*/τ_E 锁定的发散点，但每一步都有限（TD20）。 -/
theorem mu_scaling_strictly_increasing (μ η : ℝ) (hμ : μ < 1) (hη0 : 0 < η)
    (hη1 : η < 1) :
    ∀ n : ℕ,
      1 / Real.sqrt (1 - muChain μ η (n + 1)) > 1 / Real.sqrt (1 - muChain μ η n) := by
  intro n
  have hpos_n : 0 < 1 - muChain μ η n := mu_scaling_well_defined μ η hμ hη0 hη1 n
  have hpos_n1 : 0 < 1 - muChain μ η (n + 1) :=
    mu_scaling_well_defined μ η hμ hη0 hη1 (n + 1)
  have hlt : 1 - muChain μ η (n + 1) < 1 - muChain μ η n := by
    have := muChain_strict_mono μ η hμ hη0 hη1 n
    linarith
  have hsqrt : Real.sqrt (1 - muChain μ η (n + 1)) < Real.sqrt (1 - muChain μ η n) :=
    Real.sqrt_lt_sqrt (le_of_lt hpos_n1) hlt
  exact one_div_lt_one_div_of_lt (Real.sqrt_pos.2 hpos_n1) hsqrt

/-- ★★ TD21（窗口关闭步的可算判据）：把闭式解代入 FC11b 阈值——
    `1 − m_e/m_i ≤ μ_n  ⟺  (1−η)^n (1−μ₀) ≤ m_e/m_i`。
    右边是纯代数式：给定 η 与初始 μ₀ 就能算**第几步窗口关闭**（工程侧可用）。 -/
theorem rmf_window_threshold_iff (m_e m_i μ η : ℝ) (n : ℕ) :
    (1 - m_e / m_i ≤ muChain μ η n ↔ (1 - η) ^ n * (1 - μ) ≤ m_e / m_i) := by
  rw [muChain_closed_form]
  constructor <;> intro h <;> linarith

def MU_FIELD_COUPLING_SCOPE : String :=
  "μ↔场控制桥: 增益=抹平进展 η=1−Q_A(v)/Q_A(v₀)(TD11) + 抹平一次⟹η=1⟹μ一步到1(TD12,复用GCA2c) + Q与η反向(TD13) + 顺序差=(1−μ)(1−η_before)(TD15/TD16) + 不可交换见证:先抹平后更新μ'=1 vs 先更新后抹平μ'=0(Fin2,TD17) + 满增益⟺零代价⟺区域已平坦(TD18) + FRC接缝(TD19 窗口余量单调收窄/TD20 锁定因子良定义+单调增/TD21 窗口关闭步判据); GCA6(两抹平算子)与本模块(抹平vs μ更新)是两种不同来源的不可交换; 缺口移动(不是消失): η物理来源⟹抹平功率来源; 无新物理预言"

end ProjectionPhysics.MuFieldCoupling
