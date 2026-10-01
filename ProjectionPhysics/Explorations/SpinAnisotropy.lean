-- ProjectionPhysics — SpinAnisotropy：自旋能不能当旋钮用？（SA1–SA9）
--
-- leo：能不能把这个自旋拿来做应用（专门做自旋的应用）。
--
-- 本模块做两件事：第一件「钉边界」，第二件「开一个口并把它的死法写清」。
--
-- ── ① 钉边界（把现状写成定理，以后谁也绕不过） ────────────────────────────
--   仓库现有的锚定定义两处：
--     · SpaceLightSpeed.lean  anchorMassOf = Int.natAbs s.spin + |relative.x| + |y| + |z|
--       ⟹ 只有**绝对值**（方向被 natAbs 吃掉）
--     · MinimalCoreMathlib    anchorMassSq ψ = ‖σ₁ψ‖² = |ψ₁|² + |ψ₀|²
--       ⟹ 这是**旋量范数**，而 σ₁ 是酉的
--   本模块证明：锚定 = 总范数平方（SA1），因此对 σ₁（SA2）、σ₃（SA3）、σ₂（SA4）
--   三个自旋转动生成元**全都不变**，于是两个自旋态**质量简并**（SA5）。
--   ⟹ **自旋方向不进入质量。** 这就是为什么「自旋的应用」目前为零——不是没做，
--      是**结构上没有开口**。把这条写成定理，是为了让后来人不能靠改措辞绕过它。
--   诚实边界：一般 SU(2) 元的酉性未形式化（需要任意 2×2 酉矩阵）；本模块证的是
--   三个生成元 + 全局相位（SA6）——即「方向」这个自由度的全部生成方向，够用且便宜。
--
-- ── ② 开一个口（新假设，带自己的死法） ────────────────────────────────────
--   仓库已有接口：B = curl C（SF5）；FM9 ω₀ = CurlZ/2；FM10 ω₀ = B_z/2
--   ⟹ **空间流动的涡度轴就是 B 的方向**，所以「自旋轴 vs B 的夹角」是现成的可观测量。
--
--   最小扩展：anchoredMass s ε θ := s·(1 + ε·cos θ)，θ = 自旋轴与 B 的夹角，ε = 新耦合。
--   合法性：依赖的是**相对夹角** ⟹ 自旋与流动一起转动时不变 ⟹ 不破坏转动不变性 ✓；
--           它破坏单独的自旋转动 ⟹ 与「磁场挑出一个轴」同类，磁化等离子体本就不各向同性 ✓
--
--   ★ 这是**新假设（模型选择），不是推导**，按仓库规矩它必须带着自己的死法：
--     **ε = 0 ⟺ 两个自旋态质量相同 ⟺ 无任何可观测效应（SA7）**。
--   与既有判决量 D1（R_ci = 1/(1−μ) − 1，生死门 G1/M6）合流：
--     ★★ 自旋分辨的 D1 劈裂 = −2ε/((1−μ)(1−ε²))（SA8），其大小 ≥ 2ε（SA9）
--     ⟹ 「μ 越大（越接近判决门槛）自旋轴越容易看见」——与 D1 判决**同向**，不是竞争。
--
--   诚实边界：**ε 是被测的量，不是被预言的量。** 本模块给的是「劈裂的形式 + 死法」，
--   不是数值预言。属判决类（档 3），不属推导类（档 1/2）。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ProjectionPhysics.MinimalCoreMathlib

noncomputable section

namespace ProjectionPhysics.SpinAnisotropy

open MinimalCoreMathlib
open Matrix

/-- Fin 2 的两个下标（用 abbrev：可约展开，保证与 MinimalCoreMathlib 里
    `⟨0, by decide⟩` / `⟨1, by decide⟩` 的写法定义等价）。 -/
abbrev i0 : Fin 2 := ⟨0, by decide⟩
abbrev i1 : Fin 2 := ⟨1, by decide⟩

-- ---------------------------------------------------------------------------
-- ① 钉边界：锚定是范数 ⟹ 自旋方向不进入质量
-- ---------------------------------------------------------------------------

/-- ★ SA1：锚定质量平方 = 总范数平方 |ψ₁|² + |ψ₀|²。
    ——把「锚定其实只是范数」这件事显式写出来；下面的不变性全是它的推论。 -/
theorem anchor_massSq_eq_sum (ψ : Spinor) :
    anchorMassSq ψ = Complex.normSq (ψ i1) + Complex.normSq (ψ i0) := by
  unfold anchorMassSq
  rw [spinFlow_0, spinFlow_1]

/-- ★ SA2：锚定对 σ₁（x 方向自旋转动）**不变**。 -/
theorem anchor_sigma1_blind (ψ : Spinor) :
    anchorMassSq (σ₁.mulVec ψ) = anchorMassSq ψ := by
  rw [anchor_massSq_eq_sum, anchor_massSq_eq_sum]
  have h0 : (σ₁.mulVec ψ) i0 = ψ i1 := by
    change (∑ j : Fin 2, σ₁ i0 j * ψ j) = ψ i1
    simp [σ₁, Fin.sum_univ_two]
  have h1 : (σ₁.mulVec ψ) i1 = ψ i0 := by
    change (∑ j : Fin 2, σ₁ i1 j * ψ j) = ψ i0
    simp [σ₁, Fin.sum_univ_two]
  rw [h0, h1]
  ring

/-- ★ SA3：锚定对 σ₃（z 方向 / 法向量方向自旋转动）**不变**。
    σ₃ = diag(1,−1) ⟹ ψ₁ ↦ −ψ₁，而 normSq(−z) = normSq z。 -/
theorem anchor_sigma3_blind (ψ : Spinor) :
    anchorMassSq (σ₃.mulVec ψ) = anchorMassSq ψ := by
  rw [anchor_massSq_eq_sum, anchor_massSq_eq_sum]
  have h0 : (σ₃.mulVec ψ) i0 = ψ i0 := by
    change (∑ j : Fin 2, σ₃ i0 j * ψ j) = ψ i0
    simp [σ₃, Fin.sum_univ_two]
  have h1 : (σ₃.mulVec ψ) i1 = -ψ i1 := by
    change (∑ j : Fin 2, σ₃ i1 j * ψ j) = -ψ i1
    simp [σ₃, Fin.sum_univ_two]
  rw [h0, h1, Complex.normSq_neg]

/-- ★ SA4：锚定对 σ₂（y 方向自旋转动）**不变**。
    σ₂ψ = (−i·ψ₁, i·ψ₀)，而 normSq(−i·z) = normSq z。 -/
theorem anchor_sigma2_blind (ψ : Spinor) :
    anchorMassSq (σ₂.mulVec ψ) = anchorMassSq ψ := by
  rw [anchor_massSq_eq_sum, anchor_massSq_eq_sum]
  have h0 : (σ₂.mulVec ψ) i0 = -Complex.I * ψ i1 := by
    change (∑ j : Fin 2, σ₂ i0 j * ψ j) = -Complex.I * ψ i1
    simp [σ₂, Fin.sum_univ_two]
  have h1 : (σ₂.mulVec ψ) i1 = Complex.I * ψ i0 := by
    change (∑ j : Fin 2, σ₂ i1 j * ψ j) = Complex.I * ψ i0
    simp [σ₂, Fin.sum_univ_two]
  rw [h0, h1]
  simp [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I]
  ring

/-- 自旋「上」态（分量 0 被占据）。 -/
def spinUp : Spinor := fun i => if i = i0 then 1 else 0

/-- 自旋「下」态（分量 1 被占据）。 -/
def spinDown : Spinor := fun i => if i = i0 then 0 else 1

/-- ★ SA5：**两个自旋态质量简并**——这是「自旋不能当旋钮」的最锋利形式，
    也是实验要检验的**零假设**（标准 MHD 也预言无劈裂）。 -/
theorem up_down_degenerate : anchorMassSq spinUp = anchorMassSq spinDown := by
  rw [anchor_massSq_eq_sum, anchor_massSq_eq_sum]
  have hu0 : spinUp i0 = 1 := by unfold spinUp; rw [if_pos rfl]
  have hu1 : spinUp i1 = 0 := by unfold spinUp; rw [if_neg (by decide)]
  have hd0 : spinDown i0 = 0 := by unfold spinDown; rw [if_pos rfl]
  have hd1 : spinDown i1 = 1 := by unfold spinDown; rw [if_neg (by decide)]
  rw [hu0, hu1, hd0, hd1, Complex.normSq_zero, Complex.normSq_one]
  norm_num

/-- ★ SA6：锚定对全局相位**不变**（|z| = 1 时）：相位也不是「方向」。 -/
theorem anchor_phase_blind (ψ : Spinor) (z : ℂ) (hz : Complex.normSq z = 1) :
    anchorMassSq (fun i => z * ψ i) = anchorMassSq ψ := by
  rw [anchor_massSq_eq_sum, anchor_massSq_eq_sum, Complex.normSq_mul, Complex.normSq_mul, hz]
  ring

-- ---------------------------------------------------------------------------
-- ② 开口：夹角敏感版（新假设）
-- ---------------------------------------------------------------------------

/-- 夹角敏感锚定：θ = 自旋轴与流动涡度轴（= B 方向）的夹角，ε = 新耦合常数。
    ε = 0 退回各向同性（= ① 的现状）。 -/
def anchoredMass (s ε θ : ℝ) : ℝ := s * (1 + ε * Real.cos θ)

/-- ↑ 态（θ = 0，自旋平行 B）。 -/
theorem anchoredMass_up (s ε : ℝ) : anchoredMass s ε 0 = s * (1 + ε) := by
  unfold anchoredMass; rw [Real.cos_zero]; ring

/-- ↓ 态（θ = π，自旋反平行 B）。 -/
theorem anchoredMass_down (s ε : ℝ) : anchoredMass s ε Real.pi = s * (1 - ε) := by
  unfold anchoredMass; rw [Real.cos_pi]; ring

/-- 垂直（θ = π/2）：各向同性点，与 ε 无关。 -/
theorem anchoredMass_isotropic (s ε : ℝ) :
    anchoredMass s ε (Real.pi / 2) = s := by
  unfold anchoredMass; rw [Real.cos_pi_div_two]; ring

/-- 两个自旋态的有效质量比 m↓/m↑（= ω_ci↑/ω_ci↓，因 FC9 ω_ci ∝ 1/m_eff）。 -/
def spinMassRatio (ε : ℝ) : ℝ := (1 + ε) / (1 - ε)

/-- ★ SA7（死法）：**ε = 0 ⟹ 两个自旋态质量相同 ⟹ 无任何可观测效应。**
    —— 这就是本假设的失败判据：实验测到「劈裂与极化无关」即落在此条。 -/
theorem spinMassRatio_zero : spinMassRatio 0 = 1 := by
  unfold spinMassRatio; norm_num

/-- ★ 任何 0 < ε < 1 都给出严格的质量劈裂（原理上可测）。 -/
theorem spinMassRatio_gt_one (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    1 < spinMassRatio ε := by
  unfold spinMassRatio
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 1 - ε)]
  linarith

/-- ★★ 「劈裂 = 2ε」的严格形式：比值超出 1 的部分 ≥ 2ε（一阶精确，高阶更大）。 -/
theorem two_eps_le_spinMassRatio_sub_one (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) :
    2 * ε ≤ spinMassRatio ε - 1 := by
  have hpos : (0 : ℝ) < 1 - ε := by linarith
  have hkey : spinMassRatio ε - 1 = 2 * ε / (1 - ε) := by
    unfold spinMassRatio
    field_simp
    ring
  rw [hkey, le_div_iff₀ hpos]
  -- 显式构造 2ε ≥ 0（把 h0 真正用进证明项，避免 unused variable 警告）
  have h2ε : (0 : ℝ) ≤ 2 * ε := by linarith
  nlinarith [h2ε, sq_nonneg ε]

-- ---------------------------------------------------------------------------
-- ③ 与既有判决量 D1 合流
-- ---------------------------------------------------------------------------

/-- D1 判决量（既有）：回旋共振相对频移 R_ci = 1/(1−μ) − 1（生死门 G1/M6）。 -/
def Rci (μ : ℝ) : ℝ := 1 / (1 - μ) - 1

/-- 加自旋轴后的 D1：m_eff = s(1−μ)(1 + ε·cos θ)，ω_ci ∝ 1/m_eff。 -/
def RciAt (μ ε θ : ℝ) : ℝ := 1 / ((1 - μ) * (1 + ε * Real.cos θ)) - 1

theorem RciAt_up (μ ε : ℝ) : RciAt μ ε 0 = 1 / ((1 - μ) * (1 + ε)) - 1 := by
  unfold RciAt; rw [Real.cos_zero]; ring_nf

theorem RciAt_down (μ ε : ℝ) : RciAt μ ε Real.pi = 1 / ((1 - μ) * (1 - ε)) - 1 := by
  unfold RciAt; rw [Real.cos_pi]; ring_nf

/-- 垂直取向退回各向同性的 D1。 -/
theorem RciAt_isotropic (μ ε : ℝ) : RciAt μ ε (Real.pi / 2) = Rci μ := by
  unfold RciAt Rci; rw [Real.cos_pi_div_two]; ring

/-- ★★ SA8：**自旋分辨的 D1 劈裂 = −2ε/((1−μ)(1−ε²))** ——本应用的核心数。 -/
theorem Rci_spin_split (μ ε : ℝ) (hμ : μ < 1) (hε : ε * ε < 1) :
    RciAt μ ε 0 - RciAt μ ε Real.pi = -2 * ε / ((1 - μ) * (1 - ε * ε)) := by
  rw [RciAt_up, RciAt_down]
  have hlt1 : ε < 1 := by nlinarith [sq_nonneg (ε - 1)]
  have hgt1 : -1 < ε := by nlinarith [sq_nonneg (ε + 1)]
  have hμ' : (1 : ℝ) - μ ≠ 0 := by linarith
  have hp : (1 : ℝ) + ε ≠ 0 := by linarith
  have hm : (1 : ℝ) - ε ≠ 0 := by linarith
  have hsq : (1 : ℝ) - ε ^ 2 ≠ 0 := by nlinarith [sq_nonneg ε]
  have ha : (1 - μ) * (1 + ε) ≠ 0 := mul_ne_zero hμ' hp
  have hb : (1 - μ) * (1 - ε) ≠ 0 := mul_ne_zero hμ' hm
  have hc : (1 - μ) * (1 - ε ^ 2) ≠ 0 := mul_ne_zero hμ' hsq
  field_simp [ha, hb, hc, hμ', hp, hm, hsq]
  ring

/-- ★★ SA9：劈裂 ≥ 2ε ⟹ **μ 越大（越接近判决门槛）自旋轴越容易看见**——
    所以它与 D1 判决方向**同向**，不是竞争关系。（这是它比别的附加轴都好的地方。） -/
theorem spin_split_amplified (μ ε : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    2 * ε ≤ RciAt μ ε Real.pi - RciAt μ ε 0 := by
  have hεsq : ε * ε < 1 := by nlinarith [hε0, hε1]
  have hsplit := Rci_spin_split μ ε hμ1 hεsq
  have hden_pos : 0 < (1 - μ) * (1 - ε * ε) :=
    mul_pos (by linarith) (by nlinarith [sq_nonneg ε])
  have hden_le : (1 - μ) * (1 - ε * ε) ≤ 1 := by
    nlinarith [hμ0, sq_nonneg ε, mul_nonneg hμ0.le (sq_nonneg ε)]
  have hgoal : RciAt μ ε Real.pi - RciAt μ ε 0
      = 2 * ε / ((1 - μ) * (1 - ε * ε)) := by
    rw [show RciAt μ ε Real.pi - RciAt μ ε 0
          = -(RciAt μ ε 0 - RciAt μ ε Real.pi) by ring, hsplit]
    ring
  rw [hgoal, le_div_iff₀ hden_pos]
  have hprod : 2 * ε * ((1 - μ) * (1 - ε * ε)) ≤ 2 * ε * 1 :=
    mul_le_mul_of_nonneg_left hden_le (by linarith : (0 : ℝ) ≤ 2 * ε)
  linarith

/-- ★ 两种「看不见」的方式：耦合为零（ε=0）**或**取向垂直（cos θ = 0）。
    （非退化条件 1 + ε·cos θ ≠ 0 是必要的：它为零时质量完全取消，是退化情形。） -/
theorem spin_effect_vanishes_iff (μ ε θ : ℝ) (hμ : μ < 1)
    (hx : 1 + ε * Real.cos θ ≠ 0) :
    RciAt μ ε θ = Rci μ ↔ ε * Real.cos θ = 0 := by
  have hμ' : (1 : ℝ) - μ ≠ 0 := by linarith
  have hden : (1 - μ) * (1 + ε * Real.cos θ) ≠ 0 := mul_ne_zero hμ' hx
  have hmain : RciAt μ ε θ = Rci μ ↔
      1 / ((1 - μ) * (1 + ε * Real.cos θ)) = 1 / (1 - μ) := by
    unfold RciAt Rci
    constructor <;> intro h <;> linarith
  rw [hmain, div_eq_div_iff hden hμ']
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]; ring

end ProjectionPhysics.SpinAnisotropy
