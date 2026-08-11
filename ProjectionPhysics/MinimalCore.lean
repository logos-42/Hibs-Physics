-- ProjectionPhysics — Minimal Core（最小核心命题，旋量流锚定版）
--
-- 质量默认有量的结构：它不是场的激发能量，而是物质为抵抗空间本身的
-- 运动产生的锚定效果。内部运动状态——自旋本身——就是运动状态，不需要
-- 空间位移差来描述。
--
-- 最简推导（四步）：
--   内部运动状态 s（自旋：Clifford 生成元 σ 作用在旋量 ψ 上的流 σψ）
--   → 空间运动 F（空间本身的运动）
--   → 质量 m := 锚定效果（旋量流的分量范数：对空间运动的抵抗）
--   → 自旋非零 ⟹ m ≠ 0
--
-- 适用对象：胶子、夸克、电子——任何有自旋（内部运动）的物质。
-- 电子有电荷（"电"），但质量来自自旋对空间运动的抵御。
-- 光子边界：无自旋（零旋量）⟹ 零锚定 ⟹ 无质量。
-- 0++ 胶球：总角动量 J=0 但内部是两个自旋-1 胶子 ⟹ 内部运动非零 ⟹ 有质量。
--
-- 诚实边界：以上是质量候选的代数锚定，不是实验质量、QCD 质量或
-- MeV 数值。连续时空、规范场动力学、禁闭、色动力学均为后续扩展。

import ProjectionPhysics.Clifford
import ProjectionPhysics.HiddenOnlyHiggs
import ProjectionPhysics.GlueballBridge

namespace ProjectionPhysics

instance : Zero Spinor := ⟨⟨0, 0⟩⟩

/-! ### MC1. 旋量流锚定：自旋本身就是内部运动状态 -/

/-- 内部运动状态：旋量 ψ 在自旋算子 σ 作用下的流 σψ。
    自旋是运动，不是静态属性；流的分量就是抵抗空间运动的量。 -/
def spinFlow (σ : Mat2) (ψ : Spinor) : Spinor :=
  matMulSpinor σ ψ

/-- 单个 ℂ 分量的范数（|re| + |im|）。 -/
def componentNorm (z : ℂ) : Nat :=
  Int.natAbs z.re + Int.natAbs z.im

/-- 锚定质量候选：旋量流 σψ 的四分量范数之和。
    它是"抵抗空间运动的锚定效果"，不是场的激发能量。 -/
def spinFlowAnchorMass (σ : Mat2) (ψ : Spinor) : Nat :=
  componentNorm (spinFlow σ ψ).ψ₁ + componentNorm (spinFlow σ ψ).ψ₂

/-- ℂ 非零 ⟹ re 或 im 非零。 -/
theorem complex_nonzero_has_component (z : ℂ) (hz : z ≠ 0) :
    z.re ≠ 0 ∨ z.im ≠ 0 := by
  by_cases hr : z.re = 0
  · by_cases hi : z.im = 0
    · exfalso
      apply hz
      apply ℂ.ext
      · exact hr
      · exact hi
    · exact Or.inr hi
  · exact Or.inl hr

/-- 非零 ℂ 分量的范数为正。 -/
theorem componentNorm_pos_of_nonzero (z : ℂ) (hz : z ≠ 0) :
    0 < componentNorm z := by
  rcases complex_nonzero_has_component z hz with hr | hi
  · have hnr : Int.natAbs z.re ≠ 0 := Int.natAbs_ne_zero.mpr hr
    have hpos : 0 < Int.natAbs z.re := Nat.pos_of_ne_zero hnr
    unfold componentNorm
    omega
  · have hni : Int.natAbs z.im ≠ 0 := Int.natAbs_ne_zero.mpr hi
    have hpos : 0 < Int.natAbs z.im := Nat.pos_of_ne_zero hni
    unfold componentNorm
    omega

/-- 非零旋量流 ⟹ 至少一个分量非零。 -/
theorem spinor_nonzero_has_component (s : Spinor) (hs : s ≠ 0) :
    s.ψ₁ ≠ 0 ∨ s.ψ₂ ≠ 0 := by
  by_cases h1 : s.ψ₁ = 0
  · by_cases h2 : s.ψ₂ = 0
    · exfalso
      apply hs
      apply Spinor.ext
      · exact h1
      · exact h2
    · exact Or.inr h2
  · exact Or.inl h1

/-- 自旋算子作用在零旋量上仍为零（线性）。 -/
theorem matMulSpinor_zero (M : Mat2) : matMulSpinor M 0 = 0 := by
  change matMulSpinor M (⟨0, 0⟩ : Spinor) = (⟨0, 0⟩ : Spinor)
  apply Spinor.ext <;> apply ℂ.ext <;>
    simp [matMulSpinor, ℂ.mul_re, ℂ.mul_im,
      ℂ.ofNat0_re, ℂ.ofNat0_im] <;> omega

/-- σ₁² = I（来自 Clifford C1）⟹ σ₁ 作用在旋量上保持非零性：
    非零旋量在 σ₁ 下的流非零（自旋作用不消灭内部运动）。 -/
theorem spin_flow_sigma1_nonzero_of_spinor_nonzero
    (ψ : Spinor) (hψ : ψ ≠ 0) :
    spinFlow σ₁ ψ ≠ 0 := by
  intro h0
  apply hψ
  -- ψ = σ₁(σ₁ψ)（σ₁² = I 与表示同态）
  have hinv : matMulSpinor σ₁ (matMulSpinor σ₁ ψ) = ψ := by
    rw [← spinor_rep_hom σ₁ σ₁ ψ, sigma1_sq]
    apply Spinor.ext <;> apply ℂ.ext <;>
      simp [matMulSpinor, ℂ.mul_re, ℂ.mul_im,
        ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega
  have h0' : matMulSpinor σ₁ ψ = 0 := by
    simpa [spinFlow] using h0
  rw [← hinv]
  rw [h0']
  exact matMulSpinor_zero σ₁

/-- 非零旋量 ⟹ 锚定质量为正：内部运动非零 ⟹ 抵抗空间运动的锚定非零。 -/
theorem spin_flow_anchor_mass_pos_of_spinor_nonzero
    (ψ : Spinor) (hψ : ψ ≠ 0) :
    0 < spinFlowAnchorMass σ₁ ψ := by
  have hsf : spinFlow σ₁ ψ ≠ 0 := spin_flow_sigma1_nonzero_of_spinor_nonzero ψ hψ
  have hcomp : (spinFlow σ₁ ψ).ψ₁ ≠ 0 ∨ (spinFlow σ₁ ψ).ψ₂ ≠ 0 :=
    spinor_nonzero_has_component (spinFlow σ₁ ψ) hsf
  unfold spinFlowAnchorMass
  rcases hcomp with h1 | h2
  · have hp := componentNorm_pos_of_nonzero (spinFlow σ₁ ψ).ψ₁ h1
    omega
  · have hp := componentNorm_pos_of_nonzero (spinFlow σ₁ ψ).ψ₂ h2
    omega

/-- 光子边界：零旋量（无自旋）⟹ 锚定质量为零。
    "摆脱空间运动锚定"的激发场粒子质量为零。 -/
theorem spin_flow_anchor_mass_zero_of_zero_spinor :
    spinFlowAnchorMass σ₁ (⟨0, 0⟩ : Spinor) = 0 := by
  unfold spinFlowAnchorMass spinFlow componentNorm
  simp [matMulSpinor, σ₁, ℂ.mul_re, ℂ.mul_im,
    ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im]

/-! ### MC1h. 隐数实现：自旋锚定质量的核方向表达 -/

/-- 隐数实现：自旋状态编码为核方向（隐数 h ∈ ker Re），
    锚定质量平方 = 隐数内部量的平方。 -/
def hiddenSpinAnchorMassSquared (h : PureHiddenNumber) : Int :=
  h.value * h.value

/-- 隐数版：非零自旋状态（非零隐数）⟹ 锚定质量平方非零。 -/
theorem hidden_spin_anchor_mass_squared_nonzero
    (h : PureHiddenNumber) (hh : h.value ≠ 0) :
    hiddenSpinAnchorMassSquared h ≠ 0 := by
  change h.value * h.value ≠ 0
  exact Int.mul_ne_zero hh hh

/-- 隐数版光子边界：零自旋状态 ⟹ 锚定质量平方为零。 -/
theorem hidden_spin_anchor_mass_squared_zero_of_zero :
    hiddenSpinAnchorMassSquared ⟨0⟩ = 0 := by
  rfl

/-! ### MC2. 胶球：三胶子内部运动状态的色单态组合 -/

/-- G = (a, b, c)，color profile = (1, 1, 1)：三个胶子的内部运动状态
    （a, b, c）组成色单态。 -/
def minimalTripletGlueball (a b c : PureHiddenNumber) : Glueball :=
  tripletScalarGlueball a b c

theorem minimal_triplet_glueball_is_singlet (a b c : PureHiddenNumber) :
    ColorSinglet (minimalTripletGlueball a b c).configuration.colorProfile := by
  simpa [minimalTripletGlueball] using triplet_scalar_glueball_is_singlet a b c

/-- 锚定质量平方 = |a|² + |b|² + |c|²：三分量内部运动状态的平方和。
    格点胶球谱 m²(2++)/m²(0++) ≈ 2 与 m² = N·M₀²（N 整数模式数）相容。 -/
theorem triplet_glueball_mass_squared_formula (a b c : PureHiddenNumber) :
    pureGlueMassSquared (minimalTripletGlueball a b c) =
      Int.ofNat (Int.natAbs a.value * Int.natAbs a.value +
                 Int.natAbs b.value * Int.natAbs b.value +
                 Int.natAbs c.value * Int.natAbs c.value) := by
  simp [minimalTripletGlueball, pureGlueMassSquared, tripletScalarGlueball,
    configurationFieldEnergy, gluonModeEnergy]
  ac_rfl

/-- a, b, c 至少一个内部运动状态非零 ⟹ 锚定质量平方 > 0。 -/
theorem triplet_glueball_mass_squared_positive_of_any_nonzero
    (a b c : PureHiddenNumber)
    (h : a.value ≠ 0 ∨ b.value ≠ 0 ∨ c.value ≠ 0) :
    0 < pureGlueMassSquared (minimalTripletGlueball a b c) := by
  have hnz : pureGlueMassSquared (minimalTripletGlueball a b c) ≠ 0 := by
    rcases h with ha | hb | hc
    · exact pure_glue_mass_squared_nonzero_of_nonzero_mode
        (minimalTripletGlueball a b c) ⟨a, .c0⟩
          (by simp [minimalTripletGlueball, tripletScalarGlueball]) ha
    · exact pure_glue_mass_squared_nonzero_of_nonzero_mode
        (minimalTripletGlueball a b c) ⟨b, .c1⟩
          (by simp [minimalTripletGlueball, tripletScalarGlueball]) hb
    · exact pure_glue_mass_squared_nonzero_of_nonzero_mode
        (minimalTripletGlueball a b c) ⟨c, .c2⟩
          (by simp [minimalTripletGlueball, tripletScalarGlueball]) hc
  have hnneg : 0 ≤ pureGlueMassSquared (minimalTripletGlueball a b c) :=
    pure_glue_mass_squared_is_nonnegative (minimalTripletGlueball a b c)
  omega

end ProjectionPhysics
