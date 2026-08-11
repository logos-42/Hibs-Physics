-- ProjectionPhysics — Minimal Core（最小核心命题）
--
-- 整个项目压缩为一条最小命题：
--
--     h ∈ K，Q(h) = h²，m²(h) := Q(h)   ⟹   h ≠ 0 ⟹ m²(h) ≠ 0
--
-- 最简推导只有四步：
--   内部自由度 h
--   → 二次型 Q(h) = h²
--   → 定义质量平方 m² = Q(h)
--   → h ≠ 0 ⇒ m² ≠ 0
--
-- 胶球版本（保留最少的色单态条件）：
--   G = (a, b, c)，color profile = (1, 1, 1)
--   m_G² = |a|² + |b|² + |c|²
--   只要 a, b, c 中至少一个非零 ⟹ m_G² > 0
--
-- 边界（必须明确）：
--   这里证明的是"非零内部不变量产生非零质量平方候选"，
--   还不是实验质量、QCD 质量或 MeV 数值。
--   SU(3)、Higgs 门户、时间、连续场和禁闭都属于后续扩展，
--   不应放进最小核心。

import ProjectionPhysics.HiddenOnlyHiggs
import ProjectionPhysics.GlueballBridge

namespace ProjectionPhysics

/-! ### MC1. 最小命题：非零内部不变量 ⟹ 非零质量平方候选 -/

/-- h ∈ K：纯隐数经核嵌入进入 ker(Re)，是内部（不可观测）方向。 -/
def minimalKernelElement (h : PureHiddenNumber) : KernelOf reProj :=
  hiddenKernelEmbedding h

theorem minimal_kernel_element_is_in_kernel (h : PureHiddenNumber) :
    (minimalKernelElement h).val.re = 0 := by
  rfl

/-- Q(h) = h²：核二次型给出标量不变量。 -/
theorem minimal_quadratic_formula (h : PureHiddenNumber) :
    hiddenKernelQuadratic h = h.value * h.value := by
  simp [hiddenKernelQuadratic, hiddenKernelPairing_formula]

/-- m²(h) := Q(h)：定义质量平方候选为核二次型。 -/
def minimalMassSquared (h : PureHiddenNumber) : Int :=
  hiddenKernelQuadratic h

theorem minimal_mass_squared_formula (h : PureHiddenNumber) :
    minimalMassSquared h = h.value * h.value := by
  simp [minimalMassSquared, minimal_quadratic_formula]

/-- h ≠ 0 ⟹ m²(h) ≠ 0：非零内部不变量产生非零质量平方候选。 -/
theorem minimal_mass_squared_nonzero_of_nonzero
    (h : PureHiddenNumber) (hh : h.value ≠ 0) :
    minimalMassSquared h ≠ 0 := by
  rw [minimal_mass_squared_formula]
  exact Int.mul_ne_zero hh hh

/-! ### MC2. 胶球最小版本：三色单态质量平方 = |a|² + |b|² + |c|² -/

/-- G = (a, b, c)，color profile = (1, 1, 1)：三色占据相等的色单态。 -/
def minimalTripletGlueball (a b c : PureHiddenNumber) : Glueball :=
  tripletScalarGlueball a b c

theorem minimal_triplet_glueball_is_singlet (a b c : PureHiddenNumber) :
    ColorSinglet (minimalTripletGlueball a b c).configuration.colorProfile := by
  simpa [minimalTripletGlueball] using triplet_scalar_glueball_is_singlet a b c

/-- m_G² = |a|² + |b|² + |c|²：纯胶子质量平方候选是三分量平方和。 -/
theorem triplet_glueball_mass_squared_formula (a b c : PureHiddenNumber) :
    pureGlueMassSquared (minimalTripletGlueball a b c) =
      Int.ofNat (Int.natAbs a.value * Int.natAbs a.value +
                 Int.natAbs b.value * Int.natAbs b.value +
                 Int.natAbs c.value * Int.natAbs c.value) := by
  simp [minimalTripletGlueball, pureGlueMassSquared, tripletScalarGlueball,
    configurationFieldEnergy, gluonModeEnergy]
  ac_rfl

/-- a, b, c 至少一个非零 ⟹ m_G² > 0。 -/
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

-- 物理边界：以上是离散质量平方候选，非实验质量、QCD 质量或 MeV 数值。
-- （边界由注释与 wiki 文档承载；Lean 层只形式化代数内容。）

end ProjectionPhysics
