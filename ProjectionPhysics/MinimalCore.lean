-- ProjectionPhysics — Minimal Core（最小核心命题，锚定版本）
--
-- 质量默认有量的结构：它不是场的激发能量（不是从场与激发态来描述的），
-- 而是物质为抵抗空间本身的运动产生的锚定效果。内部运动状态（自旋/
-- 内部关系）在空间流中产生旋量阻抗，阻抗的量就是质量候选。
--
-- 最简推导（四步）：
--   内部运动状态 s（自旋/内部关系：隐数内部流）
--   → 空间运动 F（空间本身的运动：space flow）
--   → 质量 m := 锚定效果（旋量阻抗：对空间运动的抵抗）
--   → 内部运动非零 ⟹ m ≠ 0
--
-- 适用对象：胶子、夸克、电子——任何有内部运动状态的物质。
-- 电子有电荷（"电"），但质量来自自旋对空间运动的抵御。
-- 光子边界：正反电子碰撞激发出的光子，是一瞬间"摆脱了空间运动锚定"
-- 的激发场粒子——零内部运动状态 ⟹ 零锚定 ⟹ 无质量。
--
-- 诚实边界：以上是质量候选的代数锚定，不是实验质量、QCD 质量或
-- MeV 数值。连续时空、规范场动力学、禁闭、色动力学均为后续扩展。

import ProjectionPhysics.HiddenSpacePhysics
import ProjectionPhysics.GlueballBridge

namespace ProjectionPhysics

/-! ### MC1. 锚定质量：内部运动状态 ⟹ 对空间运动的抵抗 -/

/-- 锚定质量候选：空间流产生的旋量阻抗。
    它是"抵抗空间运动的锚定效果"，不是场的激发能量。 -/
def anchorMassOf (x y : HiddenTriAxis) : Nat :=
  massIndexOfMotion (spaceFlow x y)

theorem anchor_mass_formula (x y : HiddenTriAxis) :
    anchorMassOf x y =
      Int.natAbs (y.hidden - x.hidden) +
      Int.natAbs ((y.real - x.real) - (y.imag - x.imag)) := by
  simp [anchorMassOf, massIndexOfMotion, spinorResistanceIndex,
    spinorResistanceOf, spaceFlow]

/-- 内部运动状态非零（隐数内部流非零）⟹ 锚定质量非零。
    这是"质量 = 内部运动对空间运动的抵抗"的代数内容。 -/
theorem anchor_mass_nonzero_of_internal_motion
    (x y : HiddenTriAxis) (h : y.hidden ≠ x.hidden) :
    anchorMassOf x y ≠ 0 := by
  have hleft : (spinorResistanceOf (spaceFlow x y)).left ≠ 0 :=
    hidden_flow_generates_spinor_resistance x y h
  unfold anchorMassOf massIndexOfMotion spinorResistanceIndex
  have hn : Int.natAbs (spinorResistanceOf (spaceFlow x y)).left ≠ 0 :=
    Int.natAbs_ne_zero.mpr hleft
  omega

/-- 光子边界：无内部运动差异（静止流）⟹ 锚定质量为零。
    "摆脱空间运动锚定"的激发场粒子质量为零。 -/
theorem anchor_mass_zero_of_no_internal_motion (x : HiddenTriAxis) :
    anchorMassOf x x = 0 := by
  simp [anchorMassOf, massIndexOfMotion, spinorResistanceIndex,
    spinorResistanceOf, spaceFlow]

/-! ### MC2. 胶球：三胶子内部运动状态的色单态组合 -/

/-- G = (a, b, c)，color profile = (1, 1, 1)：三个胶子的内部运动状态
    （a, b, c）组成色单态。 -/
def minimalTripletGlueball (a b c : PureHiddenNumber) : Glueball :=
  tripletScalarGlueball a b c

theorem minimal_triplet_glueball_is_singlet (a b c : PureHiddenNumber) :
    ColorSinglet (minimalTripletGlueball a b c).configuration.colorProfile := by
  simpa [minimalTripletGlueball] using triplet_scalar_glueball_is_singlet a b c

/-- 锚定质量平方 = |a|² + |b|² + |c|²：三分量内部运动状态的平方和。 -/
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
