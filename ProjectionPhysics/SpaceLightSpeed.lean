-- ProjectionPhysics — 矢量光速：空间本身的等效速度（新概念）
--
-- 传统表述：光速 c 是"物质/信号在空间中的最大速度"（物质属性）。
-- 新概念（leo, 2026-08-11）：光速是**空间本身的等效速度**——
-- 空间自身以 c 运动，物质在其中运动是相对空间运动而言的。
-- 这不是对空间里面物质的速度描述，而是空间自身的运动属性。
--
-- 与三方向假设的连接：空间在三个方向运动（平面内圆周/椭圆 + 法向量），
-- 矢量光速 = 空间运动在三方向的等效速度矢量。
--
-- 物理图像：
--   光子 = 去掉垂直方向向量 + 完全随空间运动 ⟹ 零锚定 ⟹ 零质量
--   电子 = 法向旋转（自旋）⟹ 偏离空间运动 ⟹ 锚定非零 ⟹ 有质量
--
-- SLS4–SLS5（思路 B 落地）：空间运动方向 → Pauli 自旋生成元（波法向量
-- 旋量）→ 等效旋转角动量；三方向 ↔ 三胶子的形式化连接。
--   σ₁, σ₂ = 平面内两方向的运动生成元（反交换 ⟹ 圆周运动的代数）
--   σ₃ = i·σ₁σ₂ ⟹ ★"平面外的垂直向量"从平面内运动涌现（C4 实例化）
--
-- 诚实边界：这是新概念的代数种子（结构 + 序关系定理），
-- 不是连续时空，也不是狭义/广义相对论的形式化。

import ProjectionPhysics.Clifford
import ProjectionPhysics.MinimalCore

namespace ProjectionPhysics

/-! ### SLS1. 矢量光速：空间本身的等效速度 -/

/-- 空间速度矢量（矢量光速）：空间自身在三个方向的等效运动。
    `c2` 是光速平方的普适常数——空间每点的等效速度模都等于它。 -/
structure SpaceVelocity (c2 : Int) where
  x : Int
  y : Int
  z : Int
  speed_squared : x * x + y * y + z * z = c2

/-- 光速普适性：任何两个空间点的等效速度模相同（c 是空间属性，
    不是物质速度的极限）。这是"矢量光速 = 空间本身等效速度"的核心。 -/
theorem light_speed_is_universal_space_property
    (c2 : Int) (v w : SpaceVelocity c2) :
    v.x * v.x + v.y * v.y + v.z * v.z =
      w.x * w.x + w.y * w.y + w.z * w.z := by
  calc
    v.x * v.x + v.y * v.y + v.z * v.z = c2 := v.speed_squared
    _ = w.x * w.x + w.y * w.y + w.z * w.z := w.speed_squared.symm

/-- 例：空间沿 x 方向以速度 c 运动（等效速度 = c，其余分量为零）。 -/
def xDirectionalSpace (c : Int) : SpaceVelocity (c * c) :=
  ⟨c, 0, 0, by omega⟩

/-- 三方向空间运动：空间在三个方向都有运动分量
    （对应"平面内圆周/椭圆 + 法向量"的三方向假设）。 -/
def triDirectionalSpace (c2 a b c : Int) (h : a * a + b * b + c * c = c2) :
    SpaceVelocity c2 :=
  ⟨a, b, c, h⟩

/-- 三方向空间运动是"矢量光速"的自然形态：
    空间同时沿 x、y、z 三方向运动，模为普适常数。 -/
theorem tri_directional_space_has_universal_speed
    (c2 a b c : Int) (h : a * a + b * b + c * c = c2)
    (v w : SpaceVelocity c2) :
    a * a + b * b + c * c =
      v.x * v.x + v.y * v.y + v.z * v.z := by
  calc
    a * a + b * b + c * c = c2 := h
    _ = v.x * v.x + v.y * v.y + v.z * v.z := v.speed_squared.symm

/-! ### SLS2. 相对运动与光子 -/

/-- 物质相对空间的运动（物质速度 − 空间本身的运动）。 -/
structure RelativeMotion where
  x : Int
  y : Int
  z : Int

theorem RelativeMotion.ext {r s : RelativeMotion}
    (hx : r.x = s.x) (hy : r.y = s.y) (hz : r.z = s.z) : r = s := by
  cases r
  cases s
  cases hx
  cases hy
  cases hz
  rfl

def relativeMotionZero : RelativeMotion := ⟨0, 0, 0⟩

/-- 光子条件：物质完全随空间运动（相对运动为零）。 -/
def IsComoving (r : RelativeMotion) : Prop := r = relativeMotionZero

/-- 物质状态：空间背景 + 相对空间运动 + 内部运动（自旋）。 -/
structure MatterState (c2 : Int) where
  space : SpaceVelocity c2
  relative : RelativeMotion
  spin : Int

/-- 锚定质量候选 = 内部运动（自旋）+ 相对空间运动的抵抗。 -/
def anchorMassOf (s : MatterState c2) : Nat :=
  Int.natAbs s.spin + Int.natAbs s.relative.x +
    Int.natAbs s.relative.y + Int.natAbs s.relative.z

/-- 光子：无内部运动（去掉垂直方向向量）且完全随空间运动
    ⟹ 零锚定 ⟹ 零质量。 -/
theorem anchor_mass_zero_of_photon (s : MatterState c2)
    (hspin : s.spin = 0) (hrel : IsComoving s.relative) :
    anchorMassOf s = 0 := by
  rw [anchorMassOf, hspin]
  rw [hrel]
  simp [IsComoving, relativeMotionZero]

/-- 光子零锚定的显式落地（#eval 可算）。 -/
theorem photon_anchor_zero_example :
    anchorMassOf ({ space := xDirectionalSpace 1, relative := relativeMotionZero,
                    spin := 0 } : MatterState 1) = 0 := by
  simp [anchorMassOf, xDirectionalSpace, relativeMotionZero]

/-! ### SLS3. 内部运动 ⟹ 锚定非零 -/

/-- 非零内部运动（自旋）⟹ 锚定质量为正。
    （电子 = 法向旋转的自旋，偏离纯空间运动 ⟹ 有质量。） -/
theorem anchor_mass_positive_of_internal_motion
    (s : MatterState c2) (hspin : s.spin ≠ 0) :
    0 < anchorMassOf s := by
  unfold anchorMassOf
  have h : 0 < Int.natAbs s.spin := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hspin)
  omega

/-- 电子情形落地：自旋非零 ⟹ 锚定质量为正。 -/
theorem electron_anchor_positive :
    0 < anchorMassOf ({ space := xDirectionalSpace 1, relative := relativeMotionZero,
                        spin := 1 } : MatterState 1) := by
  apply anchor_mass_positive_of_internal_motion
  native_decide

/-- 相对空间运动非零（物质偏离空间流）也产生锚定。 -/
theorem anchor_mass_positive_of_relative_motion
    (s : MatterState c2) (hrel : s.relative ≠ relativeMotionZero) :
    0 < anchorMassOf s := by
  unfold anchorMassOf
  by_cases hx : s.relative.x = 0
  · by_cases hy : s.relative.y = 0
    · by_cases hz : s.relative.z = 0
      · exfalso
        apply hrel
        apply RelativeMotion.ext <;> assumption
      · have hp : 0 < Int.natAbs s.relative.z :=
          Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hz)
        omega
    · have hp : 0 < Int.natAbs s.relative.y :=
        Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hy)
      omega
  · have hp : 0 < Int.natAbs s.relative.x :=
      Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hx)
    omega

/-! ### SLS4. 波法向量旋量：空间运动方向 → 自旋生成元（思路 B） -/

/-- 空间运动方向（未归一化的三分量波法向量）。 -/
structure MotionDirection where
  x : Int
  y : Int
  z : Int

/-- 标量乘 Mat2（ℂ 标量 × 矩阵的逐分量乘法）。 -/
def mat2Scalar (z : ℂ) (M : Mat2) : Mat2 :=
  ⟨z * M.a, z * M.b, z * M.c, z * M.d⟩

/-- Int → ℂ 实嵌入。 -/
def intC (n : Int) : ℂ :=
  ⟨n, 0⟩

/-- 方向 → 自旋算子：n·σ = nx·σ₁ + ny·σ₂ + nz·σ₃。
    波法向量形成旋量的第一步：方向决定自旋投影轴。 -/
def directionalSpin (n : MotionDirection) : Mat2 :=
  mat2Scalar (intC n.x) σ₁ + mat2Scalar (intC n.y) σ₂ + mat2Scalar (intC n.z) σ₃

/-- 平面内两方向的运动生成元反交换：σ₁σ₂ + σ₂σ₁ = 0。
    ★ 平面内圆周/椭圆运动的代数——两个横向方向不可交换，
    是"旋量"（半整数角动量）出现的根源（C2 实例化）。 -/
theorem planar_directions_anticommute :
    matMul σ₁ σ₂ + matMul σ₂ σ₁ = 0 :=
  sigma1_sigma2_anticommute

/-- ★ 法向量从平面内涌现：σ₃ = i·σ₁σ₂。
    "平面外的垂直向量"不是独立输入——它是平面内两方向运动
    乘积的必然结果（C4 实例化）。这精确对应"空间在平面外
    还有一个垂直向量"。 -/
theorem normal_direction_emerges_from_plane :
    σ₃ = matMul (scalar2 cI) (matMul σ₁ σ₂) :=
  sigma3_from_sigma1_sigma2

/-- 平面内运动乘积给出虚数单位：i² = -1。
    （C3 实例化：圆周运动的两个半圈产生符号翻转） -/
theorem planar_motion_products_give_i :
    matMul (matMul σ₁ σ₂) (matMul σ₁ σ₂) = -1 :=
  i_emerges_from_clifford

/-- 光子：去掉垂直方向向量 ⟹ 空间运动只剩平面内两方向。 -/
def planarOnlyMotion (nx ny : Int) : MotionDirection :=
  ⟨nx, ny, 0⟩

/-- 光子方向无垂直分量（法向量被去掉）。 -/
theorem photon_direction_has_no_normal_component (nx ny : Int) :
    (planarOnlyMotion nx ny).z = 0 := by
  rfl

/-- 沿 x 方向的空间运动，其自旋投影正是 σ₁：
    空间运动方向 ↔ 旋量生成元的具体对应。 -/
theorem x_motion_spin_is_sigma1 :
    directionalSpin ⟨1, 0, 0⟩ = σ₁ := by
  unfold directionalSpin mat2Scalar intC
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, cI, ℂ.mul_re, ℂ.mul_im,
      ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega

/-- 空间运动产生的等效旋转角动量流：旋量 ψ 在方向自旋 n·σ 下流动。
    这是"胶子在空间中随空间运动的等效旋转角动量"的代数表达。 -/
def motionSpinFlow (n : MotionDirection) (ψ : Spinor) : Spinor :=
  matMulSpinor (directionalSpin n) ψ

/-- 沿 x 方向的空间运动在非零旋量上产生非零角动量流：
    空间运动把自旋结构传给旋量（胶子/电子的等效旋转角动量）。 -/
theorem x_motion_spin_flow_nonzero (ψ : Spinor) (hψ : ψ ≠ 0) :
    motionSpinFlow ⟨1, 0, 0⟩ ψ ≠ 0 := by
  unfold motionSpinFlow
  rw [x_motion_spin_is_sigma1]
  exact spin_flow_sigma1_nonzero_of_spinor_nonzero ψ hψ

/-! ### SLS5. 三方向 ↔ 三胶子：三方向假设的形式化连接 -/

/-- 三方向空间运动单位态：空间沿三方向各以单位速度运动
    （平面两方向 + 法向量 = (1,1,1)）。 -/
def triUnitMotion : MotionDirection :=
  ⟨1, 1, 1⟩

/-- ★ 三方向单位态 ↔ 三胶子单位态：两侧的"三"是同一个三。
    空间三方向（x,y,z）= 色三方向（c0,c1,c2）= 三胶子。
    m_G² = 3 是"三个方向各贡献一个模式单位"的代数内容
    （数值：√3·M₀ 精确匹配格点 0++ = 1.71 GeV）。 -/
theorem tri_direction_triplet_mass_connection :
    pureGlueMassSquared (minimalTripletGlueball ⟨1⟩ ⟨1⟩ ⟨1⟩) = 3 :=
  triplet_unit_mode_mass_squared_is_three

/-- 三方向空间运动是矢量光速的自然形态：三方向运动模 = 3（单位化前），
    与三胶子色单态 (1,1,1) 的 m_G² = 3 对应。 -/
theorem tri_unit_motion_speed_squared_is_three :
    (triUnitMotion.x) * (triUnitMotion.x) +
    (triUnitMotion.y) * (triUnitMotion.y) +
    (triUnitMotion.z) * (triUnitMotion.z) = 3 := by
  native_decide

/-- 三方向假设的两侧连接定理（汇总）：
    空间三方向运动模² = 3 ∧ 三胶子质量平方 = 3。 -/
theorem three_direction_three_glueball_bridge :
    ((triUnitMotion.x) * (triUnitMotion.x) +
     (triUnitMotion.y) * (triUnitMotion.y) +
     (triUnitMotion.z) * (triUnitMotion.z) = 3) ∧
    (pureGlueMassSquared (minimalTripletGlueball ⟨1⟩ ⟨1⟩ ⟨1⟩) = 3) := by
  constructor
  · exact tri_unit_motion_speed_squared_is_three
  · exact tri_direction_triplet_mass_connection

end ProjectionPhysics
