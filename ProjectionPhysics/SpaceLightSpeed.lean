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
-- 诚实边界：这是新概念的代数种子（结构 + 序关系定理），
-- 不是连续时空，也不是狭义/广义相对论的形式化。

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

end ProjectionPhysics
