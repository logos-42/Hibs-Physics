-- ProjectionPhysics — Hidden-space physics bridge
--
-- Module 15: HiddenSpacePhysics.lean
--
-- 本模块把新的物理直觉压缩成一个可检查的离散模型：
--   1. 隐数轴、实轴、虚轴是三条正交坐标轴；
--   2. 轴投影可以互相转换，并且三轴分量可以重构原态；
--   3. 空间流产生离散运动向量；
--   4. 自旋被建模为抵抗运动的旋量残差；
--   5. 质量是旋量残差的离散范数；
--   6. 三夸克核的轴间距给出渐近自由指数；
--   7. 时间不是基本字段，而是流路径的步数（涌现量纲）。
--
-- 诚实边界：这些是“假设 -> 可证明后果”的模型定理，不是标准模型、
-- QCD 或连续时空的完整推导。特别是“渐近自由”在这里是一个离散
-- proximity law，尚未等同于 QCD 的 beta 函数。

import ProjectionPhysics.Archive.Clifford

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- HSP1. 隐数三轴
-- ---------------------------------------------------------------------------

/-- 隐数空间的离散三轴态：隐藏轴 H、实轴 R、虚轴 I。
    H 不是复平面中的第四个普通坐标，而是内部/核方向的专用轴。 -/
structure HiddenTriAxis where
  hidden : Int
  real : Int
  imag : Int

def hiddenTriAxisAdd (x y : HiddenTriAxis) : HiddenTriAxis :=
  ⟨x.hidden + y.hidden, x.real + y.real, x.imag + y.imag⟩

instance hiddenTriAxisAddInstance : Add HiddenTriAxis :=
  ⟨hiddenTriAxisAdd⟩

instance : Zero HiddenTriAxis :=
  ⟨⟨0, 0, 0⟩⟩

instance : Neg HiddenTriAxis :=
  ⟨fun x => ⟨-x.hidden, -x.real, -x.imag⟩⟩

theorem HiddenTriAxis.ext {x y : HiddenTriAxis}
    (hh : x.hidden = y.hidden) (hr : x.real = y.real) (hi : x.imag = y.imag) : x = y := by
  cases x
  cases y
  cases hh
  cases hr
  cases hi
  rfl

def hiddenAxis (h : Int) : HiddenTriAxis := ⟨h, 0, 0⟩
def realAxis (r : Int) : HiddenTriAxis := ⟨0, r, 0⟩
def imagAxis (i : Int) : HiddenTriAxis := ⟨0, 0, i⟩

def hiddenProjection (x : HiddenTriAxis) : Int := x.hidden
def realProjection (x : HiddenTriAxis) : Int := x.real
def imagProjection (x : HiddenTriAxis) : Int := x.imag

/-- 三轴之间的转换通道：转换保留目标轴分量，但不声称投影可逆。 -/
def convertHiddenToReal (h : Int) : Int := h
def convertRealToImag (r : Int) : Int := r
def convertImagToHidden (i : Int) : Int := i

def convertHiddenToRealAxis (h : Int) : HiddenTriAxis := realAxis h
def convertRealToImagAxis (r : Int) : HiddenTriAxis := imagAxis r
def convertImagToHiddenAxis (i : Int) : HiddenTriAxis := hiddenAxis i

theorem hidden_real_conversion_roundtrip (h : Int) :
    convertHiddenToReal h = h := by
  rfl

theorem real_imag_conversion_roundtrip (r : Int) :
    convertRealToImag r = r := by
  rfl

theorem imag_hidden_conversion_roundtrip (i : Int) :
    convertImagToHidden i = i := by
  rfl

theorem hidden_to_real_axis_preserves_value (h : Int) :
    realProjection (convertHiddenToRealAxis h) = h := by
  rfl

theorem real_to_imag_axis_preserves_value (r : Int) :
    imagProjection (convertRealToImagAxis r) = r := by
  rfl

theorem imag_to_hidden_axis_preserves_value (i : Int) :
    hiddenProjection (convertImagToHiddenAxis i) = i := by
  rfl

/-- 转换的真正可验证内容：三轴投影可以重构原始隐数态。 -/
def reconstructHiddenTriAxis (x : HiddenTriAxis) : HiddenTriAxis :=
  hiddenAxis (hiddenProjection x) + realAxis (realProjection x) + imagAxis (imagProjection x)

theorem hidden_tri_axis_reconstructs (x : HiddenTriAxis) :
    reconstructHiddenTriAxis x = x := by
  apply HiddenTriAxis.ext
  · change x.hidden + 0 + 0 = x.hidden
    omega
  · change 0 + x.real + 0 = x.real
    omega
  · change 0 + 0 + x.imag = x.imag
    omega

/-- 三轴的离散内积；不同轴的基向量正交。 -/
def triAxisDot (x y : HiddenTriAxis) : Int :=
  x.hidden * y.hidden + x.real * y.real + x.imag * y.imag

theorem hidden_real_orthogonal (h r : Int) :
    triAxisDot (hiddenAxis h) (realAxis r) = 0 := by
  simp [triAxisDot, hiddenAxis, realAxis]

theorem hidden_imag_orthogonal (h i : Int) :
    triAxisDot (hiddenAxis h) (imagAxis i) = 0 := by
  simp [triAxisDot, hiddenAxis, imagAxis]

theorem real_imag_orthogonal (r i : Int) :
    triAxisDot (realAxis r) (imagAxis i) = 0 := by
  simp [triAxisDot, realAxis, imagAxis]

-- ---------------------------------------------------------------------------
-- HSP2. 空间流产生运动向量
-- ---------------------------------------------------------------------------

/-- 可观测三维空间中的离散运动向量；第三分量承载隐数轴的内部流。 -/
structure SpaceMotion where
  x : Int
  y : Int
  z : Int

theorem SpaceMotion.ext {u v : SpaceMotion}
    (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u
  cases v
  cases hx
  cases hy
  cases hz
  rfl

def spaceMotionOf (x : HiddenTriAxis) : SpaceMotion :=
  ⟨x.real, x.imag, x.hidden⟩

/-- 空间流的运动向量：它是状态的流动输出，而不是预先存在的时间导数。 -/
def spaceFlow (x y : HiddenTriAxis) : SpaceMotion :=
  ⟨y.real - x.real, y.imag - x.imag, y.hidden - x.hidden⟩

theorem stationary_space_flow (x : HiddenTriAxis) :
    spaceFlow x x = ⟨0, 0, 0⟩ := by
  cases x
  simp [spaceFlow]

theorem space_flow_is_axis_difference (x y : HiddenTriAxis) :
    (spaceFlow x y).x = y.real - x.real ∧
    (spaceFlow x y).y = y.imag - x.imag ∧
    (spaceFlow x y).z = y.hidden - x.hidden := by
  exact ⟨rfl, rfl, rfl⟩

-- ---------------------------------------------------------------------------
-- HSP3. 自旋 = 对空间运动的旋量阻抗
-- ---------------------------------------------------------------------------

/-- 两分量离散旋量残差：
    z 分量是隐数内部流对可观测运动的抵抗，x-y 是横向运动的不相容量。 -/
structure SpinorResistance where
  left : Int
  right : Int

def spinorResistanceOf (v : SpaceMotion) : SpinorResistance :=
  ⟨v.z, v.x - v.y⟩

/-- 离散旋量阻抗范数。它是质量候选，不直接声称是物理单位制下的 m²。 -/
def spinorResistanceIndex (s : SpinorResistance) : Nat :=
  Int.natAbs s.left + Int.natAbs s.right

def massIndexOfMotion (v : SpaceMotion) : Nat :=
  spinorResistanceIndex (spinorResistanceOf v)

theorem mass_is_spinor_resistance (v : SpaceMotion) :
    massIndexOfMotion v = Int.natAbs v.z + Int.natAbs (v.x - v.y) := by
  rfl

theorem stationary_flow_has_zero_spinor_mass (x : HiddenTriAxis) :
    massIndexOfMotion (spaceFlow x x) = 0 := by
  cases x
  simp [massIndexOfMotion, spinorResistanceIndex, spinorResistanceOf, spaceFlow]

theorem hidden_flow_generates_spinor_resistance
    (x y : HiddenTriAxis) (h : y.hidden ≠ x.hidden) :
    (spinorResistanceOf (spaceFlow x y)).left ≠ 0 := by
  intro hz
  apply h
  dsimp [spinorResistanceOf, spaceFlow] at hz
  omega

-- ---------------------------------------------------------------------------
-- HSP4. 三夸克核与离散“渐近自由”指数
-- ---------------------------------------------------------------------------

structure Quark where
  state : HiddenTriAxis
  motion : SpaceMotion

structure QuarkTriplet where
  q1 : Quark
  q2 : Quark
  q3 : Quark

def axisDistance (x y : HiddenTriAxis) : Nat :=
  Int.natAbs (x.hidden - y.hidden) +
  Int.natAbs (x.real - y.real) +
  Int.natAbs (x.imag - y.imag)

def nucleusAxisSpread (t : QuarkTriplet) : Nat :=
  axisDistance t.q1.state t.q2.state +
  axisDistance t.q2.state t.q3.state +
  axisDistance t.q1.state t.q3.state

/-- 距离越小，指数越大：这是本模型对“靠近时渐近自由”的离散编码。 -/
def freedomIndex (cutoff distance : Nat) : Nat :=
  cutoff - min cutoff distance

def quarkAsymptoticFreedom (t : QuarkTriplet) : Nat :=
  freedomIndex 3 (nucleusAxisSpread t)

def quarkMassIndex (q : Quark) : Nat :=
  massIndexOfMotion q.motion

/-- 核质量候选 = 三个夸克的旋量阻抗 + 轴间残差。 -/
def nucleusMassIndex (t : QuarkTriplet) : Nat :=
  quarkMassIndex t.q1 + quarkMassIndex t.q2 + quarkMassIndex t.q3 + nucleusAxisSpread t

theorem axisDistance_self (x : HiddenTriAxis) : axisDistance x x = 0 := by
  cases x
  simp [axisDistance]

theorem coincident_quarks_have_maximal_asymptotic_freedom
    (t : QuarkTriplet)
    (h12 : t.q1.state = t.q2.state)
    (h23 : t.q2.state = t.q3.state) :
    nucleusAxisSpread t = 0 ∧ quarkAsymptoticFreedom t = 3 := by
  have hspread : nucleusAxisSpread t = 0 := by
    simp [nucleusAxisSpread, axisDistance, h12, h23]
  constructor
  · exact hspread
  · simp [quarkAsymptoticFreedom, hspread, freedomIndex]

theorem coincident_quark_nucleus_mass_is_internal_resistance
    (t : QuarkTriplet)
    (h12 : t.q1.state = t.q2.state)
    (h23 : t.q2.state = t.q3.state) :
    nucleusMassIndex t = quarkMassIndex t.q1 + quarkMassIndex t.q2 + quarkMassIndex t.q3 := by
  have hspread : nucleusAxisSpread t = 0 :=
    (coincident_quarks_have_maximal_asymptotic_freedom t h12 h23).1
  simp [nucleusMassIndex, hspread]

-- ---------------------------------------------------------------------------
-- HSP5. 时间是流路径的步数
-- ---------------------------------------------------------------------------

/-- 不在状态中放入原始 t；时间由离散流路径的长度定义。 -/
def emergentTime (path : List HiddenTriAxis) : Nat :=
  path.length

theorem emergent_time_empty : emergentTime [] = 0 := by
  rfl

theorem emergent_time_append (p q : List HiddenTriAxis) :
    emergentTime (p ++ q) = emergentTime p + emergentTime q := by
  simp [emergentTime]

theorem two_nodes_have_two_time_units (x y : HiddenTriAxis) :
    emergentTime [x, y] = 2 := by
  rfl

end ProjectionPhysics
