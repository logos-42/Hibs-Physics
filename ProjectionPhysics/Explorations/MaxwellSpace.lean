-- ProjectionPhysics — 电磁 = 空间场的运动学（全新形式推导，探索）
--
-- leo（2026-08-14）：麦克斯韦方程规定了电磁效应，现在把空间运行也
-- 纳入——考虑电场、磁场、空间场本身的运行和互相影响。这是完全全新
-- 的形式推导（思考深度高于麦克斯韦尺度）。
--
-- ★ 核心结构（本模块形式化的新内容）：
--
--   空间场 C（1+1 维差分骨架）为独立动力学场；
--   电磁场是 C 的运动学派生：
--     E = −∂_t C（电场 = 空间场的时间变化）
--     B = ∂_x C  （磁场 = 空间场的空间梯度，1+1 维 = 涡旋的代数种子）
--
--   检验（本模块证）：
--     MS1  差分交换：∂_t∂_x C = ∂_x∂_t C（代数恒等）
--     MS2  ★ 法拉第定律自动成立：∂_t B = −∂_x E
--          ——不是独立的物理定律，是"电磁场 = 空间场运动学"的恒等
--     MS3  ★ 安培-麦克斯韦 ⟺ C 的波动方程：∂_tE = −c²∂_xB ⟺ ∂_t²C = c²∂_x²C
--          ——麦克斯韦方程组整体 ⟺ C 的波动方程 + 两个定义
--     MS4  电磁场 = 空间场运动学（定义定理）
--     MS5  源（电荷/电流）⟺ C 方程的驱动项：电荷驱动空间流动（互相影响）
--
--   ⟹ 麦克斯韦尺度之上的数学内容：C = 电磁矢量势 A，但 C 是物理的
--     （SLS1：|C| = c 普适 ⟹ 规范自由度被物理条件固定——仓库假设
--     消灭规范冗余，这是与标准电磁理论的解释层区别；3D 中
--     B = ∇×C 自动无散，见注释）。
--
-- 诚实边界：
--   - 本模块是 1+1 维差分骨架（仓库风格：微分 = 差商种子，D7 路线）；
--     连续偏导（∂_t, ∂_x）与 3D 旋度/散度未形式化（仓库明确未支持
--     ∇·/∇×，连续版在 Python 侧数值验证）。
--   - "C = A 且 |C| = c 固定规范"是解释层（4 层判定：概念重构），
--     本模块证明的是代数内核：麦克斯韦 ⟺ C 波动 + 定义。
--   - 源项（电荷）只有形式化位置（MS5），电荷量子化/数值无来源。

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProjectionPhysics

/-! ### 空间场与差分算符（1+1 维骨架） -/

/-- 空间场 C(t, x)：离散时间-空间标量场（1+1 维差分骨架）。 -/
abbrev SpaceField : Type := ℤ → ℤ → ℝ

/-- 时间差分：∂_t C ≈ C(t+1) − C(t)。 -/
def Dt (C : SpaceField) (t x : ℤ) : ℝ :=
  C (t + 1) x - C t x

/-- 空间差分：∂_x C ≈ C(x+1) − C(x)。 -/
def Dx (C : SpaceField) (t x : ℤ) : ℝ :=
  C t (x + 1) - C t x

/-- 电场 = 空间场的时间变化：E = −∂_t C。 -/
def E_of (C : SpaceField) : SpaceField :=
  fun t x => -Dt C t x

/-- 磁场 = 空间场的空间梯度（1+1 维 = 3D 涡旋 ∇×C 的代数种子）：B = ∂_x C。 -/
def B_of (C : SpaceField) : SpaceField :=
  fun t x => Dx C t x

/-! ### MS1. 差分交换（Clairaut 的代数种子） -/

/-- ★ 差分交换：∂_t∂_x C = ∂_x∂_t C（连续偏导交换律的差分对应）。
    ——电磁场 = 空间场运动学的一切恒等关系都从这里来。 -/
theorem dtx_commute (C : SpaceField) (t x : ℤ) :
    Dt (Dx C) t x = Dx (Dt C) t x := by
  unfold Dt Dx
  ring

/-! ### MS2. 法拉第定律自动成立 -/

/-- ★ 法拉第定律是恒等：∂_t B = −∂_x E（代入 E = −∂_tC, B = ∂_xC 后
    就是差分交换 MS1）——标准麦克斯韦的第一条方程不是独立物理定律，
    而是"电磁场 = 空间场运动学"的必然结果。 -/
theorem faraday_automatic (C : SpaceField) (t x : ℤ) :
    Dt (B_of C) t x = -Dx (E_of C) t x := by
  unfold E_of B_of
  unfold Dt Dx
  ring

/-! ### MS3. 安培-麦克斯韦 ⟺ C 的波动方程 -/

/-- ★ 安培-麦克斯韦 ⟺ 空间场波动方程：∂_t E = −c²∂_x B ⟺ ∂_t²C = c²∂_x²C。
    麦克斯韦方程组的第二条方程 = 空间场 C 自身的动力学（波动）。
    ⟹ 整个麦克斯韦方程组 ⟺ C 的波动方程 + 两个运动学定义。 -/
theorem ampere_iff_wave_equation (C : SpaceField) (c : ℝ) (t x : ℤ) :
    Dt (E_of C) t x = -c ^ 2 * Dx (B_of C) t x ↔
    Dt (Dt C) t x = c ^ 2 * Dx (Dx C) t x := by
  unfold E_of B_of
  constructor
  · intro h
    unfold Dt at h ⊢
    ring_nf at h ⊢
    linarith
  · intro h
    unfold Dt at h ⊢
    ring_nf at h ⊢
    linarith

/-! ### MS4. 电磁场 = 空间场运动学（定义定理） -/

/-- ★ 电磁场是空间场的运动学派生：E = −∂_t C，B = ∂_x C。
    空间场 C 是唯一独立动力学场（波动方程 MS3）；E、B 是它的
    时间/空间变化率——"电磁 = 空间运动的表观形态"。 -/
theorem em_fields_are_space_kinematics (C : SpaceField) (t x : ℤ) :
    E_of C t x = -(Dt C t x) ∧ B_of C t x = Dx C t x := by
  unfold E_of B_of
  constructor <;> rfl

/-! ### MS5. 源（电荷/电流）驱动空间场 -/

/-- ★ 互相影响（带源版）：安培-麦克斯韦带源 ∂_tE = −c²∂_xB − J
    ⟺ 空间场方程被电荷/电流驱动：∂_t²C = c²∂_x²C + J。
    ——电荷不是场外的"子弹"，而是空间场方程本身的驱动项：
    空间场的运行与电磁源互相影响。 -/
theorem source_drives_space_flow (C J : SpaceField) (c : ℝ) (t x : ℤ) :
    Dt (E_of C) t x = -c ^ 2 * Dx (B_of C) t x - J t x ↔
    Dt (Dt C) t x = c ^ 2 * Dx (Dx C) t x + J t x := by
  unfold E_of B_of
  constructor
  · intro h
    unfold Dt at h ⊢
    ring_nf at h ⊢
    linarith
  · intro h
    unfold Dt at h ⊢
    ring_nf at h ⊢
    linarith

/-! ### 结论注释 -/

-- MS1–MS5 合读（麦克斯韦尺度之上的数学内容）：
--   1. 标准麦克斯韦：E、B 两个独立场 + 两条独立演化定律。
--   2. 本框架：唯一独立场 = 空间场 C（满足波动方程）；
--      E = −∂_tC、B = ∂_xC 是运动学定义；
--      法拉第 = 恒等（MS2，差分交换），安培 ⟺ C 波动（MS3）；
--      源 = C 方程的驱动项（MS5）。
--   3. C = 电磁矢量势 A；仓库 SLS1（|C| = c 普适）给 C 物理意义
--      ⟹ 规范自由度被物理条件固定（解释层，4 层判定：概念重构）。
--   4. 3D 推广：B = ∇×C 自动无散（∇·∇× = 0）；E = −∂_tC（库仑规范
--      无源）——超出本模块（仓库未支持 ∇×），数值见
--      scripts/verify_maxwell_space.py。
--   5. 预言候选：若 C 满足波动方程且 |C| = c，则 C 的波动 = 光
--      （已有 MF1/MF4）；电子 = C 的源+涡旋结构（∇·C ≠ 0 电荷，
--      ∇×C ≠ 0 自旋/磁场）——探讨层结构对应。

end ProjectionPhysics
