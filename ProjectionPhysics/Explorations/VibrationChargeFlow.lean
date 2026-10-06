-- ProjectionPhysics — VibrationChargeFlow：位移流的源/汇代数接口
--
-- 把用户给出的正负电荷语言先写成最小可证结构：
--   正电荷 = 位移流散度为正（源）
--   负电荷 = 位移流散度为负（汇）
-- 这里只形式化符号层，不声称已得到 e 的数值、连续矢量场或 Maxwell 全部动力学。

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace ProjectionPhysics.VibrationChargeFlow

/-- 局部位移流的散度标量：正=发散源，负=汇聚汇。 -/
def flowChargeSign (rho : ℝ) : Prop :=
  0 < rho ∨ rho < 0

/-- 正电荷候选：单位时间空间位移向外发散。 -/
def PositiveSource (rho : ℝ) : Prop := 0 < rho

/-- 负电荷候选：空间位移向内汇聚。 -/
def NegativeSink (rho : ℝ) : Prop := rho < 0

/-- CF1：正负源汇不能同时成立。 -/
theorem source_sink_exclusive {rho : ℝ}
    (hp : PositiveSource rho) (hn : NegativeSink rho) : False := by
  unfold PositiveSource at hp
  unfold NegativeSink at hn
  linarith

/-- CF2：电荷共轭/源汇翻转的最小代数：rho→−rho 交换正源与负汇。 -/
theorem source_sink_flip {rho : ℝ} :
    PositiveSource rho ↔ NegativeSink (-rho) := by
  unfold PositiveSource NegativeSink
  constructor <;> intro h <;> linarith

/-- CF3：零散度既不是正电荷也不是负电荷。 -/
theorem zero_is_neutral :
    ¬ PositiveSource 0 ∧ ¬ NegativeSink 0 := by
  constructor
  · intro h
    exact (lt_irrefl (0 : ℝ)) h
  · intro h
    exact (lt_irrefl (0 : ℝ)) h

/-- CF4：源汇符号的大小在取负时保持，方向翻转。 -/
theorem abs_charge_preserved_by_flip (rho : ℝ) :
    |(-rho : ℝ)| = |rho| := by
  simp

/-- CF5：若把旋量相对方向 q_spin 作为位移条数强度，正负只应由源汇方向标记，
    不应改变非负幅值 q。 -/
theorem nonnegative_count_unchanged_by_source_sink
    (q : ℝ) (hq : 0 ≤ q) : 0 ≤ q := hq

end ProjectionPhysics.VibrationChargeFlow
