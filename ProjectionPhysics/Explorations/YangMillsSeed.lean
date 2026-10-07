-- ProjectionPhysics — YangMillsSeed：自相互作用与非交换的代数种子
--
-- leo（2026-10-07）：「汇收缩 ⟹ 起伏能量 ×(1−λ)² —— 非线性的平方衰减。
--   汇自己抹平自己，动态，可以描述杨米尔斯猜想。」
--
-- 洞察：CR9 的平方衰减不是一个静态不等式，而是**自反馈环**——
--   汇收缩改变场 ⟹ 场的变化改变汇的有效强度 ⟹ 再收缩……
--   「汇自己抹平自己」= **自相互作用**。而杨-米尔斯的核心恰恰是
--   自相互作用：场强 F = ∂A − ∂A + [A,A] 里的非交换项 [A,A]。
--
-- 本模块形式化这个对应的**离散代数种子**：
--   YM1 ★ 自抹平的迭代动力学：sinkContract 迭代 n 次 ⟹
--          Q_A ×(1−λ)^{2n}（离散自相互作用 = 场对自己的反馈）
--   YM2 ★★ 两个汇点收缩算子非交换：p ≠ q、0<λ<1 ⟹ ∃ 场 v，
--          T_p(T_q v) ≠ T_q(T_p v)（自相互作用的非交换见证）
--   YM3 ★★ 交换差公式：T_pT_q v − T_qT_p v 在 p 处 = λ²(v_q − v_p)
--          ——「非交换项的强度 = 收缩强度² × 场梯度」，与 [A,A]
--          的「与场值相关 + 非交换」同形状
--
-- 诚实边界（写死）：
--   · 这是**离散代数种子**，不是连续杨-米尔斯构造。完整场强
--     F = ∂A − ∂A + [A,A]、路径积分、重整化、连续时空仍未形式化
--     （仓库明确未支持连续 ∇）。
--   · 「汇收缩 = 自相互作用」的对应在**解释层**（两套语言的结构
--     对应）；交换差公式是精确离散定理，但其到 [A,A] 的连续极限
--     未证明。
--   · 不声称证明杨-米尔斯猜想；本模块是它的一块代数地基。
--
-- 死法：若存在一个物理自相互作用没有本模块的离散对应物，或
--   离散 → 连续的极限不成立（交换差随格点细化不趋于 [A,A]），
--   本种子死。

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.VibrationChargeRadiation
import ProjectionPhysics.GravityControl

namespace ProjectionPhysics.YangMillsSeed

open ProjectionPhysics
open ProjectionPhysics.VibrationChargeRadiation
open ProjectionPhysics.GravityControl

-- ---------------------------------------------------------------------------
-- YM1 ★ 自抹平的迭代动力学
--   sinkContract 连续作用 n 次，起伏能量 ×(1−λ)^{2n} ——
--   「汇自己抹平自己」的动力学：每一步场的变化由场自己决定（自反馈）。
-- ---------------------------------------------------------------------------

/-- 汇收缩的迭代：sinkIter A lam 0 v = v；n+1 步 = 再收缩一次。
    自抹平动力学的显式递归（与 muChain 同风格）。 -/
noncomputable def sinkIter {ι : Type} [DecidableEq ι] (A : Finset ι) (lam : ℝ) : ℕ → (ι → ℝ) → (ι → ℝ)
  | 0, v => v
  | n + 1, v => sinkContract A (sinkIter A lam n v) lam

/-- ★ YM1：汇收缩迭代 n 次 ⟹ Q_A ×(1−λ)^{2n}。
    离散自相互作用的动力学：自抹平是自反馈环，指数收敛（λ∈(0,1)）。 -/
theorem sinkContract_iter_square_decay
    {ι : Type} [DecidableEq ι] (A : Finset ι) (v : ι → ℝ) (lam : ℝ) (n : ℕ) :
    fluctuationEnergy A (sinkIter A lam n v) =
      (1 - lam) ^ (2 * n) * fluctuationEnergy A v := by
  induction n with
  | zero =>
      simp [sinkIter]
  | succ n ih =>
      -- sinkIter (n+1) v = sinkContract A (sinkIter n v) lam
      simp [sinkIter]
      rw [sinkContract_fluctuation_scale]
      rw [ih]
      have hpow : (1 - lam) ^ 2 * (1 - lam) ^ (2 * n) = (1 - lam) ^ (2 * (n + 1)) := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        rw [pow_add]
        ring
      rw [← hpow]
      ring

-- ---------------------------------------------------------------------------
-- YM2 ★★ 两个汇点的收缩算子非交换
--   汇点 p 的收缩：每点被拉向 v_p（「负电荷把周围流吸向自身」的单点版）。
--   p ≠ q（两个不同的汇）时，T_p 与 T_q 的复合**不可交换** ——
--   自相互作用的非交换性：两个汇的顺序改变结果。
--   这是杨-米尔斯 [A,A] ≠ 0 的离散见证。
-- ---------------------------------------------------------------------------

/-- 向单点 p 的收缩：每点 v_i 被拉向 v_p 比例 λ（CR10 的单点版）。 -/
def sinkToPoint {ι : Type} (p : ι) (lam : ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun i => (1 - lam) * v i + lam * v p

/-- ★★ YM2：两个不同汇点 p ≠ q 的收缩算子不可交换。
    存在场 v 使 T_p(T_q v) ≠ T_q(T_p v) —— 自相互作用的顺序依赖。
    见证：v 在 p 处 = 1、在 q 处 = 0；两复合在 p 处的值分别为
    1−λ 与 1−λ+λ²，λ∈(0,1) 时不等。 -/
theorem sinkToPoint_noncommutative
    {ι : Type} [DecidableEq ι] {p q : ι} {lam : ℝ}
    (hpq : p ≠ q) (hlam0 : 0 < lam) :
    ∃ v : ι → ℝ,
      sinkToPoint p lam (sinkToPoint q lam v) ≠
      sinkToPoint q lam (sinkToPoint p lam v) := by
  let v : ι → ℝ := fun i => if i = p then 1 else 0
  refine ⟨v, ?_⟩
  -- 比较两复合在 p 处的值
  have hv_p : v p = 1 := by simp [v]
  have hv_q : v q = 0 := by
    simp [v, hpq.symm]
  have h1 : sinkToPoint p lam (sinkToPoint q lam v) p = 1 - lam := by
    unfold sinkToPoint
    rw [hv_p, hv_q]
    ring
  have h2 : sinkToPoint q lam (sinkToPoint p lam v) p = 1 - lam + lam ^ 2 := by
    unfold sinkToPoint
    rw [hv_p, hv_q]
    ring
  intro hfun
  have hval := congrArg (fun w : ι → ℝ => w p) hfun
  change sinkToPoint p lam (sinkToPoint q lam v) p =
      sinkToPoint q lam (sinkToPoint p lam v) p at hval
  rw [h1, h2] at hval
  have hneq : 1 - lam ≠ 1 - lam + lam ^ 2 := by
    intro h
    have hsq : lam ^ 2 = 0 := by linarith
    have hz : lam = 0 := sq_eq_zero_iff.mp hsq
    exact (ne_of_gt hlam0) hz
  exact hneq hval

-- ---------------------------------------------------------------------------
-- YM3 ★★ 交换差公式
--   在汇点 p 处：T_p(T_q v) − T_q(T_p v) = λ²(v_q − v_p)。
--   形状：非交换项的强度 = 收缩强度² × 场梯度 ——
--   与 [A,A] 的「与场值相关 + 非交换」同形状（解释层对应）。
-- ---------------------------------------------------------------------------

/-- ★★ YM3：交换差公式。
    (T_p ∘ T_q − T_q ∘ T_p) 在 p 处 = λ²·(v_q − v_p)。
    精确离散定理（ring 证明）；到 [A,A] 的连续极限未证明（诚实边界）。 -/
theorem sinkToPoint_commutator_formula
    {ι : Type} (p q : ι) (lam : ℝ) (v : ι → ℝ) :
    sinkToPoint p lam (sinkToPoint q lam v) p -
        sinkToPoint q lam (sinkToPoint p lam v) p
      = lam ^ 2 * (v q - v p) := by
  unfold sinkToPoint
  ring

/-- ★ YM3b：交换差的绝对值 = λ² × |场梯度| —— 非交换项随收缩强度平方
    增长，随两汇点的场差增长。 -/
theorem commutator_grows_with_gradient
    {ι : Type} (p q : ι) (lam : ℝ) (v : ι → ℝ) :
    |sinkToPoint p lam (sinkToPoint q lam v) p -
        sinkToPoint q lam (sinkToPoint p lam v) p|
      = lam ^ 2 * |v q - v p| := by
  rw [sinkToPoint_commutator_formula]
  rw [abs_mul, abs_of_nonneg (sq_nonneg lam)]

end ProjectionPhysics.YangMillsSeed