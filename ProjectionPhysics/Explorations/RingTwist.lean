-- ProjectionPhysics — RingTwist：环扭转 → 条数 N 与 μ 的连接数写法（RT1–RT7）
--
-- leo（2026-09-29）：在原扭量数学上做**环扭转**，形成比普通螺旋线圈更扭转的
-- "扭量螺旋环"；环本身也带时空的变化 ⟹ 或许可以解释质量来源。
--
-- 本模块只形式化**代数内核**（不含新物理），要接的两个缺口：
--   * Twistor.lean TW6：质量 m = |⟨π₁,π₂⟩|（两扭量的相对方向）——缺"谁定这个方向"
--   * 胶球账本 m² = N·M₀²，N ∈ {3,6,7}：仓库自己标注"N 仍无第一性解释"
--
-- 数学对应：
--   RT1  ring_identity：环形计数二次型可写成平方和
--        Q(a,b,c) = a²+b²+c²+ab+bc+ca = ½[(a+b)²+(b+c)²+(c+a)²]
--        （交叉项 = "三个方向互相耦合"。与 SH3 形成对照：SH3 说**反对称**耦合下交叉项被消灭，
--          这里说**对称**耦合下交叉项留下来 —— 而它正是 N=7 需要的东西）
--   RT2  ★ nonneg / definite：Q ≥ 0；Q = 0 ⟺ a = b = c = 0
--   RT3  ★ ladder：Q(1,1,0) = 3、Q(1,1,1) = 6、Q(2,1,0) = 7 —— 胶球 N 序列
--   RT4  diag_no_seven（Fin 5 有界版）：三个**独立**绕数的平方和在 |nᵢ| ≤ 2 内取不到 7
--        （一般情形 = Legendre 三平方定理：7 = 4⁰(8·0+7) 不可表；见脚本注释与 wiki）
--        ⟹ 仓库 0-+ 的 N=7 否掉"三个独立绕数"模型 ⟹ 集体（非对角）项是必需的
--   RT7  diag_small（Fin 3 有界版）：三个独立绕数在 |nᵢ| ≤ 1 内只能给 0、1、2、3
--        ⟹ 6 与 7 都需要"被扭过两圈以上"的环（扭转余量）
--   RT5  半整数扭转 ⟹ 自旋结构：半整数圈回到 −1，整数圈回到 +1（双覆盖）
--   RT6  μ 的连接数写法有界：μ = 1 − |net| / gross ∈ [0,1]（|net| ≤ gross）
--
-- 诚实：本模块全是代数恒等式与有界枚举（真但平凡）；"扭转 → N"是**模型选择**，
-- 这里只**否掉**对角模型并给出最小集体实现，**没有**导出选择规则。

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ProjectionPhysics.RingTwist

/-- 环形（三方向对称耦合）计数二次型：Q = a²+b²+c²+ab+bc+ca。 -/
def Q (a b c : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a

/-- RT1：环形恒等式 —— Q 可写成三个平方和的一半。 -/
theorem RT1_ring_identity (a b c : ℤ) :
    2 * Q a b c = (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 := by
  simp only [Q]
  ring

/-- RT2a：非负性（质量平方的条数因子不会为负）。 -/
theorem RT2_nonneg (a b c : ℤ) : 0 ≤ Q a b c := by
  have h := RT1_ring_identity a b c
  nlinarith [sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]

/-- RT2b：正定 —— 只有零态给出零条数。 -/
theorem RT2_definite (a b c : ℤ) (h : Q a b c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hsum : (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 = 0 := by
    have h1 := RT1_ring_identity a b c
    omega
  have h1 : (a + b) ^ 2 = 0 :=
    by nlinarith [sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]
  have h2 : (b + c) ^ 2 = 0 :=
    by nlinarith [sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]
  have h3 : (c + a) ^ 2 = 0 :=
    by nlinarith [sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]
  have e1 : a + b = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using h1)
  have e2 : b + c = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using h2)
  have e3 : c + a = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using h3)
  omega

/-- RT3：★ 胶球 N 序列 {3, 6, 7} 的三个最小集体实现。 -/
theorem RT3_ladder : Q 1 1 0 = 3 ∧ Q 1 1 1 = 6 ∧ Q 2 1 0 = 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Q]

/-- RT4：三个独立绕数（对角型）在 |nᵢ| ≤ 2 内取不到 7（Fin 5 有界枚举）。 -/
theorem RT4_diag_no_seven (a b c : Fin 5) :
    ((a : ℤ) - 2) ^ 2 + ((b : ℤ) - 2) ^ 2 + ((c : ℤ) - 2) ^ 2 ≠ 7 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num

/-- RT7：三个独立绕数在 |nᵢ| ≤ 1 内只能给 0、1、2、3
    ⟹ 6 与 7 都需要"被扭过两圈以上"的环（扭转余量）。 -/
theorem RT7_diag_small (a b c : Fin 3) :
    ((a : ℤ) - 1) ^ 2 + ((b : ℤ) - 1) ^ 2 + ((c : ℤ) - 1) ^ 2 ≤ 3 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num

/-- RT5a：半整数扭转（奇数个半圈）⟹ 相位 −1 —— 自旋双覆盖。
    扭转圈数取自然数（2n+1 个半圈 ⟹ 相位 −1）;负数情形由 cos 的偶函数性直接得到。 -/
theorem RT5_half_turn (n : ℕ) : Real.cos ((2 * n + 1 : ℕ) * Real.pi) = -1 := by
  rw [Real.cos_nat_mul_pi]
  exact Odd.neg_one_pow ⟨n, rfl⟩

/-- RT5b：整数个半圈（偶数）⟹ 相位 +1。 -/
theorem RT5_full_turn (n : ℕ) : Real.cos ((2 * n : ℕ) * Real.pi) = 1 := by
  rw [Real.cos_nat_mul_pi]
  exact Even.neg_one_pow ⟨n, by ring⟩

/-- RT5c：最小见证 —— 转一圈（π 的半整数扭转）回到 −1。 -/
theorem RT5_spinor_double_cover : Real.cos Real.pi = -1 := Real.cos_pi

/-- RT6：μ 的连接数写法 μ = 1 − |net| / gross 落在 [0,1]（当 |net| ≤ gross）。 -/
theorem RT6_mu_bounds (gross net : ℝ) (hg : 0 < gross) (h : |net| ≤ gross) :
    0 ≤ 1 - |net| / gross ∧ 1 - |net| / gross ≤ 1 := by
  have hnn : 0 ≤ |net| := abs_nonneg net
  constructor
  · have hle : |net| / gross ≤ 1 := by
      rw [div_le_one hg]
      exact h
    linarith
  · have hge : 0 ≤ |net| / gross := div_nonneg hnn (le_of_lt hg)
    linarith

end ProjectionPhysics.RingTwist
