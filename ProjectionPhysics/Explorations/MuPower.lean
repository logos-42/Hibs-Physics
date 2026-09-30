-- ProjectionPhysics — MuPower：μ 的功率账本 + 与胶球 N 的同源检验（MW1–MW6）
--
-- leo（2026-09-30）：「物理学是简单的、自洽的，或许胶球的产生和 μ 也有关系…
-- 先做这次的探索」。本模块只形式化**代数内核**，不含新物理：
--
--   MW1  端点：净流为零 ⟹ μ = 1；毛 = 净（完全同向）⟹ μ = 0
--   MW2  功率账本：W = ε·gross·(1−μ) = ε·净残余（同一 gross 下与 μ 仿射）
--   MW3  ★ 斜率恒定：ΔW = −ε·gross·Δμ —— **每单位 μ 的价格只随 gross 走，与 μ 位置无关**
--   MW4  ★ 同 N 不同 μ：(1,1,0) 与 (2,−1,0) 都给 N = 3（RT3 的 Q），但 μ = 0 与 2/3
--   MW5  ★ 同 μ 不同 N：(1,1,0) 与 (1,1,1) 都 μ = 0，但 N = 3 与 6
--        ⟹ MW4/MW5 合起来：**N 与 μ 是同一整数载体的两个泛函，且互不决定**
--           （"同源"成立，"互相决定"不成立 —— 这就是本次探索要交回 leo 校准的那条）
--   MW6  奇偶律（有界枚举版）：毛与净**同奇偶** ⟹ 残余量子与 gross 必须配对
--        （一般形式的证明 = Σ|nᵢ| ≡ Σnᵢ ≡ |Σnᵢ| (mod 2)，本模块只做 Fin 5 枚举）
--
-- 复用：N 的定义与 RT3 的 Q 直接用 RingTwist 里的（不重复定义）。
-- 诚实边界：μ = 1 − |净|/毛 与 W = ε·净 都是**模型选择**；ε 无第一性实现。

import ProjectionPhysics.Explorations.RingTwist
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProjectionPhysics.MuPower

open ProjectionPhysics.RingTwist (Q)

/-- 抵消度泛函（整数向量的符号泛函）：μ = 1 − |净|/毛。 -/
noncomputable def muOf (a b c : ℤ) : ℝ :=
  1 - |(((a + b + c : ℤ) : ℝ))| / (|((a : ℝ))| + |((b : ℝ))| + |((c : ℝ))|)

/-- MW1：μ 的两个端点 —— 完全同向（毛 = 净）⟹ μ = 0；净流为零 ⟹ μ = 1。 -/
theorem MW1_mu_endpoints (gross : ℝ) (hg : gross ≠ 0) :
    (1 - 0 / gross = 1) ∧ (1 - gross / gross = 0) := by
  constructor
  · rw [zero_div, sub_zero]
  · rw [div_self hg, sub_self]

/-- MW2：功率账本 —— W = ε·gross·(1−μ) 等于 ε×净残余。 -/
theorem MW2_W_is_net (eps gross n mu : ℝ) (hg : gross ≠ 0) (h : mu = 1 - n / gross) :
    eps * gross * (1 - mu) = eps * n := by
  rw [h]
  field_simp
  ring

/-- MW3：★ 同一 gross 下 W 对 μ 的斜率恒定（−ε·gross）⟹ 每单位 μ 的价格与 μ 位置无关。 -/
theorem MW3_slope_constant (eps gross mu1 mu2 n1 n2 : ℝ) (hg : gross ≠ 0)
    (h1 : mu1 = 1 - n1 / gross) (h2 : mu2 = 1 - n2 / gross) :
    eps * gross * (mu2 - mu1) = eps * (n1 - n2) := by
  rw [h1, h2]
  field_simp
  ring

/-- MW4：★ 同 N 不同 μ —— (1,1,0) 与 (2,−1,0) 都是 N = 3，但 μ = 0 与 2/3。
    ⟹ N 不决定 μ。 -/
theorem MW4_same_N_diff_mu :
    Q 1 1 0 = 3 ∧ Q 2 (-1) 0 = 3 ∧ muOf 1 1 0 = 0 ∧ muOf 2 (-1) 0 = 2 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [Q, muOf, abs_of_nonneg]

/-- MW5：★ 同 μ 不同 N —— (1,1,0) 与 (1,1,1) 都 μ = 0，但 N = 3 与 6。
    ⟹ μ 不决定 N。与 MW4 合起来：同源但互不决定。 -/
theorem MW5_same_mu_diff_N :
    Q 1 1 0 = 3 ∧ Q 1 1 1 = 6 ∧ muOf 1 1 0 = 0 ∧ muOf 1 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [Q, muOf, abs_of_nonneg]

/-- MW6：奇偶律（Fin 5 有界枚举版）—— 毛与净同奇偶 ⟹ 残余量子必须与 gross 配对。
    一般形式 Σ|nᵢ| ≡ Σnᵢ ≡ |Σnᵢ| (mod 2) 未形式化（本模块只做 |nᵢ| ≤ 2 的枚举）。 -/
theorem MW6_parity (a b c : Fin 5) :
    (((a : ℤ) - 2).natAbs + ((b : ℤ) - 2).natAbs + ((c : ℤ) - 2).natAbs) % 2 =
      (((a : ℤ) - 2) + ((b : ℤ) - 2) + ((c : ℤ) - 2)).natAbs % 2 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

end ProjectionPhysics.MuPower
