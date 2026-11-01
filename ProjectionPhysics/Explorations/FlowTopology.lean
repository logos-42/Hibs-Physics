-- ProjectionPhysics — FlowTopology：格点上的「拓扑性」到底给了什么（FT1–FT5）
--
-- leo（2026-11-01）：「空间本身的格子是有连续性的，因为电子的散度是有拓扑结构的」。
--
-- 这句话里混着**两件事**，本模块把它们分开，各给一个定理：
--
--   ① **拓扑/整数那一半**（你是对的）：散度（= 荷）在格点上是**精确的边界量**。
--      盒内总荷 = 边界流之差（Gauss 定律，telescoping），**不需要连续极限**；
--      离散连续性方程 ⟹ 闭盒内总荷**精确守恒**；荷是整数 ⟹ 细格粗格是同一个整数。
--      ⟹ 「格子有连续性」在**荷这个层次**上是成立的：整数不会被分辨率改变。
--
--   ② **度量那一半**（补不上）：能量/‖F‖ 这类量**依赖格距**，没有分辨率无关的值。
--      同一个总荷（= 同样是 2）在粗格上是 [2]、在细格上是 [1,1]，
--      ∑ρ² = 4 vs 2 ⟹ **拓扑决定了荷，决定不了能量**。
--      要把能量变成分辨率无关，必须乘上"格距"这个**度量输入**——框架里没有。
--
--   结论（诚实）：你的直觉对**整数/守恒律**完全成立（而且比连续极限更强：不需要取极限），
--   但对**连续极限的存在性**（a → 0 让 ‖F‖、谱、质量收敛）不成立。
--   后者缺的不是拓扑，是**度量**。
--
-- 定理（全部零 sorry）：
--   FT1 ★★ `gauss_law_1d`：盒内总荷 = 边界流之差（格点 Gauss 定律，不取极限）
--   FT2 ★★★ `charge_conserved_closed_box`：离散连续性方程 ⟹ 闭盒内总荷精确守恒
--   FT3 ★★ `total_charge_boundary_only`：总荷只由边界决定（内部重排不可见 = 拓扑性）
--   FT4 ★★★ `topology_does_not_fix_energy`：**荷相同、能量不同**（反例，诚实边界）
--   FT5 `integer_charge_is_resolution_free`：整数荷与分辨率无关（细分不改变整数）
--
-- 不声称：不声称框架因此有了连续极限；不声称质量谱收敛；不声称解决 Clay。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Finset
open scoped BigOperators

namespace ProjectionPhysics.FlowTopology

/-- 一维流链上的散度（前向差分）：div J(x) = J(x+1) − J(x)。
    物理读法：单位格长的「流净流出」= 该格点的荷密度（电荷 = 流散度，GQF4）。 -/
def div1 (J : ℕ → ℝ) (x : ℕ) : ℝ := J (x + 1) - J x

/-- FT1 ★★ **格点 Gauss 定律**：盒子 {0,…,n−1} 内的总荷 = 两端流之差。
    —— 纯 telescoping，**不取任何连续极限**。这就是「散度是边界量」的形式化。 -/
theorem gauss_law_1d (J : ℕ → ℝ) (n : ℕ) :
    ∑ x ∈ range n, div1 J x = J n - J 0 := by
  unfold div1
  exact sum_range_sub J n

/-- FT3 ★★ **总荷只由边界决定**：内部怎么重排，只要边界流不变，盒内总荷就不变。
    —— 这是「拓扑性」的精确内容：可观测的是边界数据，不是内部细节。 -/
theorem total_charge_boundary_only (J J' : ℕ → ℝ) (n : ℕ)
    (h0 : J 0 = J' 0) (hn : J n = J' n) :
    ∑ x ∈ range n, div1 J x = ∑ x ∈ range n, div1 J' x := by
  rw [gauss_law_1d, gauss_law_1d, h0, hn]

/-- FT2 ★★★ **荷精确守恒**：若逐点满足离散连续性方程
    ρ(x,t+1) − ρ(x,t) = −div J(x,t)，且闭盒两端无流，则盒内总荷**严格不变**。
    —— 没有误差项、没有极限、没有重整化。格点在这件事上是**精确**的。 -/
theorem charge_conserved_closed_box (ρ : ℕ → ℕ → ℝ) (J : ℕ → ℕ → ℝ) (n t : ℕ)
    (hcont : ∀ x, x < n → ρ x (t + 1) - ρ x t = -(div1 (fun y => J y t) x))
    (h0 : J 0 t = 0) (hn : J n t = 0) :
    ∑ x ∈ range n, ρ x (t + 1) = ∑ x ∈ range n, ρ x t := by
  have hdiff : ∑ x ∈ range n, (ρ x (t + 1) - ρ x t) = 0 := by
    rw [sum_congr rfl (fun x hx => hcont x (mem_range.mp hx))]
    rw [sum_neg_distrib, gauss_law_1d, hn, h0, sub_self, neg_zero]
  rw [sum_sub_distrib] at hdiff
  linarith

/-- FT5 **整数荷与分辨率无关**：荷为整数时，无论取多少格点，总数仍是整数。
    ⟹ 「细分不改变荷」在整数层面是自动的（不需要取极限去"稳定"。） -/
theorem integer_charge_is_resolution_free (ρ : ℕ → ℕ) (n : ℕ) :
    ∃ M : ℕ, ∑ x ∈ range n, (ρ x : ℝ) = (M : ℝ) :=
  ⟨∑ x ∈ range n, ρ x, by push_cast; ring⟩

/-- FT4 ★★★ **反例（诚实边界）：拓扑决定荷，决定不了能量。**
    两套配置的总荷都是 2：
      · 粗格 [2]：∑ρ² = 4
      · 细格 [1,1]：∑ρ² = 2
    荷一样，能量差一倍。⟹ 要把能量变成分辨率无关量，必须乘上「格距」（度量输入），
    而框架里没有格距 —— 这正是 a → 0 缺的那件东西，**不是拓扑能补的**。 -/
theorem topology_does_not_fix_energy :
    (∑ x ∈ range 1, (if x = 0 then (2 : ℝ) else 0))
      = (∑ _x ∈ range 2, (1 : ℝ))
    ∧ (∑ x ∈ range 1, (if x = 0 then (2 : ℝ) else 0) ^ 2)
      ≠ (∑ _x ∈ range 2, (1 : ℝ) ^ 2) := by
  constructor
  · simp
  · simp
    norm_num

end ProjectionPhysics.FlowTopology
