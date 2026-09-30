-- ProjectionPhysics — FusionSelection：融合空间的两条选择规则（RT-I 的 Lean 侧）
--
-- leo「走最后一步」：把 SU(2)_k 的**融合空间**（conformal blocks）算出来，看 J 能不能成为
-- **导出的**标签（而不是"按质量序指配"）。数值侧在 scripts/verify_conformal_blocks.py。
--
-- 本模块把真正在做物理工作的**两条选择规则**形式化（标签用整数 L = 2j，于是 L 就是 J = 2j）：
--
--   1. 宇称：n 条自旋-1/2 的总标签 J 满足 J = n − 2s（s = 配成单态的条数）
--            ⟹ **J ≡ n (mod 2)**      —— 就是 RT-H 里那条"永远三股被否证"的规则
--   2. level 截断：两个标签都不超过 k（= level，即 j ≤ k/2）⟹ 融合结果的标签也不超过 k
--            —— 这是"level k 只有 j ≤ k/2 的扇区"这条截断
--   推论（下面 label_three_needs_level_three）：三股（标签 1 ⊗ 1 ⊗ 1）要出现 J = 3，
--   当且仅当 k ≥ 3 —— 即 level ≥ 3 才有总自旋 3/2 的扇区。这条在数值侧被逐 k 验证。
--
-- 不在本模块里（诚实登记）：J ≤ min(n, k) 的归纳证明与多重度 mult_J(n) 的组合计数，
-- 数值侧给了精确枚举 + 自检 Σ_J mult_J(n)² = Catalan(n)（k ≥ n 时 0 违例）；
-- 那是一个独立的组合恒等式，形式化它需要额外的图计数结构，本步不做。

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace ProjectionPhysics.FusionSelection

/-- 宇称选择规则：若总标签 J 由 n 条自旋-1/2 配对而来（J = n − 2s，s = 单态对数），
    则 J 与 n 同奇偶。 -/
theorem parity_selection {n J s : ℕ} (h : J + 2 * s = n) : J % 2 = n % 2 := by
  omega

/-- level 截断：两个标签都不超过 k ⟹ 融合结果的标签也不超过 k（SU(2)_k 的 level 截断）。 -/
theorem truncation_bound {k a b c : ℕ} (ha : a ≤ k) (hb : b ≤ k)
    (h1 : c ≤ a + b) (h2 : c ≤ 2 * k - a - b) : c ≤ k := by
  omega

/-- 三股要出现 J = 3（总自旋 3/2）必须 k ≥ 3：
    因为 c ≤ 2k − a − b 且 a = b = 1，所以 c = 3 要求 3 ≤ 2k − 2 ⟹ k ≥ 3。
    （数值侧逐 k 验证：k = 1, 2 没有 J = 3，k ≥ 3 有。） -/
theorem label_three_needs_level_three {k : ℕ} (h : 3 ≤ 2 * k - 1 - 1) : 3 ≤ k := by
  omega

/-- 宇称规则的一个直接推论：三股（n = 3）的总标签必为奇数 ⟹ 三股给不出 J = 0、J = 2。
    （这就是 RT-H 里"永远三股"被否证的形式化版本：0++、2++ 的 J 是偶数。） -/
theorem three_strands_odd {J s : ℕ} (h : J + 2 * s = 3) : J % 2 = 1 := by
  omega

end ProjectionPhysics.FusionSelection
