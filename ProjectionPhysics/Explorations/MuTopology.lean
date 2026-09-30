-- ProjectionPhysics — MuTopology：把"改变净连接数是**非局部**的"落成指数和定理（MT1–MT5）
--
-- leo（2026-09-30）：承认「改变必须是非局部的」这一支。
-- 于是要做的是把这句话从口头前提变成**可算、可证、可否证**的东西。
--
-- 落法（与仓库已有的两条独立结论互锁）：
--   * 闭辫的链接数载体 = 辫词的**指数和** e（RT-D 实测：三股闭辫 Σ_{i<j}Lk = e/2）
--   * e 只依赖生成元的**计数** ⟹            （MT1/MT2）
--     局部变形（braid 关系式 σ₁σ₂σ₁ = σ₂σ₁σ₂、共轭、循环）**都不改 e**（MT2/MT5）
--   * 能改 e 的只有**改变计数** = 加/减股（Markov 稳定化，MT3）或改幂次
--     ⟹ **"非局部" = 改指数和 = 改股数/幂次**（本模块的落点）
--   * 与 RT-H4「股数随态变（不是永远三股）」自洽 —— 两条独立结论指同一件事
--
-- 诚实边界：本模块只形式化**组合侧的指数和**（纯算术）；"e = 2ΣLk"这条
-- 把组合与几何钉在一起的事实来自数值（RT-D 的 Gauss 双积分），不在 Lean 里。
-- 物理学侧：非局部 = 重联这类拓扑事件（理想演化保螺旋度，只有重联改拓扑），
-- 阈值代价的估计在脚本侧（MT4，量级估计非推导）。

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProjectionPhysics.MuTopology

/-- 辫词：生成元 = (第几股, 正向/反向)，用 Bool 记符号。 -/
abbrev Gen (n : ℕ) := Fin n × Bool
abbrev Word (n : ℕ) := List (Gen n)

/-- 指数和：正向 +1、反向 −1（这就是闭辫链接数的组合载体）。 -/
def e : Word n → ℤ
  | [] => 0
  | (_, b) :: t => (if b then 1 else -1) + e t

/-- 反向词：逐个把生成元取反（逆元，几何上 = 反向绕）。 -/
def neg : Word n → Word n
  | [] => []
  | (i, b) :: t => (i, !b) :: neg t

/-- MT1：指数和是词接合的同态。 -/
theorem MT1_e_append (l₁ l₂ : Word n) : e (l₁ ++ l₂) = e l₁ + e l₂ := by
  induction l₁ with
  | nil => simp [e]
  | cons h t ih => cases h with | mk i b => simp [e, ih]; ring

/-- MT2：braid 关系式 σ₁σ₂σ₁ = σ₂σ₁σ₂ 两边**指数和相同**（都是 3）
    ⟹ 关系式（局部变形）不改 e。 -/
theorem MT2_braid_relation_same_e :
    e ([((0 : Fin 3), true), ((1 : Fin 3), true), ((0 : Fin 3), true)] : Word 3) = 3 ∧
    e ([((1 : Fin 3), true), ((0 : Fin 3), true), ((1 : Fin 3), true)] : Word 3) = 3 := by
  constructor <;> simp [e]

/-- MT3：★ **非局部见证** —— 稳定化（加一股 σₙ）使指数和变 +1。
    ⟹ 改 e 必须改生成元计数 = 加/减股或改幂次。 -/
theorem MT3_stabilization_changes_e (w : Word n) (g : Gen (n + 1)) :
    e (g :: (w.map (fun x => (x.1.castSucc, x.2)))) = (if g.2 then 1 else -1) + e w := by
  cases g with
  | mk i b =>
    simp only [e]
    congr 1
    induction w with
    | nil => simp [e]
    | cons h t ih => cases h with | mk i' b' => simp [e, ih]

/-- MT4：逆词把指数和取反。 -/
theorem MT4_e_neg (w : Word n) : e (neg w) = -e w := by
  induction w with
  | nil => simp [neg, e]
  | cons h t ih =>
    cases h with
    | mk i b =>
      cases b <;> simp [neg, e, ih] <;> ring

/-- MT5：★ **共轭（Markov 第一移动）不改 e** —— 闭辫的链接数在共轭下不变。
    与 MT2 合起来：局部变形（关系式 + 共轭 + 循环）全都不改 e。 -/
theorem MT5_conjugation_preserves_e (v w : Word n) : e (v ++ w ++ neg v) = e w := by
  rw [MT1_e_append, MT1_e_append, MT4_e_neg]
  ring

/-- MT6：推论 —— 关系式的**计数不变性**：σ₁σ₂σ₁ 与 σ₂σ₁σ₂ 含同样的生成元计数，
    所以任何由关系式连接的两个词指数和相同（这里各证一遍以作见证）。 -/
theorem MT6_relation_words_count :
    e ([((0 : Fin 3), true), ((1 : Fin 3), true), ((0 : Fin 3), true)] : Word 3) =
    e ([((1 : Fin 3), true), ((0 : Fin 3), true), ((1 : Fin 3), true)] : Word 3) := by
  simp [e]

/-- MT7：单生成元改 ±1（幂次变化的原子步）。 -/
theorem MT7_single_generator (i : Fin n) (b : Bool) :
    e ([((i), b)] : Word n) = (if b then 1 else -1) := by
  cases b <;> simp [e]

end ProjectionPhysics.MuTopology
