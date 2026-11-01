-- ProjectionPhysics — AlignCriterion：ALIGN 的可算判据 + 非阿贝尔性的代数来源（AC1–AC4）
--
-- leo（2026-11-01）：「把 ALIGN 翻译成可算的判据」「色载体是 cycle3 这个置换，
--   非阿贝尔性到底来自哪里——查清楚，否则那个形容词悬空」。
--
-- 两件事，各给定理：
--
-- ① **ALIGN 的判据**：ALIGN 说「闭合回路的 holonomy 有共同対角框架」。
--    共同対角框架 ⟹ 两两可交换（AC1/AC2）。它的**逆否**就是判据：
--    只要存在两个不交换的 holonomy，就不存在共同対角框架，ALIGN 在那里失效。
--    （反方向「可交换 + 可对角化 ⟹ 有共同特征基」需要谱定理，本模块不做，登记开口。）
--
-- ② **非阿贝尔性从哪来**：色载体里的 `cycle3` 是一个三循环置换（Weyl 群元素），
--    看起来"只有离散的"。但微分意义下不是：把环面元素（对角）与 Weyl 置换做
--    **交换子**，得到的是**非对角的根方向**（AC3/AC4）。所以
--      · 可对角（环面）给的是**极大环面**；
--      · 加一个 Weyl 置换做李括号，就生成 su(3) 的根空间 ⟹ 李代数不是环面；
--      · 有限乘积生成的**群**仍然只是环面的正规化子 N(T)（这一条是离散的）。
--    ⟹ 「非阿贝尔」在**无穷小/代数**层面成立（规范场论需要的正是这个层面），
--      而在**大规范变换**层面被限制在 N(T)。
--
--   AC1 `diag_mul_comm`：两个对角矩阵可交换
--   AC2 `common_frame_commutes`：同一基下对角的两个矩阵可交换
--        ⟹ 逆否 = ALIGN 的可判死判据（不交换 ⟹ 无共同对角框架）
--   AC3 `commutator_entry`：`cycle3` 与 `diag(1,2,3)` 的交换子在 (0,1) 处等于 −1
--   AC4 `commutator_offdiag_ne_zero`：该交换子有非对角元 ≠ 0 ⟹ 根方向出现
--
-- 诚实边界（写死）：
--   · 反方向（可交换 + 可对角化 ⟹ 共同特征基）未形式化（需谱定理）。ALIGN 的判据
--     只用逆否，因此不受影响；但"ALIGN 成立 ⟺ 两两可交换"的**完整**等价未证。
--   · AC3/AC4 是**一个具体见证**（cycle3、diag123），不是"任意 Weyl 元素"的一般定理。
--   · 「有限乘积生成的群 = N(T)」未形式化（Bruhat 分解级事实），只在注释里陈述。
--   · 不声称 Pontryagin 指数；反射正性 / 测度 / 连续极限仍为零。

import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section

namespace ProjectionPhysics.AlignCriterion

open Matrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- 对角：等于某个对角矩阵。 -/
def IsDiag (D : Mat3) : Prop := ∃ d : Fin 3 → ℂ, D = Matrix.diagonal d

/-- AC1：两个对角矩阵可交换。 -/
theorem diag_mul_comm (D₁ D₂ : Mat3) (h₁ : IsDiag D₁) (h₂ : IsDiag D₂) :
    D₁ * D₂ = D₂ * D₁ := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm (a i) (b i)

/-- AC2 ★★★ **共同对角框架 ⟹ 可交换**。
    两个矩阵若在同一个基 $P$ 下都是对角的，则可交换。
    逆否即 ALIGN 的判据：存在不交换的 holonomy ⟹ 没有共同对角框架。 -/
theorem common_frame_commutes (P Pinv D₁ D₂ : Mat3) (hP : Pinv * P = 1)
    (h₁ : IsDiag D₁) (h₂ : IsDiag D₂) :
    (P * D₁ * Pinv) * (P * D₂ * Pinv) = (P * D₂ * Pinv) * (P * D₁ * Pinv) := by
  have hcomm : D₁ * D₂ = D₂ * D₁ := diag_mul_comm D₁ D₂ h₁ h₂
  calc (P * D₁ * Pinv) * (P * D₂ * Pinv)
      = P * D₁ * (Pinv * P) * D₂ * Pinv := by noncomm_ring
    _ = P * D₁ * 1 * D₂ * Pinv := by rw [hP]
    _ = P * (D₁ * D₂) * Pinv := by noncomm_ring
    _ = P * (D₂ * D₁) * Pinv := by rw [hcomm]
    _ = P * D₂ * 1 * D₁ * Pinv := by noncomm_ring
    _ = P * D₂ * (Pinv * P) * D₁ * Pinv := by rw [← hP]
    _ = (P * D₂ * Pinv) * (P * D₁ * Pinv) := by noncomm_ring

/-- 色载体里的三循环置换（`ColorOctet` 的 `cycle3`）。 -/
def cycle3 : Mat3 := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- 一个对角元素（`ColorOctet` 的 `diag123`）。 -/
def diag123 : Mat3 := !![1, 0, 0; 0, 2, 0; 0, 0, 3]

/-- AC3 ★★★ 交换子的 (0,1) 元等于 −1（对角元素与 Weyl 置换的交换子不消）。 -/
theorem commutator_entry : (diag123 * cycle3 - cycle3 * diag123) 0 1 = -1 := by
  simp [diag123, cycle3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply]
  norm_num

/-- AC4 ★★★ **根方向出现**：对角元素与 Weyl 置换的交换子非零且有**非对角**元
    ⟹ 李代数不只是环面（对角 × 置换的李括号生成根空间）。
    这是「非阿贝尔」在无穷小层面成立的形式内容。 -/
theorem commutator_offdiag_ne_zero : (diag123 * cycle3 - cycle3 * diag123) 0 1 ≠ 0 := by
  rw [commutator_entry]
  norm_num

end ProjectionPhysics.AlignCriterion
