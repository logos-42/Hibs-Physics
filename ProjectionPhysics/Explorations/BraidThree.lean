-- ProjectionPhysics — BraidThree：三股编织群 B₃ 的既约 Burau 表示与其**中心元**
--
-- leo（2026-09-29）：按三股试试 —— 用 B₃ 的 2 维不可约表示（既约 Burau）给 J^PC 找一个
-- **可导出的**（而不是"按质量序指派"的）量子数来源。
--
-- 本模块证明（都不含新物理，纯代数）：
--   BT1  braid 关系：σ₁σ₂σ₁ = σ₂σ₁σ₂（B₃ 的定义关系）
--   BT2  ★ 全扭转（中心元）是**纯量**：(σ₁σ₂)³ = t³·I
--   BT3  ★ 推论：Δ := (σ₁σ₂)³ 与**任意** 2×2 矩阵交换 ⟹ 从它读出的相位/符号对**所有** braid 词
--         都一样 ⟹ **这个表示无法给不同态不同的量子数** —— 本轮最硬的一条否定
--   BT4  在 t = −1（S₃ 点）Δ 的两个对角元都 = −1 ⟹ 唯一的 ℤ₂ 只有一个取值（无态依赖）
--   BT5  Δ 的行列式 = t⁶、迹 = 2t³（特征值只有 t³，二重）—— 数值层的相位阶梯由此得出
--
-- 为什么重要（接到 RT-F 的穷举否定）：RT-F 用 (Σ|nᵢ| mod 2, μ̄₃) 穷举 256 条规则全中 = 0，
-- 说明"少了输入"。本轮把**最自然的另一个来源**（B₃ 表示的中心元相位）也判掉了：
-- 它在 2 维不可约表示里是纯量 ⟹ 天然不含态依赖信息。
-- ⟹ 下一步必须离开 2 维：Temperley–Lieb / Jones 表示在 level k ≥ 4 才有 j = 2 以上的自旋。

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
namespace ProjectionPhysics.BraidThree

open Matrix

/-- B₃ 的既约 Burau 表示：σ₁ ↦ !![−t, 1; 0, 1]。 -/
def b1 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) := !![-(Polynomial.X : Polynomial ℤ), 1; 0, 1]

/-- B₃ 的既约 Burau 表示：σ₂ ↦ !![1, 0; t, −t]。 -/
def b2 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  !![1, 0; (Polynomial.X : Polynomial ℤ), -(Polynomial.X : Polynomial ℤ)]

/-- 全扭转（中心元）写成显式对角矩阵：t³·I。 -/
def Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  !![(Polynomial.X : Polynomial ℤ) ^ 3, 0; 0, (Polynomial.X : Polynomial ℤ) ^ 3]

/-- BT1：braid 关系 σ₁σ₂σ₁ = σ₂σ₁σ₂（B₃ 的定义关系）。 -/
theorem BT1_braid_relation : b1 * b2 * b1 = b2 * b1 * b2 := by
  ext i j
  all_goals (fin_cases i <;> fin_cases j <;> simp [b1, b2, mul_apply, Fin.sum_univ_two])

/-- BT2：★ 全扭转（中心元）是**纯量**：(σ₁σ₂)³ = t³·I。 -/
theorem BT2_full_twist_is_scalar : (b1 * b2) ^ 3 = Delta := by
  simp only [pow_succ]
  ext i j
  all_goals (fin_cases i <;> fin_cases j <;>
    simp [b1, b2, Delta, mul_apply, Fin.sum_univ_two] <;> ring)

/-- BT3：★ 推论 —— Δ := (σ₁σ₂)³ 与**任意** 2×2 矩阵交换。
    即：从 Δ 读出的任何相位/符号对**所有** braid 词相同 ⟹ 该表示不含态依赖的量子数。 -/
theorem BT3_full_twist_commutes_with_everything (M : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) :
    (b1 * b2) ^ 3 * M = M * (b1 * b2) ^ 3 := by
  rw [BT2_full_twist_is_scalar]
  ext i j
  all_goals (fin_cases i <;> fin_cases j <;> simp [Delta, mul_apply] <;> ring)

/-- BT3′：特别地 Δ 与两个生成元都交换。 -/
theorem BT3_commutes_with_generators :
    (b1 * b2) ^ 3 * b1 = b1 * (b1 * b2) ^ 3 ∧ (b1 * b2) ^ 3 * b2 = b2 * (b1 * b2) ^ 3 :=
  ⟨BT3_full_twist_commutes_with_everything b1, BT3_full_twist_commutes_with_everything b2⟩

/-- BT4：在 t = −1（S₃ 点）Δ 的两个对角元都 = −1 ⟹ 唯一的 ℤ₂ 只有一个取值（无态依赖）。 -/
theorem BT4_at_minus_one : ∀ i : Fin 2, Polynomial.eval (-1 : ℤ) (Delta i i) = -1 := by
  intro i
  fin_cases i <;> simp [Delta]

/-- BT5a：Δ 的行列式 = t⁶。 -/
theorem BT5_det : Delta.det = (Polynomial.X : Polynomial ℤ) ^ 6 := by
  simp [Delta, det_fin_two]
  ring

/-- BT5b：Δ 的迹 = 2t³（⟹ 特征值只有 t³，二重）。 -/
theorem BT5_trace : Delta.trace = 2 * (Polynomial.X : Polynomial ℤ) ^ 3 := by
  simp [Delta, trace_fin_two]
  ring

end ProjectionPhysics.BraidThree
