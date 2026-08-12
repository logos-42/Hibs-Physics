-- ProjectionPhysics — PauliMathlib：Clifford 核心的 mathlib 重写版
--
-- 与 ProjectionPhysics/Clifford.lean（core Lean 手写 ℂ/Mat2）对照，
-- 本模块用 mathlib 的 2×2 矩阵 + ℂ 证明同样的核心定理：
--   C1' σ₁² = σ₂² = σ₃² = I
--   C2' σ₁σ₂ + σ₂σ₁ = 0（反交换 = Clifford 关系）
--   C3' (σ₁σ₂)² = -I（★ 虚数单位 i 的涌现）
--   C4' σ₃ = -i·σ₁σ₂（第三个生成元从前两个涌现）
--
-- 目的：展示"利用 mathlib"后证明的简化（simp + ring 即可，
-- 无需逐分量展开 ℂ 的 re/im 到 Int 再 omega）。
-- 注：实数 2×2 矩阵无法容纳三个平方=I 的反交换生成元
-- （第三个方向必须是虚数——这正是 i 涌现的几何意义），
-- 故用 mathlib 内建 ℂ。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

noncomputable section
open Matrix

namespace PauliMathlib

/-- 2×2 复矩阵（对应项目 Clifford 的 Mat2）。 -/
abbrev Mat2C : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- σ₁ = [[0, 1], [1, 0]]（x 方向自旋生成元）。 -/
def σ₁ : Mat2C := !![ 0, 1; 1, 0 ]

/-- σ₂ = [[0, -i], [i, 0]]（y 方向——含虚数单位，同项目 Clifford）。 -/
def σ₂ : Mat2C := !![ 0, -Complex.I; Complex.I, 0 ]

/-- σ₃ = [[1, 0], [0, -1]]（z 方向自旋生成元）。 -/
def σ₃ : Mat2C := !![ 1, 0; 0, -1 ]

/-- ★ C1'：生成元平方 = 单位矩阵（度规正定方向）。 -/
theorem sigma1_sq : σ₁ * σ₁ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, Matrix.mul_apply] <;> ring

theorem sigma2_sq : σ₂ * σ₂ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₂, Matrix.mul_apply] <;> ring

theorem sigma3_sq : σ₃ * σ₃ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₃, Matrix.mul_apply] <;> ring

/-- ★ C2'：反交换 σ₁σ₂ + σ₂σ₁ = 0（Clifford 关系，旋量的代数根源）。 -/
theorem sigma1_sigma2_anticommute :
    σ₁ * σ₂ + σ₂ * σ₁ = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, Matrix.mul_apply] <;> ring

/-- ★ C3'：(σ₁σ₂)² = -1（虚数单位 i 从矩阵涌现——
    两个反交换的平方为 I 的生成元之积给出 -1）。 -/
theorem sigma12_sq : (σ₁ * σ₂) * (σ₁ * σ₂) = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, Matrix.mul_apply] <;> ring

/-- ★ C4'：σ₃ = -i·σ₁σ₂（第三个生成元从前两个涌现，
    对应项目 C4"法向量从平面内运动涌现"）。 -/
theorem sigma3_from_sigma12 : σ₃ = (-Complex.I : ℂ) • (σ₁ * σ₂) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, σ₃, Matrix.mul_apply] <;> ring

/-- 汇总：Clifford 三定理在 mathlib 下同时成立（对照 Clifford.lean C1-C3）。 -/
theorem clifford_core_mathlib :
    (σ₁ * σ₁ = 1) ∧ (σ₂ * σ₂ = 1) ∧
    (σ₁ * σ₂ + σ₂ * σ₁ = 0) ∧ ((σ₁ * σ₂) * (σ₁ * σ₂) = -1) := by
  constructor
  · exact sigma1_sq
  constructor
  · exact sigma2_sq
  constructor
  · exact sigma1_sigma2_anticommute
  · exact sigma12_sq

end PauliMathlib

end
