-- ProjectionPhysics — MinimalCoreMathlib：最小核心命题的 mathlib 重写版
--
-- 与 ProjectionPhysics/MinimalCore.lean（core Lean 手写 Spinor/Mat2）对照，
-- 本模块用 mathlib 的 2×2 复矩阵 + Fin 2 旋量 + 显式分量证明：
--   MC1' spinFlow ψ = σ₁ψ（旋量流）
--   MC2' 非零旋量 ⟹ 锚定质量平方 > 0（★ 核心命题：自旋非零 ⟹ m ≠ 0）
--   MC3' 零旋量 ⟹ 锚定质量平方 = 0（光子边界）
--   MC4' 锚定质量平方 = |ψ₁|² + |ψ₀|²（分量展开——σ₁ 交换分量，
--        不改变"量"，锚定 = 原旋量的量）
--
-- 收获：mathlib 的 2×2 矩阵 + ext/fin_cases/ring 处理分量，
-- |·|² 用 Complex.sq_norm 直接化简，无需手写 ℂ 的 re/im 展开。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

noncomputable section
open Matrix

namespace MinimalCoreMathlib

/-- 2×2 复矩阵。 -/
abbrev Mat2C : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- 旋量（2 分量，Clifford 旋量）。 -/
abbrev Spinor : Type := Fin 2 → ℂ

/-- σ₁ = [[0, 1], [1, 0]]（x 方向自旋生成元，同项目 Clifford）。 -/
def σ₁ : Mat2C := !![ 0, 1; 1, 0 ]

/-- 旋量流：σ₁ψ（空间运动在旋量上的作用）。 -/
def spinFlow (ψ : Spinor) : Spinor := σ₁.mulVec ψ

/-- 锚定质量平方 = 旋量流的范数平方 |(σ₁ψ)₀|² + |(σ₁ψ)₁|²。
    （对应项目 MC1 的 spinFlowAnchorMass） -/
def anchorMassSq (ψ : Spinor) : ℝ :=
  Complex.normSq ((spinFlow ψ) ⟨0, by decide⟩) +
  Complex.normSq ((spinFlow ψ) ⟨1, by decide⟩)

/-- σ₁² = 1（Clifford 关系，mathlib 一行）。 -/
theorem sigma1_sq : σ₁ * σ₁ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, Matrix.mul_apply] <;> ring

/-- σ₁ 交换旋量分量：(σ₁ψ)₀ = ψ₁。 -/
theorem spinFlow_0 (ψ : Spinor) :
    (spinFlow ψ) ⟨0, by decide⟩ = ψ ⟨1, by decide⟩ := by
  unfold spinFlow
  change (∑ j : Fin 2, σ₁ ⟨0, by decide⟩ j * ψ j) = ψ ⟨1, by decide⟩
  simp [σ₁, Fin.sum_univ_two]

/-- σ₁ 交换旋量分量：(σ₁ψ)₁ = ψ₀。 -/
theorem spinFlow_1 (ψ : Spinor) :
    (spinFlow ψ) ⟨1, by decide⟩ = ψ ⟨0, by decide⟩ := by
  unfold spinFlow
  change (∑ j : Fin 2, σ₁ ⟨1, by decide⟩ j * ψ j) = ψ ⟨0, by decide⟩
  simp [σ₁, Fin.sum_univ_two]

/-- ★ MC4'：锚定质量平方 = |ψ₁|² + |ψ₀|²（分量展开——
    σ₁ 只交换分量，不改变"量"；锚定 = 原旋量的量）。 -/
theorem anchorMassSq_component (ψ : Spinor) :
    anchorMassSq ψ = Complex.normSq (ψ ⟨1, by decide⟩) +
      Complex.normSq (ψ ⟨0, by decide⟩) := by
  unfold anchorMassSq
  rw [spinFlow_0, spinFlow_1]

/-- 非零旋量 ⟹ 至少一个分量非零（逐点 ≠ 0 的否命题）。 -/
theorem nonzero_spinor_has_component (ψ : Spinor) (h : ψ ≠ 0) :
    ψ ⟨0, by decide⟩ ≠ 0 ∨ ψ ⟨1, by decide⟩ ≠ 0 := by
  by_contra hcon
  apply h
  -- 两个分量都 = 0 ⟹ 旋量 = 0
  push_neg at hcon
  funext i
  fin_cases i
  · exact hcon.1
  · exact hcon.2

/-- ★ MC2'：非零旋量 ⟹ 锚定质量平方 > 0（★ 核心命题：
    自旋非零 ⟹ 质量非零——质量 = 内部运动状态对空间运动的锚定）。 -/
theorem anchorMassSq_pos_of_nonzero (ψ : Spinor) (h : ψ ≠ 0) :
    0 < anchorMassSq ψ := by
  rw [anchorMassSq_component]
  -- 加法交换：|ψ₁|² + |ψ₀|² = |ψ₀|² + |ψ₁|²（便于用分量假设）
  rw [add_comm]
  -- 至少一个分量非零 ⟹ 其 |·|² > 0 ⟹ 和 > 0
  rcases nonzero_spinor_has_component ψ h with h0 | h1
  · -- ψ₀ ≠ 0：|ψ₀|² > 0
    have hp : 0 < Complex.normSq (ψ ⟨0, by decide⟩) := by
      exact Complex.normSq_pos.mpr h0
    -- |ψ₁|² ≥ 0
    have hn1 : 0 ≤ Complex.normSq (ψ ⟨1, by decide⟩) := by
      exact Complex.normSq_nonneg _
    linarith
  · -- ψ₁ ≠ 0：|ψ₁|² > 0
    have hp : 0 < Complex.normSq (ψ ⟨1, by decide⟩) := by
      exact Complex.normSq_pos.mpr h1
    have hn0 : 0 ≤ Complex.normSq (ψ ⟨0, by decide⟩) := by
      exact Complex.normSq_nonneg _
    linarith

/-- ★ MC3'：零旋量 ⟹ 锚定质量平方 = 0（光子边界：
    零内部运动状态 ⟹ 零锚定 ⟹ 零质量）。 -/
theorem anchorMassSq_zero_of_zero (ψ : Spinor) (h : ψ = 0) :
    anchorMassSq ψ = 0 := by
  subst ψ
  simp [anchorMassSq, spinFlow, σ₁, Matrix.mulVec]

/-- ★ 汇总：核心命题的 mathlib 版（对应项目 MC1–MC2）。 -/
theorem core_proposition_mathlib :
    (∀ ψ : Spinor, ψ ≠ 0 → 0 < anchorMassSq ψ) ∧
    (anchorMassSq 0 = 0) := by
  constructor
  · intro ψ h
    exact anchorMassSq_pos_of_nonzero ψ h
  · exact anchorMassSq_zero_of_zero 0 rfl

end MinimalCoreMathlib

end
