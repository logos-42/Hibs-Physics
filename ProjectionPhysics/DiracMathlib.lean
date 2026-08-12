-- ProjectionPhysics — DiracMathlib：狄拉克桥的 mathlib 重写版
--
-- 与 ProjectionPhysics/DiracBridge.lean（core Lean 2×2 分块手写）对照，
-- 本模块用 mathlib 的 4×4 复矩阵 + Fin 4 旋量证明同样的核心定理：
--   DB1' gamma0² = 1（时间方向特殊：度规 +1 签名）
--   DB2' gamma1² = gamma2² = gamma3² = -1（空间方向：度规 −1 签名）
--   DB3' gamma0γⁱ + γⁱgamma0 = 0（时间-空间反交换）
--   DB4' γⁱγʲ + γʲγⁱ = 0（空间-空间反交换，i≠j）
--   DB5' 质量方程：gamma0ψ = ψ ⟺ ψ_L = ψ_R（★ 质量 = 手征耦合）
--   DB6' 零质量极限：∃ψ 手征不对称（m=0 ⟹ Weyl 手征对称）
--
-- 收获：mathlib 的 ext + fin_cases + ring 一行处理 4×4 矩阵乘法，
-- 无需手写 2×2 分块乘法与逐分量展开。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

noncomputable section
open Matrix

namespace DiracMathlib

/-- 4×4 复矩阵（狄拉克代数）。 -/
abbrev Mat4C : Type := Matrix (Fin 4) (Fin 4) ℂ

/-- 狄拉克旋量（4 分量：上半=左手 Weyl，下半=右手 Weyl）。 -/
abbrev DiracSpinor : Type := Fin 4 → ℂ

/-- gamma0 = [[0, 1], [1, 0]]（2×2 分块，Weyl 表示）——交换左右手。 -/
def gamma0 : Mat4C := !![ 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0 ]

/-- gamma1 = [[0, σ₁], [−σ₁, 0]]。 -/
def gamma1 : Mat4C := !![ 0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0 ]

/-- gamma2 = [[0, σ₂], [−σ₂, 0]]。 -/
def gamma2 : Mat4C := !![ 0, 0, 0, -Complex.I; 0, 0, Complex.I, 0;
                    0, Complex.I, 0, 0; -Complex.I, 0, 0, 0 ]

/-- gamma3 = [[0, σ₃], [−σ₃, 0]]。 -/
def gamma3 : Mat4C := !![ 0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0 ]

/-- 左手投影：取旋量上半（分量 0, 1）。 -/
def ψL (ψ : DiracSpinor) : Fin 2 → ℂ := fun i => ψ ⟨i.val, by omega⟩

/-- 右手投影：取旋量下半（分量 2, 3）。 -/
def ψR (ψ : DiracSpinor) : Fin 2 → ℂ := fun i => ψ ⟨i.val + 2, by omega⟩

/-! ### DB1'–DB2'：γ 平方（度规签名） -/

/-- ★ DB1'：gamma0² = 1（时间方向平方 = +1——度规时间分量签名）。 -/
theorem gamma0_sq : gamma0 * gamma0 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma0, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- ★ DB2a'：gamma1² = −1（空间方向平方 = −1——度规空间分量签名）。
    这就是"时间特殊"的代数内容：时间方向 +1，空间方向 −1。 -/
theorem gamma1_sq : gamma1 * gamma1 = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma1, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gamma2_sq : gamma2 * gamma2 = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma2, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gamma3_sq : gamma3 * gamma3 = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma3, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-! ### DB3'–DB4'：反交换 -/

/-- ★ DB3'：gamma0gamma1 + gamma1gamma0 = 0（时间与空间方向反交换）。 -/
theorem gamma0_gamma1_anticommute :
    gamma0 * gamma1 + gamma1 * gamma0 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma1, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gamma0_gamma2_anticommute :
    gamma0 * gamma2 + gamma2 * gamma0 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma2, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gamma0_gamma3_anticommute :
    gamma0 * gamma3 + gamma3 * gamma0 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma3, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gamma1_gamma2_anticommute :
    gamma1 * gamma2 + gamma2 * gamma1 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma1, gamma2, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gamma1_gamma3_anticommute :
    gamma1 * gamma3 + gamma3 * gamma1 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma1, gamma3, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gamma2_gamma3_anticommute :
    gamma2 * gamma3 + gamma3 * gamma2 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-! ### DB5'：质量方程 = 手征耦合 -/

/-- γ⁰ 作用于旋量 = 交换左右手（分量展开）。 -/
theorem gamma0_act_0 (ψ : DiracSpinor) :
    (gamma0.mulVec ψ) ⟨0, by decide⟩ = ψ ⟨2, by decide⟩ := by
  change (∑ j : Fin 4, gamma0 ⟨0, by decide⟩ j * ψ j) = ψ ⟨2, by decide⟩
  simp [gamma0, Fin.sum_univ_four]

theorem gamma0_act_1 (ψ : DiracSpinor) :
    (gamma0.mulVec ψ) ⟨1, by decide⟩ = ψ ⟨3, by decide⟩ := by
  change (∑ j : Fin 4, gamma0 ⟨1, by decide⟩ j * ψ j) = ψ ⟨3, by decide⟩
  simp [gamma0, Fin.sum_univ_four]

theorem gamma0_act_2 (ψ : DiracSpinor) :
    (gamma0.mulVec ψ) ⟨2, by decide⟩ = ψ ⟨0, by decide⟩ := by
  change (∑ j : Fin 4, gamma0 ⟨2, by decide⟩ j * ψ j) = ψ ⟨0, by decide⟩
  simp [gamma0, Fin.sum_univ_four]

theorem gamma0_act_3 (ψ : DiracSpinor) :
    (gamma0.mulVec ψ) ⟨3, by decide⟩ = ψ ⟨1, by decide⟩ := by
  change (∑ j : Fin 4, gamma0 ⟨3, by decide⟩ j * ψ j) = ψ ⟨1, by decide⟩
  simp [gamma0, Fin.sum_univ_four]

/-- ★ DB5'：静止质量方程 (gamma0 − 1)ψ = 0 ⟺ ψ_L = ψ_R。
    质量解要求左手 = 右手——★ 质量 = 手征耦合的精确代数内容。 -/
theorem mass_equation_couples_chiralities (ψ : DiracSpinor) :
    gamma0.mulVec ψ = ψ ↔ ψL ψ = ψR ψ := by
  constructor
  · intro h
    -- 投影到左右手：从 γ⁰ψ = ψ 推出左 = 右
    funext i
    fin_cases i
    · -- i = 0：ψL ψ 0 = ψR ψ 0 ⟺ ψ 0 = ψ 2
      have h0 := congrArg (fun s : DiracSpinor => s ⟨0, by decide⟩) h
      change (gamma0.mulVec ψ) ⟨0, by decide⟩ = ψ ⟨0, by decide⟩ at h0
      rw [gamma0_act_0] at h0
      exact h0.symm
    · -- i = 1：ψL ψ 1 = ψR ψ 1 ⟺ ψ 1 = ψ 3
      have h1 := congrArg (fun s : DiracSpinor => s ⟨1, by decide⟩) h
      change (gamma0.mulVec ψ) ⟨1, by decide⟩ = ψ ⟨1, by decide⟩ at h1
      rw [gamma0_act_1] at h1
      exact h1.symm
  · intro hLR
    -- 从左 = 右推出 γ⁰ψ = ψ（逐分量）
    ext i
    fin_cases i
    · -- i = 0：(γ⁰ψ) 0 = ψ 2 = ψ 0（hLR 在 0）
      have h0 := congrArg (fun s : Fin 2 → ℂ => s ⟨0, by decide⟩) hLR
      -- h0 : ψL ψ 0 = ψR ψ 0，展开 = ψ 0 = ψ 2
      simp [ψL, ψR] at h0
      rw [gamma0_act_0]
      exact h0.symm
    · -- i = 1：(γ⁰ψ) 1 = ψ 3 = ψ 1（hLR 在 1）
      have h1 := congrArg (fun s : Fin 2 → ℂ => s ⟨1, by decide⟩) hLR
      simp [ψL, ψR] at h1
      rw [gamma0_act_1]
      exact h1.symm
    · -- i = 2：(γ⁰ψ) 2 = ψ 0 = ψ 2（hLR 在 0）
      have h0 := congrArg (fun s : Fin 2 → ℂ => s ⟨0, by decide⟩) hLR
      simp [ψL, ψR] at h0
      rw [gamma0_act_2]
      exact h0
    · -- i = 3：(γ⁰ψ) 3 = ψ 1 = ψ 3（hLR 在 1）
      have h1 := congrArg (fun s : Fin 2 → ℂ => s ⟨1, by decide⟩) hLR
      simp [ψL, ψR] at h1
      rw [gamma0_act_3]
      exact h1

/-! ### DB6'：零质量极限（Weyl） -/

/-- ★ DB6'：零质量极限存在手征不对称解——m = 0 时左右手无约束
    （手征对称性不破缺 = 光子边界）。 -/
theorem zero_mass_has_chiral_asymmetry :
    ∃ ψ : DiracSpinor, gamma0.mulVec ψ ≠ ψ := by
  -- 取 ψ = (1, 0, 0, 0)：γ⁰ψ = (0, 0, 1, 0) ≠ ψ
  refine ⟨![1, 0, 0, 0], ?_⟩
  intro h
  have h0 := congrArg (fun s : DiracSpinor => s ⟨0, by decide⟩) h
  -- (γ⁰ψ) 0 = ψ 0 ⟹ 0 = 1 矛盾
  change (gamma0.mulVec ![1, 0, 0, 0]) ⟨0, by decide⟩ =
    (![1, 0, 0, 0]) ⟨0, by decide⟩ at h0
  rw [gamma0_act_0] at h0
  norm_num at h0

end DiracMathlib

end
