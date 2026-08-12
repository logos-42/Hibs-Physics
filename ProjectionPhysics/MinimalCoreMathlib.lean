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
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open Matrix

namespace MinimalCoreMathlib

/-- 2×2 复矩阵。 -/
abbrev Mat2C : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- 旋量（2 分量，Clifford 旋量）。 -/
abbrev Spinor : Type := Fin 2 → ℂ

/-- σ₁ = [[0, 1], [1, 0]]（x 方向自旋生成元，同项目 Clifford）。 -/
def σ₁ : Mat2C := !![ 0, 1; 1, 0 ]

/-- σ₂ = [[0, -i], [i, 0]]（y 方向——"另一个方向"，含虚数单位）。 -/
def σ₂ : Mat2C := !![ 0, -Complex.I; Complex.I, 0 ]

/-- σ₃ = [[1, 0], [0, -1]]（z 方向——★ 法向量方向，平面外）。 -/
def σ₃ : Mat2C := !![ 1, 0; 0, -1 ]

/-- ★ 法向量从平面内运动涌现：σ₃ = −i·σ₁σ₂（对应 SpaceLightSpeed 的
    normal_direction_emerges_from_plane，mathlib 版）。
    平面内两个方向的运动（σ₁σ₂）产生平面外的法向量（σ₃）——
    "第三个方向不是独立的，是从平面涌现的"。 -/
theorem normal_direction_emerges :
    σ₃ = (-Complex.I : ℂ) • (σ₁ * σ₂) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, σ₃, Matrix.mul_apply] <;> ring

/-- ★ 自旋的法向量运动：自旋非零 ⟹ 法向量方向的旋量流非零（σ₃ψ ≠ 0）。
    "自旋应该有一个法向量方向的运动轨迹导致质量产生"（leo）——
    这正是它的代数形式：自旋在平面外（法向量）方向产生运动，
    使粒子偏离空间平面内流动 ⟹ 锚定 ⟹ 质量。 -/
theorem spin_normal_flow_nonzero (ψ : Spinor) (h : ψ ≠ 0) :
    σ₃.mulVec ψ ≠ 0 := by
  -- σ₃² = 1（Clifford），σ₃ 可逆 ⟹ 非零旋量映射到非零旋量
  have hsq : σ₃ * σ₃ = 1 := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [σ₃, Matrix.mul_apply] <;> ring
  intro hz
  apply h
  -- ψ = σ₃(σ₃ψ) = σ₃ 0 = 0
  calc
    ψ = σ₃.mulVec (σ₃.mulVec ψ) := by
      have : σ₃.mulVec (σ₃.mulVec ψ) = (σ₃ * σ₃).mulVec ψ := by
        simp [Matrix.mulVec_mulVec]
      rw [this, hsq]
      simp [Matrix.mulVec]
    _ = σ₃.mulVec 0 := by rw [hz]
    _ = 0 := by simp [Matrix.mulVec]

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

/-! ### 三胶子：三方向运动的纠缠（MC6'） -/

/-- 三胶子质量平方 = 三个方向旋量流锚定的叠加：
    m_G² = m₁² + m₂² + m₃²（对应项目 MC2 的 |a|²+|b|²+|c|²）。 -/
def glueballMassSq3 (ψ₁ ψ₂ ψ₃ : Spinor) : ℝ :=
  anchorMassSq ψ₁ + anchorMassSq ψ₂ + anchorMassSq ψ₃

/-- ★ MC6'：三个方向都运动（纠缠）⟹ 胶球质量 > 0。
    三个胶子的运动机制 = 电子机制 × 3（每个方向独立锚定），
    叠加后质量平方 = 三方向之和——"三个胶子在运行"的代数形式。 -/
theorem glueballMassSq3_pos (ψ₁ ψ₂ ψ₃ : Spinor)
    (h1 : ψ₁ ≠ 0) (h2 : ψ₂ ≠ 0) (h3 : ψ₃ ≠ 0) :
    0 < glueballMassSq3 ψ₁ ψ₂ ψ₃ := by
  unfold glueballMassSq3
  have p1 : 0 < anchorMassSq ψ₁ := anchorMassSq_pos_of_nonzero ψ₁ h1
  have p2 : 0 < anchorMassSq ψ₂ := anchorMassSq_pos_of_nonzero ψ₂ h2
  have p3 : 0 < anchorMassSq ψ₃ := anchorMassSq_pos_of_nonzero ψ₃ h3
  linarith

/-- ★ MC6'：三方向完全纠缠（σ₁+σ₂+σ₃ 联合旋量流）——
    三个胶子不是独立运动，而是共享一个纠缠态 ψ 的三个方向分量。
    定理：纠缠态非零 ⟹ 联合旋量流非零（三方向一起锚定）。 -/
theorem entangled_triplet_flow_nonzero (ψ : Spinor) (h : ψ ≠ 0) :
    (σ₁ + σ₂ + σ₃).mulVec ψ ≠ 0 := by
  -- M = σ₁+σ₂+σ₃ = [[1, 1−i], [1+i, −1]]，det = −3 ≠ 0 ⟹ M 可逆
  -- 若 Mψ = 0，则 ψ = M⁻¹·(Mψ) = M⁻¹·0 = 0 矛盾
  have hdet : Matrix.det (σ₁ + σ₂ + σ₃) ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [σ₁, σ₂, σ₃]
    -- det = 1·(−1) − (1−i)(1+i) = −1 − 2 = −3 ≠ 0
    have h2 : (1 + -Complex.I) * (1 + Complex.I) = 2 := by
      apply Complex.ext <;> simp [Complex.I_re, Complex.I_im] <;> ring
    rw [h2]
    norm_num
  -- 矩阵可逆（det = −3 可逆 ⟹ Invertible）
  letI : Invertible (Matrix.det (σ₁ + σ₂ + σ₃)) := invertibleOfNonzero hdet
  letI : Invertible (σ₁ + σ₂ + σ₃) :=
    Matrix.invertibleOfDetInvertible (σ₁ + σ₂ + σ₃)
  intro hz
  apply h
  -- ψ = M⁻¹·(M·ψ)（M⁻¹·M = I）
  calc
    ψ = (σ₁ + σ₂ + σ₃)⁻¹.mulVec ((σ₁ + σ₂ + σ₃).mulVec ψ) := by
      have : (σ₁ + σ₂ + σ₃)⁻¹.mulVec ((σ₁ + σ₂ + σ₃).mulVec ψ) =
          ((σ₁ + σ₂ + σ₃)⁻¹ * (σ₁ + σ₂ + σ₃)).mulVec ψ := by
        simp [Matrix.mulVec_mulVec]
      rw [this]
      simp
    _ = (σ₁ + σ₂ + σ₃)⁻¹.mulVec 0 := by rw [hz]
    _ = 0 := by simp [Matrix.mulVec]

end MinimalCoreMathlib

end
