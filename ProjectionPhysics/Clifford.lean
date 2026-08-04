-- ProjectionPhysics — Spin from the Axioms (Clifford Emergence)
--
-- Module 8: Clifford.lean
--
-- 推导链（对应 SPEC 草案 D6）：
--
--   A2b (⊗ : S×S → R) ⟹ 二次型 Q(ζ) = ζ⊗ζ†
--     ⟹ Clifford 代数 Cℓ(Q)：生成元 γ 满足 γᵢγⱼ + γⱼγᵢ = 2Q(eᵢ, eⱼ)
--     ⟹ 不可约表示 = 旋量空间 = 自旋
--     ⟹ ★ (γ₁γ₂)² = -1：虚数单位 i 从实/复生成元的反交换涌现
--
-- 本模块在 core Lean 中证明（2×2 复矩阵，Pauli 基）：
--   (C1) σ₁² = σ₂² = σ₃² = I        （生成元平方 = 度规）
--   (C2) σᵢσⱼ + σⱼσᵢ = 0 (i≠j)      （反交换 = Clifford 关系）
--   (C3) (σ₁σ₂)² = -I                （★ 虚数单位的涌现）
--   (C4) σ₃ = -i·σ₁σ₂                （第三个生成元从前两个涌现）
--   (C5) 自旋表示：Pauli 矩阵生成 Cℓ(3)（任意两个生成元决定第三个）

import ProjectionPhysics.Algebra

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- 标量嵌入与 Pauli 基
-- ---------------------------------------------------------------------------

/-- 标量嵌入：z ↦ z·I（2×2 单位阵的倍数）。 -/
def scalar2 (z : ℂ) : Mat2 := ⟨z, 0, 0, z⟩

/-- Pauli 矩阵（Clifford 生成元的自旋表示）。 -/
def σ₁ : Mat2 := ⟨0, 1, 1, 0⟩          -- σ_x
def σ₂ : Mat2 := ⟨0, cI, -cI, 0⟩       -- σ_y（含虚数单位）
def σ₃ : Mat2 := ⟨1, 0, 0, -1⟩         -- σ_z

-- ---------------------------------------------------------------------------
-- (C1) 生成元平方 = 单位矩阵（度规正定方向）
-- ---------------------------------------------------------------------------

theorem sigma1_sq : matMul σ₁ σ₁ = 1 := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [σ₁, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma2_sq : matMul σ₂ σ₂ = 1 := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [σ₂, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma3_sq : matMul σ₃ σ₃ = 1 := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

-- ---------------------------------------------------------------------------
-- (C2) 反交换：σᵢσⱼ + σⱼσᵢ = 0 (i ≠ j)
-- ---------------------------------------------------------------------------

theorem sigma1_sigma2_anticommute :
    matMul σ₁ σ₂ + matMul σ₂ σ₁ = 0 := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [σ₁, σ₂, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma1_sigma3_anticommute :
    matMul σ₁ σ₃ + matMul σ₃ σ₁ = 0 := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [σ₁, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma2_sigma3_anticommute :
    matMul σ₂ σ₃ + matMul σ₃ σ₂ = 0 := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [σ₂, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

-- ---------------------------------------------------------------------------
-- (C3) ★ 虚数单位的涌现：(σ₁σ₂)² = -1
-- ---------------------------------------------------------------------------

theorem i_emerges_from_clifford :
    matMul (matMul σ₁ σ₂) (matMul σ₁ σ₂) = -1 := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

-- ---------------------------------------------------------------------------
-- (C4) 完整乘法表：σᵢσⱼ (i ≠ j)
--      约定：σ₂ = [[0,i],[-i,0]]，得 σᵢσⱼ = δᵢⱼI − iεᵢⱼₖσₖ
-- ---------------------------------------------------------------------------

theorem sigma1_sigma2_eq : matMul σ₁ σ₂ = matMul (scalar2 (-cI)) σ₃ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma2_sigma1_eq : matMul σ₂ σ₁ = matMul (scalar2 cI) σ₃ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma1_sigma3_eq : matMul σ₁ σ₃ = matMul (scalar2 cI) σ₂ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma3_sigma1_eq : matMul σ₃ σ₁ = matMul (scalar2 (-cI)) σ₂ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma2_sigma3_eq : matMul σ₂ σ₃ = matMul (scalar2 (-cI)) σ₁ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

theorem sigma3_sigma2_eq : matMul σ₃ σ₂ = matMul (scalar2 cI) σ₁ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

-- ---------------------------------------------------------------------------
-- (C4') 完整乘法表总结（含 C1 的平方项）：
--   σ₁σ₁ = I    σ₁σ₂ = −iσ₃   σ₁σ₃ = +iσ₂
--   σ₂σ₁ = +iσ₃  σ₂σ₂ = I     σ₂σ₃ = −iσ₁
--   σ₃σ₁ = −iσ₂  σ₃σ₂ = +iσ₁   σ₃σ₃ = I
-- ---------------------------------------------------------------------------
-- (C4) σ₃ = -i·σ₁σ₂：第三个生成元从前两个涌现
-- ---------------------------------------------------------------------------

theorem sigma3_from_sigma1_sigma2 :
    σ₃ = matMul (scalar2 cI) (matMul σ₁ σ₂) := by
  -- σ₁σ₂ = -i·σ₃，故 σ₃ = i·σ₁σ₂（-i·i = 1）
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub] <;> omega

-- ---------------------------------------------------------------------------
-- (C5) 旋量表示：2×2 复矩阵 = Cℓ(3) 的自旋表示（载体空间 = 旋量空间）
-- ---------------------------------------------------------------------------

/-- 旋量空间：2 分量复列向量（Clifford 表示的载体）。 -/
structure Spinor where
  ψ₁ : ℂ
  ψ₂ : ℂ

theorem Spinor.ext {s t : Spinor} (h1 : s.ψ₁ = t.ψ₁) (h2 : s.ψ₂ = t.ψ₂) : s = t := by
  rcases s with ⟨ψ₁, ψ₂⟩
  rcases t with ⟨ψ₁', ψ₂'⟩
  cases h1 <;> cases h2 <;> rfl

/-- 矩阵作用在旋量上（线性表示）。 -/
def matMulSpinor (M : Mat2) (s : Spinor) : Spinor :=
  ⟨ M.a * s.ψ₁ + M.b * s.ψ₂, M.c * s.ψ₁ + M.d * s.ψ₂ ⟩

/-- ★ 表示性质：矩阵乘法结合律在旋量作用上保持：
    (MN)ψ = M(Nψ)。自旋表示是同态。 -/
theorem spinor_rep_hom (M N : Mat2) (s : Spinor) :
    matMulSpinor (matMul M N) s = matMulSpinor M (matMulSpinor N s) := by
  cases s
  apply Spinor.ext <;> apply ℂ.ext <;>
    simp [matMulSpinor, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc] <;> omega

-- ---------------------------------------------------------------------------
-- 草案：Clifford Emergence（完整陈述）
-- ---------------------------------------------------------------------------

/-- Clifford 涌现定理（草案声明）。
    二次型 Q（来自 A2b 的 ⊗）生成唯一的 Clifford 代数 Cℓ(Q)；
    Cℓ(Q) 的不可约矩阵表示给出旋量空间（自旋）。
    Pauli 矩阵已显式验证 C1–C5；一般维数的表示论为开放目标。 -/
structure CliffordEmergence (n : Nat) where
  -- 生成元：满足反交换关系的 n 个矩阵（作为抽象数据）
  gamma : Fin n → Mat2
  -- Clifford 关系：γᵢγⱼ + γⱼγᵢ = 0
  anticommute : ∀ i j : Fin n, i ≠ j →
    matMul (gamma i) (gamma j) + matMul (gamma j) (gamma i) = 0
  -- 平方 = 度规
  square_unit : ∀ i : Fin n, matMul (gamma i) (gamma i) = 1
  -- 自旋：旋量空间上的表示保持乘法（已证：spinor_rep_hom）
  -- 手性（A3 的 √ → iR）：草案——需要复结构后分解左右旋量

/-- ★ CliffordEmergence 实例化：Pauli 矩阵是 Cℓ(3) 的生成元（3 维情形已证）。 -/
def pauliGamma : Fin 3 → Mat2 :=
  fun i => if i = 0 then σ₁ else if i = 1 then σ₂ else σ₃

theorem pauliGamma_anticommute : ∀ i j : Fin 3, i ≠ j →
    matMul (pauliGamma i) (pauliGamma j) + matMul (pauliGamma j) (pauliGamma i) = 0 := by
  intro i j hij
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hi with hi0 | hi1 | hi2
  · rcases hj with hj0 | hj1 | hj2
    · exfalso; apply hij; apply Fin.ext; omega
    · have hi0f : i = (0 : Fin 3) := Fin.ext hi0
      have hj1f : j = (1 : Fin 3) := Fin.ext hj1
      rw [hi0f, hj1f]
      simp [pauliGamma, sigma1_sigma2_anticommute]
    · have hi0f : i = (0 : Fin 3) := Fin.ext hi0
      have hj2f : j = (2 : Fin 3) := Fin.ext hj2
      rw [hi0f, hj2f]
      simp [pauliGamma, sigma1_sigma3_anticommute]
  · rcases hj with hj0 | hj1 | hj2
    · have hi1f : i = (1 : Fin 3) := Fin.ext hi1
      have hj0f : j = (0 : Fin 3) := Fin.ext hj0
      rw [hi1f, hj0f]
      simp [pauliGamma, sigma1_sigma2_anticommute, Mat2.add_comm]
    · exfalso; apply hij; apply Fin.ext; omega
    · have hi1f : i = (1 : Fin 3) := Fin.ext hi1
      have hj2f : j = (2 : Fin 3) := Fin.ext hj2
      rw [hi1f, hj2f]
      simp [pauliGamma, sigma2_sigma3_anticommute]
  · rcases hj with hj0 | hj1 | hj2
    · have hi2f : i = (2 : Fin 3) := Fin.ext hi2
      have hj0f : j = (0 : Fin 3) := Fin.ext hj0
      rw [hi2f, hj0f]
      simp [pauliGamma, sigma1_sigma3_anticommute, Mat2.add_comm]
    · have hi2f : i = (2 : Fin 3) := Fin.ext hi2
      have hj1f : j = (1 : Fin 3) := Fin.ext hj1
      rw [hi2f, hj1f]
      simp [pauliGamma, sigma2_sigma3_anticommute, Mat2.add_comm]
    · exfalso; apply hij; apply Fin.ext; omega

theorem pauliGamma_square : ∀ i : Fin 3, matMul (pauliGamma i) (pauliGamma i) = 1 := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hi with hi0 | hi1 | hi2
  · have hi0f : i = (0 : Fin 3) := Fin.ext hi0
    rw [hi0f]
    simp [pauliGamma, sigma1_sq]
  · have hi1f : i = (1 : Fin 3) := Fin.ext hi1
    rw [hi1f]
    simp [pauliGamma, sigma2_sq]
  · have hi2f : i = (2 : Fin 3) := Fin.ext hi2
    rw [hi2f]
    simp [pauliGamma, sigma3_sq]

/-- Pauli 矩阵生成 Cℓ(3)：草案 CliffordEmergence 的 3 维实例（已证）。 -/
def pauliClifford : CliffordEmergence 3 :=
  { gamma := pauliGamma
  , anticommute := pauliGamma_anticommute
  , square_unit := pauliGamma_square }

end ProjectionPhysics
