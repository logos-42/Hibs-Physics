-- ProjectionPhysics — CliffordSix：Cℓ(6) 的 8 维复表示（胶球构造学 Part B）
--
-- leo（2026-08-13）胶球构造学探索的 Lean 化第二部分：
--   ★ 代数观察：Cℓ(6) 的旋量空间 = 8 维复 = 胶子色八重态的维度
--   （dim Cℓ(2n) 的复旋量 = 2ⁿ；Cℓ(3)⊗Cℓ(3) ≅ Cℓ(6)；3⊗3 = 8⊕1）。
--
-- 本模块构造 6 个 8×8 复矩阵（Mat8），证明 Clifford 关系：
--   CS1  Hᵢ² = I₈（6 个生成元平方 = 单位）
--   CS2  HᵢHⱼ + HⱼHᵢ = 0（15 对反交换）
--   CS3  clifford6_has_eight_dimensional_representation —— ★ 存在性定理
--        6 个反交换矩阵 = Cℓ(6) 的 8 维表示 = 旋量空间 8 维 = 色八重态
--
-- 构造策略：递归提升（Cℓ(2k) → Cℓ(2k+2) 的块构造）
--   Cℓ(2) 基：σ₁, σ₂（2×2，Clifford.lean 已有反交换）
--   Cℓ(4) 基：G₁..G₄（4×4，Mat4 = 2×2 块，复用 DiracBridge.Mat4）
--   Cℓ(6) 基：H₁..H₆（8×8，Mat8 = 4×4 块）
-- 块归约引理（diag/cross 型）把反交换证明归约到低一层，
-- 避免 8×8 的 64 分量展开。

import ProjectionPhysics.DiracBridge

namespace ProjectionPhysics

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! ### CS0. Mat8 = 四个 Mat4 块 -/

structure Mat8 where
  a : Mat4
  b : Mat4
  c : Mat4
  d : Mat4

theorem Mat8.ext {M N : Mat8}
    (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  rcases M with ⟨a, b, c, d⟩
  rcases N with ⟨a', b', c', d'⟩
  cases ha <;> cases hb <;> cases hc <;> cases hd <;> rfl

/-- 8×8 块乘法（四块结构，同 Mat4）。 -/
def mat8Mul (M N : Mat8) : Mat8 :=
  ⟨ mat4Mul M.a N.a + mat4Mul M.b N.c, mat4Mul M.a N.b + mat4Mul M.b N.d
  , mat4Mul M.c N.a + mat4Mul M.d N.c, mat4Mul M.c N.b + mat4Mul M.d N.d ⟩

instance : OfNat Mat8 0 := ⟨⟨0, 0, 0, 0⟩⟩
instance : OfNat Mat8 1 := ⟨⟨1, 0, 0, 1⟩⟩
instance : Add Mat8 := ⟨fun M N => ⟨M.a + N.a, M.b + N.b, M.c + N.c, M.d + N.d⟩⟩
instance : Neg Mat8 := ⟨fun M => ⟨-M.a, -M.b, -M.c, -M.d⟩⟩

@[simp] theorem Mat8.add_a (M N : Mat8) : (M + N).a = M.a + N.a := rfl
@[simp] theorem Mat8.add_b (M N : Mat8) : (M + N).b = M.b + N.b := rfl
@[simp] theorem Mat8.add_c (M N : Mat8) : (M + N).c = M.c + N.c := rfl
@[simp] theorem Mat8.add_d (M N : Mat8) : (M + N).d = M.d + N.d := rfl
@[simp] theorem Mat8.neg_a (M : Mat8) : (-M).a = -M.a := rfl
@[simp] theorem Mat8.neg_b (M : Mat8) : (-M).b = -M.b := rfl
@[simp] theorem Mat8.neg_c (M : Mat8) : (-M).c = -M.c := rfl
@[simp] theorem Mat8.neg_d (M : Mat8) : (-M).d = -M.d := rfl
@[simp] theorem Mat8.ofNat0_a : (0 : Mat8).a = 0 := rfl
@[simp] theorem Mat8.ofNat0_b : (0 : Mat8).b = 0 := rfl
@[simp] theorem Mat8.ofNat0_c : (0 : Mat8).c = 0 := rfl
@[simp] theorem Mat8.ofNat0_d : (0 : Mat8).d = 0 := rfl
@[simp] theorem Mat8.ofNat1_a : (1 : Mat8).a = 1 := rfl
@[simp] theorem Mat8.ofNat1_b : (1 : Mat8).b = 0 := rfl
@[simp] theorem Mat8.ofNat1_c : (1 : Mat8).c = 0 := rfl
@[simp] theorem Mat8.ofNat1_d : (1 : Mat8).d = 1 := rfl

/-! ### CS0b. 生成元定义（提升构造：Cℓ(2)→Cℓ(4)→Cℓ(6)） -/

/-- G₁ = diag(σ₁, −σ₁)（从 Cℓ(2) 提升）。 -/
def G₁ : Mat4 := ⟨σ₁, 0, 0, -σ₁⟩
def G₂ : Mat4 := ⟨σ₂, 0, 0, -σ₂⟩
def G₃ : Mat4 := ⟨0, 1, 1, 0⟩
/-- G₄ = [[0, −i], [i, 0]]（i = cI 标量嵌入，交叉块）。 -/
def G₄ : Mat4 := ⟨0, -scalar2 cI, scalar2 cI, 0⟩

/-- 4×4 标量嵌入（复标量 z 的对角块）。 -/
def c6_scalar4 (z : ℂ) : Mat4 := ⟨scalar2 z, 0, 0, scalar2 z⟩

def H₁ : Mat8 := ⟨G₁, 0, 0, -G₁⟩
def H₂ : Mat8 := ⟨G₂, 0, 0, -G₂⟩
def H₃ : Mat8 := ⟨G₃, 0, 0, -G₃⟩
def H₄ : Mat8 := ⟨G₄, 0, 0, -G₄⟩
def H₅ : Mat8 := ⟨0, 1, 1, 0⟩
def H₆ : Mat8 := ⟨0, -c6_scalar4 cI, c6_scalar4 cI, 0⟩

/-! ### 分量展开宏（core 组件展开 + omega） -/

macro "c6_m2" : tactic =>
  `(tactic| apply Mat2.ext <;> apply ℂ.ext <;>
      simp [matMul, mat4Mul, mat8Mul, scalar2, c6_scalar4, σ₁, σ₂, cI,
        G₁, G₂, G₃, G₄, H₁, H₂, H₃, H₄, H₅, H₆,
        ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, ℂ.neg_re, ℂ.neg_im,
        Int.mul_comm, Int.mul_assoc, Int.mul_left_comm,
        Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul,
        Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub,
        Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg] <;> omega)

macro "c6_m4" : tactic =>
  `(tactic| apply Mat4.ext <;> c6_m2)

macro "c6_m8" : tactic =>
  `(tactic| apply Mat8.ext <;> c6_m4)

/-! ### CS1a. Mat2 层代数引理 -/

theorem c6_mat2_mul_zero (A : Mat2) : matMul A 0 = 0 := by c6_m2
theorem c6_mat2_zero_mul (A : Mat2) : matMul 0 A = 0 := by c6_m2
theorem c6_mat2_mul_one (A : Mat2) : matMul A 1 = A := by c6_m2
theorem c6_mat2_one_mul (A : Mat2) : matMul 1 A = A := by c6_m2
theorem c6_mat2_neg_mul_neg (A B : Mat2) : matMul (-A) (-B) = matMul A B := by c6_m2
theorem c6_mat2_mul_neg (A B : Mat2) : matMul A (-B) = -matMul A B := by c6_m2
theorem c6_mat2_neg_mul (A B : Mat2) : matMul (-A) B = -matMul A B := by c6_m2
theorem c6_mat2_add_zero (A : Mat2) : A + 0 = A := by c6_m2
theorem c6_mat2_zero_add (A : Mat2) : 0 + A = A := by c6_m2
theorem c6_mat2_add_neg_self (A : Mat2) : A + -A = 0 := by c6_m2
theorem c6_mat2_neg_add_self (A : Mat2) : -A + A = 0 := by c6_m2
/-- 标量矩阵与任何矩阵交换（复标量的中心性）。 -/
theorem c6_mat2_scalar_commute (A : Mat2) (z : ℂ) :
    matMul A (scalar2 z) = matMul (scalar2 z) A := by c6_m2

/-! ### CS1b. Mat4 层代数引理 -/

theorem c6_mat4_mul_zero (A : Mat4) : mat4Mul A 0 = 0 := by c6_m4
theorem c6_mat4_zero_mul (A : Mat4) : mat4Mul 0 A = 0 := by c6_m4
theorem c6_mat4_mul_one (A : Mat4) : mat4Mul A 1 = A := by c6_m4
theorem c6_mat4_one_mul (A : Mat4) : mat4Mul 1 A = A := by c6_m4
theorem c6_mat4_neg_mul_neg (A B : Mat4) : mat4Mul (-A) (-B) = mat4Mul A B := by c6_m4
theorem c6_mat4_mul_neg (A B : Mat4) : mat4Mul A (-B) = -mat4Mul A B := by c6_m4
theorem c6_mat4_neg_mul (A B : Mat4) : mat4Mul (-A) B = -mat4Mul A B := by c6_m4
theorem c6_mat4_add_zero (A : Mat4) : A + 0 = A := by c6_m4
theorem c6_mat4_zero_add (A : Mat4) : 0 + A = A := by c6_m4
theorem c6_mat4_add_neg_self (A : Mat4) : A + -A = 0 := by c6_m4
theorem c6_mat4_neg_add_self (A : Mat4) : -A + A = 0 := by c6_m4

/-! ### CS1c. Mat4 层块归约引理（Cℓ(2) → Cℓ(4)） -/

/-- 对角块平方：⟨A,0,0,−A⟩² = 1 ⟸ A² = 1。 -/
theorem c6_mat4_diag_sq (A : Mat2) (hA : matMul A A = 1) :
    mat4Mul ⟨A, 0, 0, -A⟩ ⟨A, 0, 0, -A⟩ = 1 := by
  apply Mat4.ext
  · simp [mat4Mul, hA, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, hA, c6_mat2_neg_mul_neg, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]

/-- 对角×对角反交换：⟨A,0,0,−A⟩ ↔ ⟨B,0,0,−B⟩ ⟸ A,B 反交换。 -/
theorem c6_mat4_diag_anticommute (A B : Mat2) (h : matMul A B + matMul B A = 0) :
    mat4Mul ⟨A, 0, 0, -A⟩ ⟨B, 0, 0, -B⟩ + mat4Mul ⟨B, 0, 0, -B⟩ ⟨A, 0, 0, -A⟩ = 0 := by
  apply Mat4.ext
  · simp [mat4Mul, h, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, h, c6_mat2_neg_mul_neg, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]

/-- 对角×交叉反交换：⟨A,0,0,−A⟩ ↔ ⟨0,B,B,0⟩ ⟸ A,B 交换（AB = BA）。 -/
theorem c6_mat4_diag_cross_anticommute (A B : Mat2) (h : matMul A B = matMul B A) :
    mat4Mul ⟨A, 0, 0, -A⟩ ⟨0, B, B, 0⟩ + mat4Mul ⟨0, B, B, 0⟩ ⟨A, 0, 0, -A⟩ = 0 := by
  apply Mat4.ext
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
    rw [h, c6_mat2_mul_neg, c6_mat2_add_neg_self]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
    rw [c6_mat2_neg_mul, h, c6_mat2_neg_add_self]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]

/-- 对角×交叉反交换（−B 版）：⟨A,0,0,−A⟩ ↔ ⟨0,−B,B,0⟩ ⟸ A,B 交换。 -/
theorem c6_mat4_diag_cross_anticommute' (A B : Mat2) (h : matMul A B = matMul B A) :
    mat4Mul ⟨A, 0, 0, -A⟩ ⟨0, -B, B, 0⟩ + mat4Mul ⟨0, -B, B, 0⟩ ⟨A, 0, 0, -A⟩ = 0 := by
  apply Mat4.ext
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
    rw [c6_mat2_mul_neg, c6_mat2_neg_mul_neg, h, c6_mat2_neg_add_self]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
    rw [c6_mat2_neg_mul, h, c6_mat2_neg_add_self]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]

/-- 交叉块平方：⟨0,B,B,0⟩² = 1 ⟸ B² = 1。 -/
theorem c6_mat4_cross_sq (B : Mat2) (hB : matMul B B = 1) :
    mat4Mul ⟨0, B, B, 0⟩ ⟨0, B, B, 0⟩ = 1 := by
  apply Mat4.ext
  · simp [mat4Mul, hB, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]
  · simp [mat4Mul, hB, c6_mat2_mul_zero, c6_mat2_zero_mul, c6_mat2_add_zero, c6_mat2_zero_add]

/-! ### CS2a. Cℓ(4) 生成元：平方与反交换 -/

theorem G1_sq : mat4Mul G₁ G₁ = 1 := c6_mat4_diag_sq σ₁ sigma1_sq
theorem G2_sq : mat4Mul G₂ G₂ = 1 := c6_mat4_diag_sq σ₂ sigma2_sq
theorem G3_sq : mat4Mul G₃ G₃ = 1 := c6_mat4_cross_sq 1 (c6_mat2_mul_one 1)
theorem G4_sq : mat4Mul G₄ G₄ = 1 := by
  apply Mat4.ext <;> c6_m2

theorem G1_G2_anticommute : mat4Mul G₁ G₂ + mat4Mul G₂ G₁ = 0 :=
  c6_mat4_diag_anticommute σ₁ σ₂ sigma1_sigma2_anticommute

theorem G1_G3_anticommute : mat4Mul G₁ G₃ + mat4Mul G₃ G₁ = 0 :=
  c6_mat4_diag_cross_anticommute σ₁ 1 (by rw [c6_mat2_mul_one, c6_mat2_one_mul])

theorem G1_G4_anticommute : mat4Mul G₁ G₄ + mat4Mul G₄ G₁ = 0 :=
  c6_mat4_diag_cross_anticommute' σ₁ (scalar2 cI) (c6_mat2_scalar_commute σ₁ cI)

theorem G2_G3_anticommute : mat4Mul G₂ G₃ + mat4Mul G₃ G₂ = 0 :=
  c6_mat4_diag_cross_anticommute σ₂ 1 (by rw [c6_mat2_mul_one, c6_mat2_one_mul])

theorem G2_G4_anticommute : mat4Mul G₂ G₄ + mat4Mul G₄ G₂ = 0 :=
  c6_mat4_diag_cross_anticommute' σ₂ (scalar2 cI) (c6_mat2_scalar_commute σ₂ cI)

theorem G3_G4_anticommute : mat4Mul G₃ G₄ + mat4Mul G₄ G₃ = 0 := by
  apply Mat4.ext <;> c6_m2

/-! ### CS1d. Mat8 层代数引理 -/

theorem c6_mat8_mul_zero (A : Mat8) : mat8Mul A 0 = 0 := by c6_m8
theorem c6_mat8_zero_mul (A : Mat8) : mat8Mul 0 A = 0 := by c6_m8
theorem c6_mat8_mul_one (A : Mat8) : mat8Mul A 1 = A := by c6_m8
theorem c6_mat8_one_mul (A : Mat8) : mat8Mul 1 A = A := by c6_m8
theorem c6_mat8_neg_mul_neg (A B : Mat8) : mat8Mul (-A) (-B) = mat8Mul A B := by c6_m8
theorem c6_mat8_mul_neg (A B : Mat8) : mat8Mul A (-B) = -mat8Mul A B := by c6_m8
theorem c6_mat8_neg_mul (A B : Mat8) : mat8Mul (-A) B = -mat8Mul A B := by c6_m8
theorem c6_mat8_add_zero (A : Mat8) : A + 0 = A := by c6_m8
theorem c6_mat8_zero_add (A : Mat8) : 0 + A = A := by c6_m8
theorem c6_mat8_add_neg_self (A : Mat8) : A + -A = 0 := by c6_m8
theorem c6_mat8_neg_add_self (A : Mat8) : -A + A = 0 := by c6_m8

/-! ### CS1e. Mat8 层块归约引理（Cℓ(4) → Cℓ(6)） -/

theorem c6_mat8_diag_sq (A : Mat4) (hA : mat4Mul A A = 1) :
    mat8Mul ⟨A, 0, 0, -A⟩ ⟨A, 0, 0, -A⟩ = 1 := by
  apply Mat8.ext
  · simp [mat8Mul, hA, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, hA, c6_mat4_neg_mul_neg, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]

theorem c6_mat8_diag_anticommute (A B : Mat4) (h : mat4Mul A B + mat4Mul B A = 0) :
    mat8Mul ⟨A, 0, 0, -A⟩ ⟨B, 0, 0, -B⟩ + mat8Mul ⟨B, 0, 0, -B⟩ ⟨A, 0, 0, -A⟩ = 0 := by
  apply Mat8.ext
  · simp [mat8Mul, h, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, h, c6_mat4_neg_mul_neg, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]

theorem c6_mat8_diag_cross_anticommute (A B : Mat4) (h : mat4Mul A B = mat4Mul B A) :
    mat8Mul ⟨A, 0, 0, -A⟩ ⟨0, B, B, 0⟩ + mat8Mul ⟨0, B, B, 0⟩ ⟨A, 0, 0, -A⟩ = 0 := by
  apply Mat8.ext
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
    rw [h, c6_mat4_mul_neg, c6_mat4_add_neg_self]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
    rw [c6_mat4_neg_mul, h, c6_mat4_neg_add_self]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]

theorem c6_mat8_diag_cross_anticommute' (A B : Mat4) (h : mat4Mul A B = mat4Mul B A) :
    mat8Mul ⟨A, 0, 0, -A⟩ ⟨0, -B, B, 0⟩ + mat8Mul ⟨0, -B, B, 0⟩ ⟨A, 0, 0, -A⟩ = 0 := by
  apply Mat8.ext
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
    rw [c6_mat4_mul_neg, c6_mat4_neg_mul_neg, h, c6_mat4_neg_add_self]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
    rw [c6_mat4_neg_mul, h, c6_mat4_neg_add_self]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]

theorem c6_mat8_cross_sq (B : Mat4) (hB : mat4Mul B B = 1) :
    mat8Mul ⟨0, B, B, 0⟩ ⟨0, B, B, 0⟩ = 1 := by
  apply Mat8.ext
  · simp [mat8Mul, hB, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]
  · simp [mat8Mul, hB, c6_mat4_mul_zero, c6_mat4_zero_mul, c6_mat4_add_zero, c6_mat4_zero_add]

/-! ### CS2b. Cℓ(6) 生成元：平方与反交换 -/

theorem H1_sq : mat8Mul H₁ H₁ = 1 := c6_mat8_diag_sq G₁ G1_sq
theorem H2_sq : mat8Mul H₂ H₂ = 1 := c6_mat8_diag_sq G₂ G2_sq
theorem H3_sq : mat8Mul H₃ H₃ = 1 := c6_mat8_diag_sq G₃ G3_sq
theorem H4_sq : mat8Mul H₄ H₄ = 1 := c6_mat8_diag_sq G₄ G4_sq
theorem H5_sq : mat8Mul H₅ H₅ = 1 := c6_mat8_cross_sq 1 (c6_mat4_mul_one 1)
theorem H6_sq : mat8Mul H₆ H₆ = 1 := by
  apply Mat8.ext <;> c6_m4

theorem H1_H2_anticommute : mat8Mul H₁ H₂ + mat8Mul H₂ H₁ = 0 :=
  c6_mat8_diag_anticommute G₁ G₂ G1_G2_anticommute

theorem H1_H3_anticommute : mat8Mul H₁ H₃ + mat8Mul H₃ H₁ = 0 :=
  c6_mat8_diag_anticommute G₁ G₃ G1_G3_anticommute

theorem H1_H4_anticommute : mat8Mul H₁ H₄ + mat8Mul H₄ H₁ = 0 :=
  c6_mat8_diag_anticommute G₁ G₄ G1_G4_anticommute

theorem H1_H5_anticommute : mat8Mul H₁ H₅ + mat8Mul H₅ H₁ = 0 :=
  c6_mat8_diag_cross_anticommute G₁ 1 (by rw [c6_mat4_mul_one, c6_mat4_one_mul])

theorem H1_H6_anticommute : mat8Mul H₁ H₆ + mat8Mul H₆ H₁ = 0 :=
  c6_mat8_diag_cross_anticommute' G₁ (c6_scalar4 cI) (by c6_m4)

theorem H2_H3_anticommute : mat8Mul H₂ H₃ + mat8Mul H₃ H₂ = 0 :=
  c6_mat8_diag_anticommute G₂ G₃ G2_G3_anticommute

theorem H2_H4_anticommute : mat8Mul H₂ H₄ + mat8Mul H₄ H₂ = 0 :=
  c6_mat8_diag_anticommute G₂ G₄ G2_G4_anticommute

theorem H2_H5_anticommute : mat8Mul H₂ H₅ + mat8Mul H₅ H₂ = 0 :=
  c6_mat8_diag_cross_anticommute G₂ 1 (by rw [c6_mat4_mul_one, c6_mat4_one_mul])

theorem H2_H6_anticommute : mat8Mul H₂ H₆ + mat8Mul H₆ H₂ = 0 :=
  c6_mat8_diag_cross_anticommute' G₂ (c6_scalar4 cI) (by c6_m4)

theorem H3_H4_anticommute : mat8Mul H₃ H₄ + mat8Mul H₄ H₃ = 0 :=
  c6_mat8_diag_anticommute G₃ G₄ G3_G4_anticommute

theorem H3_H5_anticommute : mat8Mul H₃ H₅ + mat8Mul H₅ H₃ = 0 :=
  c6_mat8_diag_cross_anticommute G₃ 1 (by rw [c6_mat4_mul_one, c6_mat4_one_mul])

theorem H3_H6_anticommute : mat8Mul H₃ H₆ + mat8Mul H₆ H₃ = 0 :=
  c6_mat8_diag_cross_anticommute' G₃ (c6_scalar4 cI) (by c6_m4)

theorem H4_H5_anticommute : mat8Mul H₄ H₅ + mat8Mul H₅ H₄ = 0 :=
  c6_mat8_diag_cross_anticommute G₄ 1 (by rw [c6_mat4_mul_one, c6_mat4_one_mul])

theorem H4_H6_anticommute : mat8Mul H₄ H₆ + mat8Mul H₆ H₄ = 0 :=
  c6_mat8_diag_cross_anticommute' G₄ (c6_scalar4 cI) (by c6_m4)

theorem H5_H6_anticommute : mat8Mul H₅ H₆ + mat8Mul H₆ H₅ = 0 := by
  apply Mat8.ext <;> c6_m4

/-! ### CS3. ★ 结论定理：Cℓ(6) 的 8 维复表示存在
    6 个 8×8 反交换矩阵 = 旋量空间 8 维 = 胶子色八重态维度。 -/

theorem clifford6_has_eight_dimensional_representation :
    ∃ H₁ H₂ H₃ H₄ H₅ H₆ : Mat8,
      (mat8Mul H₁ H₁ = 1 ∧ mat8Mul H₂ H₂ = 1 ∧ mat8Mul H₃ H₃ = 1 ∧
       mat8Mul H₄ H₄ = 1 ∧ mat8Mul H₅ H₅ = 1 ∧ mat8Mul H₆ H₆ = 1) ∧
      (mat8Mul H₁ H₂ + mat8Mul H₂ H₁ = 0 ∧ mat8Mul H₁ H₃ + mat8Mul H₃ H₁ = 0 ∧
       mat8Mul H₁ H₄ + mat8Mul H₄ H₁ = 0 ∧ mat8Mul H₁ H₅ + mat8Mul H₅ H₁ = 0 ∧
       mat8Mul H₁ H₆ + mat8Mul H₆ H₁ = 0 ∧
       mat8Mul H₂ H₃ + mat8Mul H₃ H₂ = 0 ∧ mat8Mul H₂ H₄ + mat8Mul H₄ H₂ = 0 ∧
       mat8Mul H₂ H₅ + mat8Mul H₅ H₂ = 0 ∧ mat8Mul H₂ H₆ + mat8Mul H₆ H₂ = 0 ∧
       mat8Mul H₃ H₄ + mat8Mul H₄ H₃ = 0 ∧ mat8Mul H₃ H₅ + mat8Mul H₅ H₃ = 0 ∧
       mat8Mul H₃ H₆ + mat8Mul H₆ H₃ = 0 ∧
       mat8Mul H₄ H₅ + mat8Mul H₅ H₄ = 0 ∧ mat8Mul H₄ H₆ + mat8Mul H₆ H₄ = 0 ∧
       mat8Mul H₅ H₆ + mat8Mul H₆ H₅ = 0) :=
  ⟨H₁, H₂, H₃, H₄, H₅, H₆, ⟨⟨H1_sq, H2_sq, H3_sq, H4_sq, H5_sq, H6_sq⟩,
    ⟨H1_H2_anticommute, H1_H3_anticommute, H1_H4_anticommute,
     H1_H5_anticommute, H1_H6_anticommute,
     H2_H3_anticommute, H2_H4_anticommute, H2_H5_anticommute, H2_H6_anticommute,
     H3_H4_anticommute, H3_H5_anticommute, H3_H6_anticommute,
     H4_H5_anticommute, H4_H6_anticommute, H5_H6_anticommute⟩⟩⟩

/-- 维度观察：旋量空间 2³ = 8 = 色八重态维度（8 个胶子）。 -/
theorem spinor_dimension_eq_octet : 2 ^ 3 = 8 := rfl

end ProjectionPhysics
