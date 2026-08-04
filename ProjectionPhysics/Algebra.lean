-- ProjectionPhysics — Matrix Algebra from the Axioms
--
-- Module 7: Algebra.lean
--
-- 推导链（对应 SPEC 草案 D5/D6 的代数地基）：
--
--   A2a (S 在 ⊕ 下封闭) ⟹ S 是加法群
--     ⟹ End(S)（保加法映射）构成环，复合为乘法
--     ⟹ 选定基后，每个态射对应一个矩阵，矩阵乘法 = 复合
--     ⟹ 矩阵算法（乘法结合律、分配律）是复合的必然结果，不是发明
--
-- 本模块在 core Lean 中证明：
--   (A1) End(S) 在复合下封闭（环的乘法封闭性）
--   (A2) 复合结合（End 是半群）—— 一切矩阵乘法结合律的来源
--   (A3) 2×2 复矩阵的乘法结合律（真实矩阵算法的验证）
--   (A4) 矩阵乘法分配律（复合对加法的分配）

import ProjectionPhysics.Definitions

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- 加法群 S（A2a 的抽象：S 在 ⊕ 下封闭）
-- ---------------------------------------------------------------------------

/-- 保加法的映射（加法群的自同态）：T(a + b) = T a + T b。 -/
def AdditiveMap {S V : Type} [Add S] [Add V] (T : S → V) : Prop :=
  ∀ a b : S, T (a + b) = T a + T b

-- ---------------------------------------------------------------------------
-- (A1) End(S) 在复合下封闭：保加法映射的复合仍保加法
-- ---------------------------------------------------------------------------

theorem comp_additive {S U V : Type} [Add S] [Add U] [Add V]
    (T : U → V) (S' : S → U)
    (hT : AdditiveMap T) (hS : AdditiveMap S') :
    AdditiveMap (fun x : S => T (S' x)) := by
  unfold AdditiveMap at hT hS ⊢
  intro a b
  simp [hS, hT]

-- ---------------------------------------------------------------------------
-- (A2) 复合结合：矩阵乘法的结合律之源
-- ---------------------------------------------------------------------------

theorem comp_assoc {S U V W : Type}
    (T : V → W) (S' : U → V) (R : S → U) :
    (fun x : S => T (S' (R x))) = fun x : S => (fun y : U => T (S' y)) (R x) := by
  rfl

-- ---------------------------------------------------------------------------
-- 2×2 复矩阵：矩阵算法的显式验证
-- ---------------------------------------------------------------------------

/-- 复数 ℂ := Int × Int（分量算术）。HIBS 的 ℂ 是投影切片；
    这里 ℂ 作为矩阵系数的承载者。 -/
structure ℂ where
  re : Int
  im : Int

instance : Add ℂ := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul ℂ := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg ℂ := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : OfNat ℂ 0 := ⟨⟨0, 0⟩⟩
instance : OfNat ℂ 1 := ⟨⟨1, 0⟩⟩

def cConj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩
def cI : ℂ := ⟨0, 1⟩

@[simp] theorem cI_re : cI.re = 0 := rfl
@[simp] theorem cI_im : cI.im = 1 := rfl

theorem ℂ.ext {z w : ℂ} (hr : z.re = w.re) (hi : z.im = w.im) : z = w := by
  rcases z with ⟨zr, zi⟩
  rcases w with ⟨wr, wi⟩
  cases hr
  cases hi
  rfl

/-- ℂ 分量展开（实例的匿名实现，rfl 级别）。 -/
@[simp] theorem ℂ.add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] theorem ℂ.add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl
@[simp] theorem ℂ.mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem ℂ.mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem ℂ.neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] theorem ℂ.neg_im (z : ℂ) : (-z).im = -z.im := rfl
@[simp] theorem ℂ.ofNat0_re : (0 : ℂ).re = 0 := rfl
@[simp] theorem ℂ.ofNat0_im : (0 : ℂ).im = 0 := rfl
@[simp] theorem ℂ.ofNat1_re : (1 : ℂ).re = 1 := rfl
@[simp] theorem ℂ.ofNat1_im : (1 : ℂ).im = 0 := rfl

/-- 2×2 复矩阵（四分量）。 -/
structure Mat2 where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ

instance : Add Mat2 := ⟨fun M N => ⟨M.a + N.a, M.b + N.b, M.c + N.c, M.d + N.d⟩⟩
instance : Neg Mat2 := ⟨fun M => ⟨-M.a, -M.b, -M.c, -M.d⟩⟩
instance : OfNat Mat2 0 := ⟨⟨0, 0, 0, 0⟩⟩
instance : OfNat Mat2 1 := ⟨⟨1, 0, 0, 1⟩⟩

theorem Mat2.ext {M N : Mat2}
    (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  rcases M with ⟨a, b, c, d⟩
  rcases N with ⟨a', b', c', d'⟩
  cases ha <;> cases hb <;> cases hc <;> cases hd <;> rfl

/-- Mat2 分量展开（rfl 级别）。 -/
@[simp] theorem Mat2.add_a (M N : Mat2) : (M + N).a = M.a + N.a := rfl
@[simp] theorem Mat2.add_b (M N : Mat2) : (M + N).b = M.b + N.b := rfl
@[simp] theorem Mat2.add_c (M N : Mat2) : (M + N).c = M.c + N.c := rfl
@[simp] theorem Mat2.add_d (M N : Mat2) : (M + N).d = M.d + N.d := rfl
@[simp] theorem Mat2.neg_a (M : Mat2) : (-M).a = -M.a := rfl
@[simp] theorem Mat2.neg_b (M : Mat2) : (-M).b = -M.b := rfl
@[simp] theorem Mat2.neg_c (M : Mat2) : (-M).c = -M.c := rfl
@[simp] theorem Mat2.neg_d (M : Mat2) : (-M).d = -M.d := rfl
@[simp] theorem Mat2.ofNat0_a : (0 : Mat2).a = 0 := rfl
@[simp] theorem Mat2.ofNat0_b : (0 : Mat2).b = 0 := rfl
@[simp] theorem Mat2.ofNat0_c : (0 : Mat2).c = 0 := rfl
@[simp] theorem Mat2.ofNat0_d : (0 : Mat2).d = 0 := rfl
@[simp] theorem Mat2.ofNat1_a : (1 : Mat2).a = 1 := rfl
@[simp] theorem Mat2.ofNat1_b : (1 : Mat2).b = 0 := rfl
@[simp] theorem Mat2.ofNat1_c : (1 : Mat2).c = 0 := rfl
@[simp] theorem Mat2.ofNat1_d : (1 : Mat2).d = 1 := rfl

/-- 矩阵乘法（= 线性映射复合的坐标表示，A2b 的 ⊗ 给出的矩阵算法）。 -/
def matMul (M N : Mat2) : Mat2 :=
  ⟨ M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d
  , M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d ⟩

-- ---------------------------------------------------------------------------
-- (A3) 矩阵乘法结合律：(MN)P = M(NP)
-- ---------------------------------------------------------------------------

/-- 矩阵乘法结合律的四个分量（展开 ℂ 运算到 Int 后由 omega 重排）。 -/
theorem matMul_assoc_a {M N P : Mat2} :
    (matMul (matMul M N) P).a = (matMul M (matMul N P)).a := by
  apply ℂ.ext
  · simp [matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
    omega
  · simp [matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
    omega

theorem matMul_assoc_b {M N P : Mat2} :
    (matMul (matMul M N) P).b = (matMul M (matMul N P)).b := by
  apply ℂ.ext
  · simp [matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
    omega
  · simp [matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
    omega

theorem matMul_assoc_c {M N P : Mat2} :
    (matMul (matMul M N) P).c = (matMul M (matMul N P)).c := by
  apply ℂ.ext
  · simp [matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
    omega
  · simp [matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
    omega

theorem matMul_assoc_d {M N P : Mat2} :
    (matMul (matMul M N) P).d = (matMul M (matMul N P)).d := by
  apply ℂ.ext
  · simp [matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
    omega
  · simp [matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
    omega

/-- ★ 矩阵乘法结合律：矩阵算法从复合涌现。 -/
theorem matMul_assoc (M N P : Mat2) :
    matMul (matMul M N) P = matMul M (matMul N P) := by
  apply Mat2.ext
  · exact matMul_assoc_a
  · exact matMul_assoc_b
  · exact matMul_assoc_c
  · exact matMul_assoc_d

-- ---------------------------------------------------------------------------
-- (A4) 矩阵乘法分配律：M(N + K) = MN + MK
-- ---------------------------------------------------------------------------

theorem matMul_add_right (M N K : Mat2) :
    matMul M (N + K) = matMul M N + matMul M K := by
  apply Mat2.ext
  · apply ℂ.ext
    · simp [matMul, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      omega
    · simp [matMul, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      omega
  · apply ℂ.ext
    · simp [matMul, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      omega
    · simp [matMul, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      omega
  · apply ℂ.ext
    · simp [matMul, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      omega
    · simp [matMul, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      omega
  · apply ℂ.ext
    · simp [matMul, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      omega
    · simp [matMul, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      omega

end ProjectionPhysics
