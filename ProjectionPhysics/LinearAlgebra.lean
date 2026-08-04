-- ProjectionPhysics — Linear Algebra: vectors, tensors, kernel
--
-- Module 9: LinearAlgebra.lean
--
-- 按顺序补齐隐数空间的矢量/张量/kernel 理论：
--
--   (L1) 向量空间公理（加法 + Int 标量乘）—— S 的代数结构
--   (L2) ℂ 与 Int 的向量空间实例（ℂ = 2 维实向量空间）
--   (L3) 线性映射；Re 投影是线性的
--   (L4) kernel 子空间：数乘封闭（补 K1 的缺）
--   (L5) 基（张成 + 线性无关）+ 维度
--   (L6) ★ rank-nullity 具体验证：dim ℂ = dim ker(Re) + dim im(Re) = 1 + 1
--        （i ∈ ker(Re)：虚轴是实部投影的核——HIBS A3 的 iR 就是它）
--   (L7) 双线性形式（张量原语）+ 极化恒等式（Metric Representation 的前置）

import ProjectionPhysics.Algebra
import ProjectionPhysics.Completeness

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- (L1) 向量空间结构
-- ---------------------------------------------------------------------------

/-- 向量空间公理（Int 标量乘，core Lean 手写版）。 -/
structure VecSpace (V : Type) [Add V] [Zero V] where
  smul : Int → V → V
  smul_zero : ∀ a : Int, smul a 0 = 0
  smul_add : ∀ (a : Int) (x y : V), smul a (x + y) = smul a x + smul a y
  add_smul : ∀ (a b : Int) (x : V), smul (a + b) x = smul a x + smul b x
  smul_smul : ∀ (a b : Int) (x : V), smul a (smul b x) = smul (a * b) x
  smul_one : ∀ x : V, smul 1 x = x
  zero_add : ∀ x : V, 0 + x = x
  add_assoc : ∀ x y z : V, (x + y) + z = x + (y + z)
  add_comm : ∀ x y : V, x + y = y + x

-- ---------------------------------------------------------------------------
-- (L2) ℂ 与 Int 的向量空间实例
-- ---------------------------------------------------------------------------

/-- ℂ 上的 Int 标量乘：a·(x + iy) = ax + iay。 -/
def cSmul (a : Int) (z : ℂ) : ℂ := ⟨a * z.re, a * z.im⟩

instance : Zero ℂ where zero := ⟨0, 0⟩

/-- ℂ 是 2 维实向量空间。 -/
def cVecSpace : VecSpace ℂ :=
  { smul := cSmul
  , smul_zero := by intro a; apply ℂ.ext <;> simp [cSmul]
  , smul_add := by intro a x y; apply ℂ.ext <;> simp [cSmul, Int.mul_add] <;> omega
  , add_smul := by intro a b x; apply ℂ.ext <;> simp [cSmul, Int.add_mul] <;> omega
  , smul_smul := by intro a b x; apply ℂ.ext <;> simp [cSmul, Int.mul_assoc] <;> omega
  , smul_one := by intro x; apply ℂ.ext <;> simp [cSmul]
  , zero_add := by intro x; apply ℂ.ext <;> simp
  , add_assoc := by intro x y z; apply ℂ.ext <;> simp <;> omega
  , add_comm := by intro x y; apply ℂ.ext <;> simp <;> omega }

/-- Int 是 1 维实向量空间。 -/
def intVecSpace : VecSpace Int :=
  { smul := fun a x => a * x
  , smul_zero := by intro a; simp
  , smul_add := by intro a x y; simp [Int.mul_add]
  , add_smul := by intro a b x; simp [Int.add_mul]
  , smul_smul := by intro a b x; simp [Int.mul_assoc]
  , smul_one := by intro x; simp
  , zero_add := by intro x; omega
  , add_assoc := by intro x y z; omega
  , add_comm := by intro x y; omega }

-- ---------------------------------------------------------------------------
-- (L3) 线性映射；Re 投影是线性的
-- ---------------------------------------------------------------------------

/-- 线性映射：保加法 + 保数乘。 -/
def LinearMap {V W : Type} [Add V] [Add W] [Zero V] [Zero W]
    (VS : VecSpace V) (WS : VecSpace W) (T : V → W) : Prop :=
  (∀ x y : V, T (x + y) = T x + T y) ∧
  (∀ (a : Int) (x : V), T (VS.smul a x) = WS.smul a (T x))

/-- 实部投影 Re : ℂ → Int（HIBS 的 f : S → R）。 -/
def reProj (z : ℂ) : Int := z.re

theorem reProj_add : ∀ x y : ℂ, reProj (x + y) = reProj x + reProj y := by
  intro x y
  rfl

theorem reProj_smul : ∀ (a : Int) (x : ℂ), reProj (cSmul a x) = a * reProj x := by
  intro a x
  rfl

theorem reProj_linear : LinearMap cVecSpace intVecSpace reProj := by
  constructor
  · exact reProj_add
  · intro a x
    simpa [cVecSpace, intVecSpace, reProj_smul]

-- ---------------------------------------------------------------------------
-- (L4) kernel 子空间：数乘封闭（补 K1 的加法封闭）
-- ---------------------------------------------------------------------------

/-- 线性映射的核在标量乘下封闭：π(c·x) = c·π(x) = c·0 = 0。 -/
theorem kernel_smul_closed {V W : Type} [Add V] [Add W] [Zero V] [Zero W]
    (VS : VecSpace V) (WS : VecSpace W) (T : V → W)
    (hT : LinearMap VS WS T) {x : V} (hx : T x = 0) (a : Int) :
    T (VS.smul a x) = 0 := by
  rw [hT.2 a x, hx]
  exact WS.smul_zero a

/-- 核是子空间：加法封闭（K1）+ 数乘封闭（L4）。 -/
theorem kernel_is_subspace {V W : Type} [Add V] [Add W] [Zero V] [Zero W]
    (VS : VecSpace V) (WS : VecSpace W) (T : V → W)
    (hT : LinearMap VS WS T) (h0 : T 0 = 0) :
    (∀ x y : V, T x = 0 → T y = 0 → T (x + y) = 0) ∧
    (∀ (a : Int) (x : V), T x = 0 → T (VS.smul a x) = 0) := by
  constructor
  · intro x y hx hy
    rw [hT.1 x y, hx, hy]
    exact WS.zero_add 0
  · intro a x hx
    exact kernel_smul_closed VS WS T hT hx a

-- ---------------------------------------------------------------------------
-- (L5) 基（张成 + 线性无关）与维度
-- ---------------------------------------------------------------------------

/-- 有限求和：vecSum n f = f 0 + ... + f (n−1)（结构递归）。 -/
def vecSum {V : Type} [Add V] [Zero V] : (n : Nat) → (Fin n → V) → V
  | 0, _ => 0
  | n + 1, f => vecSum n (fun i : Fin n => f (Fin.castSucc i)) + f (Fin.last n)

/-- 基：张成 + 线性无关。 -/
structure Basis (V : Type) (n : Nat) [Add V] [Zero V] (VS : VecSpace V) where
  basis : Fin n → V
  span : ∀ v : V, ∃ c : Fin n → Int, v = vecSum n (fun i => VS.smul (c i) (basis i))
  independent : ∀ c : Fin n → Int,
    vecSum n (fun i => VS.smul (c i) (basis i)) = 0 → ∀ i : Fin n, c i = 0

/-- 基的维度。 -/
def BasisDim {V : Type} {n : Nat} [Add V] [Zero V] {VS : VecSpace V}
    (B : Basis V n VS) : Nat := n

/-- 子空间基：张成子空间 { v | P v }（不要求张成整个空间）。
    ker π 的基是 SubBasis，不是 Basis。 -/
structure SubBasis (V : Type) (n : Nat) [Add V] [Zero V] (VS : VecSpace V) (P : V → Prop) where
  basis : Fin n → V
  in_subspace : ∀ i : Fin n, P (basis i)
  span : ∀ v : V, P v → ∃ c : Fin n → Int, v = vecSum n (fun i => VS.smul (c i) (basis i))
  independent : ∀ c : Fin n → Int,
    vecSum n (fun i => VS.smul (c i) (basis i)) = 0 → ∀ i : Fin n, c i = 0

/-- 子空间基的维度。 -/
def SubBasisDim {V : Type} {n : Nat} [Add V] [Zero V] {VS : VecSpace V}
    {P : V → Prop} (B : SubBasis V n VS P) : Nat := n

-- ---------------------------------------------------------------------------
-- (L6) ★ rank-nullity 具体验证：ℂ 的实部投影
--       dim ℂ = dim ker(Re) + dim im(Re) = 1 + 1
--       ker(Re) = 虚轴 iR（HIBS A3 的 iR），基 {i}
-- ---------------------------------------------------------------------------

/-- ker(Re) 的基：{i}（i = ⟨0,1⟩ ∈ ker 因为 Re(i) = 0）。 -/
def kerReBasis : Fin 1 → ℂ := fun _ => cI

/-- im(Re) 的基：{1}。 -/
def imReBasis : Fin 1 → Int := fun _ => 1

/-- ℂ 的基：{1, i}。 -/
def complexBasis : Fin 2 → ℂ :=
  fun i => if i.val = 0 then 1 else cI

-- ker(Re) 的张成：任何核元素是 i 的标量倍（z = z.im · i）
theorem kerRe_span : ∀ z : ℂ, reProj z = 0 →
    ∃ c : Fin 1 → Int, z = vecSum 1 (fun i => cSmul (c i) (kerReBasis i)) := by
  intro z hz
  refine ⟨fun _ => z.im, ?_⟩
  apply ℂ.ext
  · -- z.re = z.im * 0
    have hzr : z.re = 0 := hz
    simp [vecSum, cSmul, kerReBasis]
    exact hzr
  · simp [vecSum, cSmul, kerReBasis]

-- ker(Re) 的线性无关
theorem kerRe_independent : ∀ c : Fin 1 → Int,
    vecSum 1 (fun i => cSmul (c i) (kerReBasis i)) = 0 → ∀ i : Fin 1, c i = 0 := by
  intro c hc i
  have hza : ∀ x : ℂ, 0 + x = x := cVecSpace.zero_add
  have hc' : (⟨0, c 0⟩ : ℂ) = 0 := by
    simpa [vecSum, cSmul, kerReBasis, hza] using hc
  have hc0 : c 0 = 0 := by
    have him : (⟨0, c 0⟩ : ℂ).im = (0 : ℂ).im := congrArg (fun z : ℂ => z.im) hc'
    simpa using him
  -- i : Fin 1 ⟹ i = 0
  cases i with
  | mk n hn =>
    have hn0 : n = 0 := by omega
    subst n
    exact hc0

/-- ker(Re) 是 1 维子空间（基 {i}，i ∈ ker 因为 Re(i) = 0）。 -/
def kerReBasisInst : SubBasis ℂ 1 cVecSpace (fun z => reProj z = 0) :=
  { basis := kerReBasis
  , in_subspace := by intro i; simp [kerReBasis, reProj]
  , span := kerRe_span
  , independent := kerRe_independent }

-- im(Re) 的张成：任何整数 v 是 1 的标量倍（v = v · 1）
theorem imRe_span : ∀ v : Int, ∃ c : Fin 1 → Int,
    v = vecSum 1 (fun i => intVecSpace.smul (c i) (imReBasis i)) := by
  intro v
  refine ⟨fun _ => v, ?_⟩
  simpa [vecSum, imReBasis, intVecSpace]

-- im(Re) 的线性无关
theorem imRe_independent : ∀ c : Fin 1 → Int,
    vecSum 1 (fun i => intVecSpace.smul (c i) (imReBasis i)) = 0 → ∀ i : Fin 1, c i = 0 := by
  intro c hc i
  have hc0 : c 0 = 0 := by
    simpa [vecSum, imReBasis, intVecSpace, Int.mul_one] using hc
  -- i : Fin 1 ⟹ i = 0
  cases i with
  | mk n hn =>
    have hn0 : n = 0 := by omega
    subst n
    exact hc0

/-- im(Re) 是 1 维的。 -/
def imReBasisInst : Basis Int 1 intVecSpace :=
  { basis := imReBasis
  , span := imRe_span
  , independent := imRe_independent }

-- ℂ 的张成：任何 z = z.re · 1 + z.im · i
theorem complex_span : ∀ z : ℂ, ∃ c : Fin 2 → Int,
    z = vecSum 2 (fun i => cSmul (c i) (complexBasis i)) := by
  intro z
  refine ⟨fun i => if i.val = 0 then z.re else z.im, ?_⟩
  apply ℂ.ext
  · simp [vecSum, cSmul, complexBasis]
  · simp [vecSum, cSmul, complexBasis]

-- ℂ 的线性无关
theorem complex_independent : ∀ c : Fin 2 → Int,
    vecSum 2 (fun i => cSmul (c i) (complexBasis i)) = 0 → ∀ i : Fin 2, c i = 0 := by
  intro c hc i
  have hc0 : c 0 = 0 := by
    have hre : (vecSum 2 (fun i => cSmul (c i) (complexBasis i))).re = (0 : ℂ).re :=
      congrArg (fun z : ℂ => z.re) hc
    simpa [vecSum, cSmul, complexBasis, Int.mul_one, cVecSpace] using hre
  have hc1 : c 1 = 0 := by
    have him : (vecSum 2 (fun i => cSmul (c i) (complexBasis i))).im = (0 : ℂ).im :=
      congrArg (fun z : ℂ => z.im) hc
    simpa [vecSum, cSmul, complexBasis, Int.mul_one, cVecSpace] using him
  -- i : Fin 2 ⟹ i.val = 0 或 i.val = 1
  have hval : i.val = 0 ∨ i.val = 1 := by omega
  rcases hval with h0 | h1
  · have hi : i = 0 := Fin.ext h0
    rw [hi]
    exact hc0
  · have hi : i = 1 := Fin.ext h1
    rw [hi]
    exact hc1

/-- ℂ 是 2 维的。 -/
def complexBasisInst : Basis ℂ 2 cVecSpace :=
  { basis := complexBasis
  , span := complex_span
  , independent := complex_independent }

/-- ★ rank-nullity 具体验证：
    dim ℂ = dim ker(Re) + dim im(Re)（2 = 1 + 1）。
    虚轴 iR 是实部投影的核——HIBS 的"i ∈ ker(Re)"就是 A3 的 iR。 -/
theorem rank_nullity_complex_re :
    BasisDim complexBasisInst = SubBasisDim kerReBasisInst + BasisDim imReBasisInst := by
  rfl

-- ---------------------------------------------------------------------------
-- (L7) 双线性形式（张量原语）+ 极化恒等式
-- ---------------------------------------------------------------------------

/-- 双线性形式 B : V × V → Int（张量 V* ⊗ V* 的坐标表示）。
    对称性 + 两个参数的线性。 -/
structure BiForm (V : Type) [Add V] [Zero V] (VS : VecSpace V) where
  B : V → V → Int
  add_left : ∀ x y z : V, B (x + y) z = B x z + B y z
  add_right : ∀ x y z : V, B x (y + z) = B x y + B x z
  sym : ∀ x y : V, B x y = B y x

/-- 由双线性形式诱导的二次型 Q(x) := B(x, x)。 -/
def quadOfBiForm {V : Type} [Add V] [Zero V] {VS : VecSpace V}
    (bf : BiForm V VS) (x : V) : Int :=
  bf.B x x

/-- ★ 极化恒等式（Jordan–von Neumann 第一步）：
    2·B(x,y) = Q(x+y) − Q(x) − Q(y)。
    这是"度规从二次型涌现"的代数心脏：B 完全由 Q 决定。 -/
theorem polarization {V : Type} [Add V] [Zero V] {VS : VecSpace V}
    (bf : BiForm V VS) :
    ∀ x y : V, 2 * bf.B x y = quadOfBiForm bf (x + y) - quadOfBiForm bf x - quadOfBiForm bf y := by
  intro x y
  unfold quadOfBiForm
  -- Q(x+y) = B(x+y, x+y) = B x (x+y) + B y (x+y) = B x x + B x y + B y x + B y y
  rw [bf.add_left, bf.add_right, bf.add_right, bf.sym]
  omega

/-- 二次型在零元素上为零：Q(0) = B(0,0) = 0（用线性性）。 -/
theorem quad_zero {V : Type} [Add V] [Zero V] {VS : VecSpace V}
    (bf : BiForm V VS) : quadOfBiForm bf 0 = 0 := by
  unfold quadOfBiForm
  -- B(0, 0) = B(0 + 0, 0) = B 0 0 + B 0 0，故 B 0 0 = 0
  have hz : (0 : V) + 0 = 0 := VS.zero_add 0
  have h : bf.B 0 0 = bf.B 0 0 + bf.B 0 0 := by
    rw [← bf.add_left, hz]
  omega

-- ---------------------------------------------------------------------------
-- (L8) ★ 表示完备性（ℂ 实例）：分解唯一性 + 范数分解
-- ---------------------------------------------------------------------------

instance : Nonempty ℂ := Nonempty.intro (⟨0, 0⟩ : ℂ)

/-- 正交分解：z = Re(z)·1 + Im(z)·i（可观测部分 + 核部分）。 -/
theorem cOrthogonalDecomp (z : ℂ) :
    z = cSmul (z.re) 1 + cSmul (z.im) cI := by
  apply ℂ.ext <;> simp [cSmul] <;> omega

/-- 分解唯一性：z = a·1 + b·i ⟹ a = Re z ∧ b = Im z。 -/
theorem cOrthogonalDecomp_unique (z : ℂ) {a b : Int}
    (hz : z = cSmul a 1 + cSmul b cI) : a = z.re ∧ b = z.im := by
  have hre : z.re = a := by
    have h := congrArg (fun w : ℂ => w.re) hz
    simp [cSmul] at h
    omega
  have him : z.im = b := by
    have h := congrArg (fun w : ℂ => w.im) hz
    simp [cSmul] at h
    omega
  exact ⟨hre.symm, him.symm⟩

/-- 核分量提取：ζ_κ(z) := Im(z)·i ∈ ker(Re)。 -/
def kernelComponentC (z : ℂ) : KernelOf reProj :=
  ⟨cSmul (z.im) cI, by simp [reProj, cSmul]⟩

theorem kernelComponentC_im (z : ℂ) : (kernelComponentC z).val.im = z.im := by
  simp [kernelComponentC, cSmul, cI]

/-- 核不变量 κ：核元素的虚部平方。 -/
def kernelInvC (k : KernelOf reProj) : Int :=
  k.val.im * k.val.im

/-- ★ 范数分解（完备性的具体形式）：
    |z|² = Re(z)² + Im(z)² = Q(π z) + κ(ζ_κ z)。
    信息量 = Image 二次型 + Kernel 二次型，无第三自由度。 -/
def cNormSq (z : ℂ) : Int := z.re * z.re + z.im * z.im

theorem completeness_complex (z : ℂ) :
    cNormSq z = (reProj z) * (reProj z) + kernelInvC (kernelComponentC z) := by
  simp [cNormSq, reProj, kernelInvC, kernelComponentC_im]

/-- 任意可观测 I = J∘Re（C1 在 ℂ 上的实例化：Image 完全决定观测）。 -/
theorem observable_factors_through_re (I : ℂ → Int) (hI : IsObservable reProj I) :
    ∃ J : Int → Int, ∀ z : ℂ, I z = J (reProj z) :=
  invariant_factor_through_projection reProj I hI

/-- ★ RepresentationCompleteness 的 ℂ 实例：所有字段全部证明（草案实例化）。 -/
def completenessComplex : RepresentationCompleteness ℂ Int reProj :=
  { hadd := reProj_add
  , non_injective := by
      refine ⟨cI, 0, ?_, ?_⟩
      · intro h
        have him := congrArg (fun z : ℂ => z.im) h
        simp [cI] at him
      · rfl
  , Q := fun v => v * v
  , Q_quadratic := by simp
  , kernelComponent := kernelComponentC
  , κ := kernelInvC
  , complete := by
      intro I hI
      exact invariant_factor_through_projection reProj I hI }

/-- 核质量归零（ℂ 实例）：核元素为零 ⟹ κ = 0。 -/
theorem kernelInv_zero_of_zero {k : KernelOf reProj} (hk : k.val = 0) :
    kernelInvC k = 0 := by
  simp [kernelInvC, hk]

end ProjectionPhysics
