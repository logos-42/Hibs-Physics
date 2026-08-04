-- ProjectionPhysics — Differential Emergence（草案 D7 的代数种子）
--
-- Module 9: Differential.lean
--
-- 草案 D7（Differential Emergence）把向量微积分算子识别为 End(S) 环上的表示：
--   斜率 := π ∘ L      （线性化在观测方向的投影）
--   散度 := tr(L)      （线性化的迹：核方向的信息流）
--   旋度 := (L − Lᵀ)/2 （线性化的反对称部分：Clifford 楔积空间的元素）
--
-- 本模块在 core Lean 中把"微积分的代数雏形"显式化（不引入连续性/逆元/极限）：
--   (E1)  迹的线性性        tr(M+N) = tr M + tr N        （散度是线性标量函数）
--   (E2)  迹的奇偶性        tr(−M) = −tr M；tr(0) = 0；tr(I) = 1+1 = 维数
--   (E3)  迹对转置不变      tr(Mᵀ) = tr M
--   (E4)  ★ 散度∘旋度 = 0   tr(M − Mᵀ) = 0               （旋度无源：∇·(∇×A)=0 的代数种子）
--   (E5)  ★ 旋度反对称      (M − Mᵀ)ᵀ = −(M − Mᵀ)        （楔积空间的元素）
--   (E6)  对称/反对称分解    (M + Mᵀ) + (M − Mᵀ) = M + M  （无除法的 Cartan 分解）
--   (E7)  ★ 迹的循环性      tr(MN) = tr(NM)              （信息流守恒的代数形状）
--   (E8)  迹是环上标量函数  tr(z·M) = z·tr M              （散度 = 系数环上的标量）
--   (E9)  ★ 导数 = 线性算子本身：L(s+h) − L(s) = L(h)    （差商与位置无关；D7 平凡但关键推论）
--   (E10) 斜率 = π∘L 的差商形式                          （A1 复合封闭 ⟹ π∘L 仍保加法）
--   (E11) 自旋无迹：tr σᵢ = 0                            （旋量流无散）
--   (E12) σ₂ 反对称 / σ₁,σ₃ 对称                         （自旋的旋转部分 = 旋度生成元）
--
-- 支撑引理：转置的代数性质（对合/保加法/反同态）、Mat2 加法群定律。

import ProjectionPhysics.Clifford

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- 转置（旋度的原料）
-- ---------------------------------------------------------------------------

/-- 转置：Mᵀ = [[a, c], [b, d]]。 -/
def matTranspose (M : Mat2) : Mat2 := ⟨M.a, M.c, M.b, M.d⟩

@[simp] theorem matTranspose_a (M : Mat2) : (matTranspose M).a = M.a := rfl
@[simp] theorem matTranspose_b (M : Mat2) : (matTranspose M).b = M.c := rfl
@[simp] theorem matTranspose_c (M : Mat2) : (matTranspose M).c = M.b := rfl
@[simp] theorem matTranspose_d (M : Mat2) : (matTranspose M).d = M.d := rfl

/-- Mat2 减法：M − N := M + (−N)。只需 Neg，不需要除法/逆元。 -/
instance : Sub Mat2 := ⟨fun M N => M + (-N)⟩

@[simp] theorem Mat2.sub_a (M N : Mat2) : (M - N).a = M.a + (-N.a) := rfl
@[simp] theorem Mat2.sub_b (M N : Mat2) : (M - N).b = M.b + (-N.b) := rfl
@[simp] theorem Mat2.sub_c (M N : Mat2) : (M - N).c = M.c + (-N.c) := rfl
@[simp] theorem Mat2.sub_d (M N : Mat2) : (M - N).d = M.d + (-N.d) := rfl

/-- 转置对合：(Mᵀ)ᵀ = M。 -/
theorem matTranspose_transpose (M : Mat2) : matTranspose (matTranspose M) = M := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [matTranspose] <;> omega

/-- 转置保加法：(M + N)ᵀ = Mᵀ + Nᵀ。 -/
theorem matTranspose_add (M N : Mat2) :
    matTranspose (M + N) = matTranspose M + matTranspose N := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [matTranspose, ℂ.add_re, ℂ.add_im] <;> omega

/-- 转置保反号：(−M)ᵀ = −Mᵀ。 -/
theorem matTranspose_neg (M : Mat2) : matTranspose (-M) = -matTranspose M := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [matTranspose, ℂ.neg_re, ℂ.neg_im] <;> omega

/-- (MN)ᵀ = NᵀMᵀ：转置是反同态（矩阵乘法在转置下反序）。 -/
theorem matTranspose_mul (M N : Mat2) :
    matTranspose (matMul M N) = matMul (matTranspose N) (matTranspose M) := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [matTranspose, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.mul_comm] <;> omega

-- ---------------------------------------------------------------------------
-- 迹（散度的代数身份）
-- ---------------------------------------------------------------------------

/-- 迹：tr(M) := M.a + M.d。End(S) 的矩阵表示上的标量函数（散度的候选代数身份）。 -/
def matTr (M : Mat2) : ℂ := M.a + M.d

@[simp] theorem matTr_re (M : Mat2) : (matTr M).re = M.a.re + M.d.re := rfl
@[simp] theorem matTr_im (M : Mat2) : (matTr M).im = M.a.im + M.d.im := rfl

-- (E1) 迹线性：散度是线性标量函数
theorem matTr_add (M N : Mat2) : matTr (M + N) = matTr M + matTr N := by
  apply ℂ.ext <;> simp [matTr, Mat2.add_a, Mat2.add_d, ℂ.add_re, ℂ.add_im] <;> omega

-- (E2) 迹的奇偶性
theorem matTr_neg (M : Mat2) : matTr (-M) = -matTr M := by
  apply ℂ.ext <;> simp [matTr, Mat2.neg_a, Mat2.neg_d, ℂ.add_re, ℂ.add_im, ℂ.neg_re, ℂ.neg_im] <;> omega

theorem matTr_zero : matTr 0 = 0 := rfl

/-- tr(I) = 1 + 1：恒等自同态的迹 = 表示维数（ℂ 上 = 2）。 -/
theorem matTr_one : matTr (1 : Mat2) = (1 : ℂ) + 1 := rfl

-- (E3) 迹对转置不变（对角线不变）
theorem matTr_transpose (M : Mat2) : matTr (matTranspose M) = matTr M := by
  apply ℂ.ext <;> simp [matTr, matTranspose, ℂ.add_re, ℂ.add_im] <;> omega

-- (E4) ★ 散度∘旋度 = 0：迹杀死反对称部分。∇·(∇×A) = 0 的代数种子
theorem matTr_skew_zero (M : Mat2) : matTr (M - matTranspose M) = 0 := by
  apply ℂ.ext <;>
    simp [matTr, matTranspose, Mat2.sub_a, Mat2.sub_d, ℂ.add_re, ℂ.add_im, ℂ.neg_re, ℂ.neg_im] <;> omega

-- (E5) ★ 旋度反对称：(M − Mᵀ)ᵀ = −(M − Mᵀ)。反对称部分 = 楔积空间的元素
theorem skew_antisymmetric (M : Mat2) :
    matTranspose (M - matTranspose M) = -(M - matTranspose M) := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [matTranspose, Mat2.sub_a, Mat2.sub_b, Mat2.sub_c, Mat2.sub_d,
          Mat2.neg_a, Mat2.neg_b, Mat2.neg_c, Mat2.neg_d,
          ℂ.add_re, ℂ.add_im, ℂ.neg_re, ℂ.neg_im] <;> omega

-- (E6) 对称/反对称分解（无除法版本）：(M + Mᵀ) + (M − Mᵀ) = M + M = 2M
theorem sym_skew_decomposition (M : Mat2) :
    (M + matTranspose M) + (M - matTranspose M) = M + M := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [matTranspose, Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d,
          Mat2.sub_a, Mat2.sub_b, Mat2.sub_c, Mat2.sub_d, ℂ.add_re, ℂ.add_im] <;> omega

-- (E7) ★ 迹的循环性：tr(MN) = tr(NM)。"散度 = 信息流"守恒律的代数形状
theorem matTr_mul_comm (M N : Mat2) : matTr (matMul M N) = matTr (matMul N M) := by
  apply ℂ.ext <;>
    simp [matTr, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im, Int.mul_comm] <;> omega

-- (E8) 迹是环上的线性标量函数：tr(z·M) = z·tr(M)。散度 = 标量（核方向信息流的数值）
theorem matTr_scalar (z : ℂ) (M : Mat2) : matTr (matMul (scalar2 z) M) = z * matTr M := by
  apply ℂ.ext <;>
    simp [matTr, scalar2, matMul, ℂ.add_re, ℂ.add_im, ℂ.mul_re, ℂ.mul_im,
          Int.mul_add, Int.mul_comm] <;> omega

-- ---------------------------------------------------------------------------
-- Mat2 加法群定律（差商定理的地基）
-- ---------------------------------------------------------------------------

theorem Mat2.add_assoc (M N P : Mat2) : M + N + P = M + (N + P) := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [Mat2.add_a, Mat2.add_b, Mat2.add_c, Mat2.add_d, ℂ.add_re, ℂ.add_im] <;> omega

theorem Mat2.zero_add (M : Mat2) : 0 + M = M := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [ℂ.add_re, ℂ.add_im] <;> omega

theorem Mat2.add_zero (M : Mat2) : M + 0 = M := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [ℂ.add_re, ℂ.add_im] <;> omega

theorem Mat2.add_left_neg (M : Mat2) : -M + M = 0 := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [Mat2.neg_a, Mat2.neg_b, Mat2.neg_c, Mat2.neg_d, ℂ.neg_re, ℂ.neg_im] <;> omega

theorem Mat2.add_right_neg (M : Mat2) : M + -M = 0 := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [Mat2.neg_a, Mat2.neg_b, Mat2.neg_c, Mat2.neg_d, ℂ.neg_re, ℂ.neg_im] <;> omega

-- ---------------------------------------------------------------------------
-- (E9) ★ 导数 = 线性算子本身（D7 的平凡但关键推论）
-- ---------------------------------------------------------------------------

/-- 线性映射的差商与位置无关：L(s + h) − L(s) = L(h)。
    这就是"线性映射的差商恒等于它自己"的精确形式——
    在出现非线性映射之前，微积分没有可推导的内容。 -/
theorem linear_map_difference_quotient (L : Mat2 → Mat2) (hL : AdditiveMap L) :
    ∀ s h : Mat2, L (s + h) + (-L s) = L h := by
  intro s h
  have hlin := hL s h
  rw [hlin]
  calc
    L s + L h + -L s = L h + L s + -L s := by rw [Mat2.add_comm (L s) (L h)]
    _ = L h + (L s + -L s) := by rw [Mat2.add_assoc]
    _ = L h + 0 := by rw [Mat2.add_right_neg]
    _ = L h := by rw [Mat2.add_zero]

-- ---------------------------------------------------------------------------
-- (E10) 斜率 = π ∘ L：可观测演化比率的差商形式
-- ---------------------------------------------------------------------------

/-- 斜率（线性化在观测方向的投影）的差商恒等于它自己：
    复合保加法（A1：comp_additive）⟹ 投影线性化仍是线性化。 -/
theorem slope_difference_quotient (π L : Mat2 → Mat2) (hπ : AdditiveMap π) (hL : AdditiveMap L) :
    ∀ s h : Mat2, (π ∘ L) (s + h) + (-(π ∘ L) s) = (π ∘ L) h := by
  exact linear_map_difference_quotient (π ∘ L) (comp_additive π L hπ hL)

-- ---------------------------------------------------------------------------
-- (E11) 自旋无迹：tr σᵢ = 0（旋量流无散）
-- ---------------------------------------------------------------------------

theorem sigma1_trace_zero : matTr σ₁ = 0 := rfl
theorem sigma2_trace_zero : matTr σ₂ = 0 := rfl
theorem sigma3_trace_zero : matTr σ₃ = 0 := rfl

/-- Pauli 生成元全部无迹：散度(γ) = 0（自旋算子不产生净信息流）。 -/
theorem pauli_trace_zero (i : Fin 3) : matTr (pauliGamma i) = 0 := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hi with hi0 | hi1 | hi2
  · have hi0f : i = (0 : Fin 3) := Fin.ext hi0
    rw [hi0f]
    simp [pauliGamma, sigma1_trace_zero]
  · have hi1f : i = (1 : Fin 3) := Fin.ext hi1
    rw [hi1f]
    simp [pauliGamma, sigma2_trace_zero]
  · have hi2f : i = (2 : Fin 3) := Fin.ext hi2
    rw [hi2f]
    simp [pauliGamma, sigma3_trace_zero]

-- ---------------------------------------------------------------------------
-- (E12) 对称/反对称分类：σ₂ 是旋度生成元
-- ---------------------------------------------------------------------------

theorem sigma1_symmetric : matTranspose σ₁ = σ₁ := rfl
theorem sigma3_symmetric : matTranspose σ₃ = σ₃ := rfl

/-- ★ σ₂ 反对称：σ₂ᵀ = −σ₂。自旋的旋转部分（旋度生成元）由 σ₂ 承载。 -/
theorem sigma2_skewsymmetric : matTranspose σ₂ = -σ₂ := rfl

end ProjectionPhysics
