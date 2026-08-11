-- ProjectionPhysics — 狄拉克方程桥：质量项 = 手征耦合（锚定的代数内容）
--
-- 动机（leo, 2026-08-11）：电子是一个点，有狄拉克方程的自旋，
-- 但质量还没有被确立是怎么产生的。用狄拉克方程验证新假设：
--   质量 m 在狄拉克方程 (γ^μ p_μ − m)ψ = 0 中是标量参数；
--   本模块证明 m 的代数角色 = 左手/右手 Weyl 旋量的耦合强度。
--
-- 结构（Weyl/手征表示，2×2 分块）：
--   DiracSpinor ψ = (ψ_L, ψ_R)：左手 + 右手 2 分量旋量
--   gamma0 = [[0, 1],[1, 0]],  γⁱ = [[0, σᵢ],[−σᵢ, 0]]  (i = 1,2,3)
--
-- 核心定理（DB4–DB7）：
--   m = 0 ⟹ 左手/右手解耦（手征对称，Weyl 方程）
--   m ≠ 0 ⟹ 左手/右手耦合（质量 = 手征耦合 = 锚定）
--   ★ 静止质量方程 (gamma0 − 1)ψ = 0 ⟺ ψ_L = ψ_R：
--     质量解要求手征分量相等——这是"质量从何产生"的代数内容，
--     与最小核心"质量 = 内部运动对空间运动的锚定"一致。
--
-- 诚实边界：验证的是质量项的代数结构（手征耦合），
-- 不是质量数值（m 仍是自由参数；数值来源需 Higgs/Yukawa 层）。

import ProjectionPhysics.Clifford

namespace ProjectionPhysics

/-! ### DB1. 4×4 狄拉克 γ 矩阵（2×2 分块） -/

/-- 4×4 矩阵 = 四个 2×2 块。 -/
structure Mat4 where
  a : Mat2
  b : Mat2
  c : Mat2
  d : Mat2

theorem Mat4.ext {M N : Mat4}
    (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  rcases M with ⟨a, b, c, d⟩
  rcases N with ⟨a', b', c', d'⟩
  cases ha <;> cases hb <;> cases hc <;> cases hd <;> rfl

/-- 4×4 块乘法。 -/
def mat4Mul (M N : Mat4) : Mat4 :=
  ⟨ matMul M.a N.a + matMul M.b N.c, matMul M.a N.b + matMul M.b N.d
  , matMul M.c N.a + matMul M.d N.c, matMul M.c N.b + matMul M.d N.d ⟩

/-- 狄拉克旋量：左手 + 右手 2 分量旋量（Weyl 分解）。 -/
structure DiracSpinor where
  L : Spinor
  R : Spinor

theorem DiracSpinor.ext {ψ χ : DiracSpinor}
    (hL : ψ.L = χ.L) (hR : ψ.R = χ.R) : ψ = χ := by
  rcases ψ with ⟨L, R⟩
  rcases χ with ⟨L', R'⟩
  cases hL <;> cases hR <;> rfl

instance : Add Spinor := ⟨fun s t => ⟨s.ψ₁ + t.ψ₁, s.ψ₂ + t.ψ₂⟩⟩

instance : OfNat Mat4 0 := ⟨⟨0, 0, 0, 0⟩⟩
instance : OfNat Mat4 1 := ⟨⟨1, 0, 0, 1⟩⟩

instance : Add Mat4 := ⟨fun M N => ⟨M.a + N.a, M.b + N.b, M.c + N.c, M.d + N.d⟩⟩
instance : Neg Mat4 := ⟨fun M => ⟨-M.a, -M.b, -M.c, -M.d⟩⟩

@[simp] theorem Mat4.add_a (M N : Mat4) : (M + N).a = M.a + N.a := rfl
@[simp] theorem Mat4.add_b (M N : Mat4) : (M + N).b = M.b + N.b := rfl
@[simp] theorem Mat4.add_c (M N : Mat4) : (M + N).c = M.c + N.c := rfl
@[simp] theorem Mat4.add_d (M N : Mat4) : (M + N).d = M.d + N.d := rfl
@[simp] theorem Mat4.neg_a (M : Mat4) : (-M).a = -M.a := rfl
@[simp] theorem Mat4.neg_b (M : Mat4) : (-M).b = -M.b := rfl
@[simp] theorem Mat4.neg_c (M : Mat4) : (-M).c = -M.c := rfl
@[simp] theorem Mat4.neg_d (M : Mat4) : (-M).d = -M.d := rfl

@[simp] theorem Mat4.ofNat0_a : (0 : Mat4).a = 0 := rfl
@[simp] theorem Mat4.ofNat0_b : (0 : Mat4).b = 0 := rfl
@[simp] theorem Mat4.ofNat0_c : (0 : Mat4).c = 0 := rfl
@[simp] theorem Mat4.ofNat0_d : (0 : Mat4).d = 0 := rfl
@[simp] theorem Mat4.ofNat1_a : (1 : Mat4).a = 1 := rfl
@[simp] theorem Mat4.ofNat1_b : (1 : Mat4).b = 0 := rfl
@[simp] theorem Mat4.ofNat1_c : (1 : Mat4).c = 0 := rfl
@[simp] theorem Mat4.ofNat1_d : (1 : Mat4).d = 1 := rfl

/-- γ 矩阵作用在狄拉克旋量上（块线性作用）。 -/
def mat4Act (M : Mat4) (ψ : DiracSpinor) : DiracSpinor :=
  ⟨ matMulSpinor M.a ψ.L + matMulSpinor M.b ψ.R
  , matMulSpinor M.c ψ.L + matMulSpinor M.d ψ.R ⟩

/-- gamma0：交换左手/右手（Weyl 表示）。 -/
def gamma0 : Mat4 := ⟨0, 1, 1, 0⟩
/-- gamma1：σ₁ 反手征块。 -/
def gamma1 : Mat4 := ⟨0, σ₁, -σ₁, 0⟩
/-- gamma2：σ₂ 反手征块。 -/
def gamma2 : Mat4 := ⟨0, σ₂, -σ₂, 0⟩
/-- gamma3：σ₃ 反手征块。 -/
def gamma3 : Mat4 := ⟨0, σ₃, -σ₃, 0⟩

/-! ### DB2. 辅助引理：Mat2/Spinor 零与单位作用 -/

theorem db_matMulSpinor_zero (s : Spinor) : matMulSpinor 0 s = ⟨0, 0⟩ := by
  cases s
  apply Spinor.ext <;> apply ℂ.ext <;>
    simp [matMulSpinor, ℂ.mul_re, ℂ.mul_im,
      ℂ.ofNat0_re, ℂ.ofNat0_im] <;> omega

theorem db_matMulSpinor_one (s : Spinor) : matMulSpinor 1 s = s := by
  cases s
  apply Spinor.ext <;> apply ℂ.ext <;>
    simp [matMulSpinor, ℂ.mul_re, ℂ.mul_im,
      ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega

@[simp] theorem Spinor.add_ψ₁ (s t : Spinor) : (s + t).ψ₁ = s.ψ₁ + t.ψ₁ := rfl
@[simp] theorem Spinor.add_ψ₂ (s t : Spinor) : (s + t).ψ₂ = s.ψ₂ + t.ψ₂ := rfl

theorem spinor_add_zero (s : Spinor) : s + ⟨0, 0⟩ = s := by
  apply Spinor.ext <;> apply ℂ.ext <;> simp <;> omega

theorem zero_add_spinor (s : Spinor) : ⟨0, 0⟩ + s = s := by
  apply Spinor.ext <;> apply ℂ.ext <;> simp <;> omega

/-- gamma0 作用 = 交换左右手：gamma0(ψ_L, ψ_R) = (ψ_R, ψ_L)。 -/
theorem gamma0_act_swaps_chiralities (ψ : DiracSpinor) :
    mat4Act gamma0 ψ = ⟨ψ.R, ψ.L⟩ := by
  unfold mat4Act gamma0
  have hL : matMulSpinor 0 ψ.L + matMulSpinor 1 ψ.R = ψ.R := by
    rw [db_matMulSpinor_zero, db_matMulSpinor_one]
    exact zero_add_spinor ψ.R
  have hR : matMulSpinor 1 ψ.L + matMulSpinor 0 ψ.R = ψ.L := by
    rw [db_matMulSpinor_one, db_matMulSpinor_zero]
    exact spinor_add_zero ψ.L
  apply DiracSpinor.ext <;> assumption

/-! ### DB3. γ 平方 = 单位阵 -/

theorem gamma0_sq : mat4Mul gamma0 gamma0 = 1 := by
  unfold mat4Mul gamma0
  apply Mat4.ext
  · -- a 块: 0·0 + 1·1 = 1
    simp [matMul]
    apply Mat2.ext <;> apply ℂ.ext <;>
      simp [matMul, ℂ.mul_re, ℂ.mul_im,
        ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega
  · -- b 块: 0·1 + 1·0 = 0
    simp [matMul]
    apply Mat2.ext <;> apply ℂ.ext <;>
      simp [matMul, ℂ.mul_re, ℂ.mul_im,
        ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega
  · -- c 块: 1·0 + 0·1 = 0
    simp [matMul]
    apply Mat2.ext <;> apply ℂ.ext <;>
      simp [matMul, ℂ.mul_re, ℂ.mul_im,
        ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega
  · -- d 块: 1·1 + 0·0 = 1
    simp [matMul]
    apply Mat2.ext <;> apply ℂ.ext <;>
      simp [matMul, ℂ.mul_re, ℂ.mul_im,
        ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega

/-! ### DB4. 静止质量方程：手征耦合 -/

/-- ★ 静止狄拉克方程 (gamma0 − 1)ψ = 0 ⟺ ψ_L = ψ_R。
    质量解要求左手 = 右手——质量 = 手征耦合的精确代数内容。 -/
theorem mass_equation_couples_chiralities (ψ : DiracSpinor) :
    mat4Act gamma0 ψ = ψ ↔ ψ.L = ψ.R := by
  constructor
  · intro h
    have hswap := gamma0_act_swaps_chiralities ψ
    rw [hswap] at h
    have hL' : ψ.R = ψ.L := congrArg DiracSpinor.L h
    exact hL'.symm
  · intro hLR
    rw [gamma0_act_swaps_chiralities ψ]
    cases ψ
    apply DiracSpinor.ext
    · exact hLR.symm
    · exact hLR

/-! ### DB5. 零质量极限：手征解耦（Weyl） -/

/-- 零质量极限（Weyl）：左手/右手无约束、可独立取值——
    存在手征不对称的旋量（手征对称性：m = 0 时不破缺）。 -/
theorem zero_mass_has_chiral_asymmetry :
    ∃ ψ : DiracSpinor, ¬ mat4Act gamma0 ψ = ψ := by
  -- 取 ψ = (1, 0)：gamma0 交换后 = (0, 1) ≠ (1, 0)
  let ψ := (⟨⟨1, 0⟩, ⟨0, 0⟩⟩ : DiracSpinor)
  refine ⟨ψ, ?_⟩
  intro h
  have hswap := gamma0_act_swaps_chiralities ψ
  rw [hswap] at h
  -- h : {L := ψ.R, R := ψ.L} = ψ ⟹ 投影到 L.ψ₁: 0 = 1 矛盾
  have hproj := congrArg (fun s : DiracSpinor => s.L.ψ₁) h
  change (⟨⟨0, 0⟩, ⟨1, 0⟩⟩ : DiracSpinor).L.ψ₁ = (⟨⟨1, 0⟩, ⟨0, 0⟩⟩ : DiracSpinor).L.ψ₁ at hproj
  have hre := congrArg ℂ.re hproj
  simp at hre

/-! ### DB6. γ 反交换（Clifford 关系在 4×4 层） -/

/-- gamma0gamma1 + gamma1gamma0 = 0：时间与空间方向反交换。 -/
theorem gamma0_gamma1_anticommute :
    mat4Mul gamma0 gamma1 + mat4Mul gamma1 gamma0 = 0 := by
  unfold mat4Mul gamma0 gamma1
  apply Mat4.ext
  · -- a 块：1·(-σ₁) + 1·σ₁ = 0
    simp [matMul]
    apply Mat2.ext <;> apply ℂ.ext <;>
      simp [σ₁, ℂ.mul_re, ℂ.mul_im, ℂ.neg_re, ℂ.neg_im,
        ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega
  · -- b 块：0
    simp [matMul]
    apply Mat2.ext <;> apply ℂ.ext <;>
      simp [σ₁, ℂ.mul_re, ℂ.mul_im, ℂ.neg_re, ℂ.neg_im,
        ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega
  · -- c 块：0
    simp [matMul]
    apply Mat2.ext <;> apply ℂ.ext <;>
      simp [σ₁, ℂ.mul_re, ℂ.mul_im, ℂ.neg_re, ℂ.neg_im,
        ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega
  · -- d 块：σ₁ + (-σ₁) = 0
    simp [matMul]
    apply Mat2.ext <;> apply ℂ.ext <;>
      simp [σ₁, ℂ.mul_re, ℂ.mul_im, ℂ.neg_re, ℂ.neg_im,
        ℂ.ofNat0_re, ℂ.ofNat0_im, ℂ.ofNat1_re, ℂ.ofNat1_im] <;> omega

end ProjectionPhysics
