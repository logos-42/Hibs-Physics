-- ProjectionPhysics — Quaternions from Clifford Anticommutation
--
-- Module 13: Quaternion.lean
--
-- 推导链(对应 SPEC 草案 D9):
--
--   Clifford 反交换(C2: σᵢσⱼ + σⱼσᵢ = 0)
--     ⟹ 四元数单位 {i, j, k} 满足:
--         (Q1) i² = j² = k² = -1   (每个生成元平方 = -1,复现 C3 的 i 涌现)
--         (Q2) i·j·k = -1          (三生成元积 = -1)
--         (Q3) i·j ≠ j·i           (非交换:ij = k, ji = -k)
--     ⟹ 表示 Φ(a+bi+cj+dk) = aI + b(iσ₁) + c(iσ₂) + d(iσ₃) 保加法保乘法
--     ⟹ ★ 隐数空间中的"i²=-1 型单元"是反交换的必然表示,不是新公理
--
-- 本模块只使用 core Lean 4(无 mathlib),Int 为系数(ℤ 上的四元数环,
-- 同 ℂ = ℤ[i]:无逆元,D7' 卡点的同类结构)。

import ProjectionPhysics.LinearAlgebra
import ProjectionPhysics.Clifford

-- 该 linter 建议用 `simp at h` 替代 `simpa using h`;但 ground 矛盾等式
-- (如 1 = -1)经 `simp at h` 化简为 False 时会自动关闭目标,后续 tactic
-- 报 "No goals to be solved"(omega/exact 均触发)。此处抑制。
set_option linter.unnecessarySimpa false

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- Hamilton 四元数:ℤ 系数环
-- ---------------------------------------------------------------------------

/-- Hamilton 四元数 a + b·i + c·j + d·k(Int 系数,core 版)。
    乘法表:ij = k, jk = i, ki = j, 反交换(ji = -k 等)。 -/
structure Quat where
  re : Int
  qi : Int
  qj : Int
  qk : Int

instance : Add Quat :=
  ⟨fun q p => ⟨q.re + p.re, q.qi + p.qi, q.qj + p.qj, q.qk + p.qk⟩⟩

instance : Neg Quat :=
  ⟨fun q => ⟨-q.re, -q.qi, -q.qj, -q.qk⟩⟩

instance : OfNat Quat 0 := ⟨⟨0, 0, 0, 0⟩⟩
instance : OfNat Quat 1 := ⟨⟨1, 0, 0, 0⟩⟩

/-- 四元数乘法(Hamilton 表)。 -/
instance : Mul Quat :=
  ⟨fun q p =>
    ⟨ q.re * p.re - q.qi * p.qi - q.qj * p.qj - q.qk * p.qk
    , q.re * p.qi + q.qi * p.re + q.qj * p.qk - q.qk * p.qj
    , q.re * p.qj - q.qi * p.qk + q.qj * p.re + q.qk * p.qi
    , q.re * p.qk + q.qi * p.qj - q.qj * p.qi + q.qk * p.re ⟩⟩

theorem Quat.ext {q p : Quat}
    (h1 : q.re = p.re) (h2 : q.qi = p.qi) (h3 : q.qj = p.qj) (h4 : q.qk = p.qk) : q = p := by
  rcases q with ⟨a, b, c, d⟩
  rcases p with ⟨a', b', c', d'⟩
  cases h1 <;> cases h2 <;> cases h3 <;> cases h4 <;> rfl

-- Quat 分量展开(实例的匿名实现,rfl 级别)
@[simp] theorem Quat.add_re (q p : Quat) : (q + p).re = q.re + p.re := rfl
@[simp] theorem Quat.add_qi (q p : Quat) : (q + p).qi = q.qi + p.qi := rfl
@[simp] theorem Quat.add_qj (q p : Quat) : (q + p).qj = q.qj + p.qj := rfl
@[simp] theorem Quat.add_qk (q p : Quat) : (q + p).qk = q.qk + p.qk := rfl
@[simp] theorem Quat.neg_re (q : Quat) : (-q).re = -q.re := rfl
@[simp] theorem Quat.neg_qi (q : Quat) : (-q).qi = -q.qi := rfl
@[simp] theorem Quat.neg_qj (q : Quat) : (-q).qj = -q.qj := rfl
@[simp] theorem Quat.neg_qk (q : Quat) : (-q).qk = -q.qk := rfl
@[simp] theorem Quat.mul_re (q p : Quat) :
    (q * p).re = q.re * p.re - q.qi * p.qi - q.qj * p.qj - q.qk * p.qk := rfl
@[simp] theorem Quat.mul_qi (q p : Quat) :
    (q * p).qi = q.re * p.qi + q.qi * p.re + q.qj * p.qk - q.qk * p.qj := rfl
@[simp] theorem Quat.mul_qj (q p : Quat) :
    (q * p).qj = q.re * p.qj - q.qi * p.qk + q.qj * p.re + q.qk * p.qi := rfl
@[simp] theorem Quat.mul_qk (q p : Quat) :
    (q * p).qk = q.re * p.qk + q.qi * p.qj - q.qj * p.qi + q.qk * p.re := rfl
@[simp] theorem Quat.ofNat0_re : (0 : Quat).re = 0 := rfl
@[simp] theorem Quat.ofNat0_qi : (0 : Quat).qi = 0 := rfl
@[simp] theorem Quat.ofNat0_qj : (0 : Quat).qj = 0 := rfl
@[simp] theorem Quat.ofNat0_qk : (0 : Quat).qk = 0 := rfl
@[simp] theorem Quat.ofNat1_re : (1 : Quat).re = 1 := rfl
@[simp] theorem Quat.ofNat1_qi : (1 : Quat).qi = 0 := rfl
@[simp] theorem Quat.ofNat1_qj : (1 : Quat).qj = 0 := rfl
@[simp] theorem Quat.ofNat1_qk : (1 : Quat).qk = 0 := rfl

/-- 四元数单位。 -/
def qI : Quat := ⟨0, 1, 0, 0⟩
def qJ : Quat := ⟨0, 0, 1, 0⟩
def qK : Quat := ⟨0, 0, 0, 1⟩

@[simp] theorem qI_re : qI.re = 0 := rfl
@[simp] theorem qI_qi : qI.qi = 1 := rfl
@[simp] theorem qI_qj : qI.qj = 0 := rfl
@[simp] theorem qI_qk : qI.qk = 0 := rfl
@[simp] theorem qJ_re : qJ.re = 0 := rfl
@[simp] theorem qJ_qi : qJ.qi = 0 := rfl
@[simp] theorem qJ_qj : qJ.qj = 1 := rfl
@[simp] theorem qJ_qk : qJ.qk = 0 := rfl
@[simp] theorem qK_re : qK.re = 0 := rfl
@[simp] theorem qK_qi : qK.qi = 0 := rfl
@[simp] theorem qK_qj : qK.qj = 0 := rfl
@[simp] theorem qK_qk : qK.qk = 1 := rfl

-- ---------------------------------------------------------------------------
-- (Q1) i² = j² = k² = -1
-- ---------------------------------------------------------------------------

theorem quat_i_sq : qI * qI = -1 := by
  apply Quat.ext <;> simp <;> omega

theorem quat_j_sq : qJ * qJ = -1 := by
  apply Quat.ext <;> simp <;> omega

theorem quat_k_sq : qK * qK = -1 := by
  apply Quat.ext <;> simp <;> omega

-- ---------------------------------------------------------------------------
-- (Q2) i·j·k = -1(三生成元积)
-- ---------------------------------------------------------------------------

theorem quat_ij_eq_k : qI * qJ = qK := by
  apply Quat.ext <;> simp <;> omega

theorem quat_jk_eq_i : qJ * qK = qI := by
  apply Quat.ext <;> simp <;> omega

theorem quat_ki_eq_j : qK * qI = qJ := by
  apply Quat.ext <;> simp <;> omega

/-- ★ i·j·k = -1:三个单位之积 = -1(Hamilton 关系,含负号)。 -/
theorem quat_ijk_minus_one : (qI * qJ) * qK = -1 := by
  apply Quat.ext <;> simp <;> omega

-- ---------------------------------------------------------------------------
-- (Q3) 非交换:ij = k ≠ -k = ji
-- ---------------------------------------------------------------------------

theorem quat_ji_eq_neg_k : qJ * qI = -qK := by
  apply Quat.ext <;> simp

/-- ★ 非交换性:i·j ≠ j·i(四元数与复数代数结构的本质区别)。 -/
theorem quat_ij_ne_ji : qI * qJ ≠ qJ * qI := by
  intro h
  have hk := congrArg (fun q : Quat => q.qk) h
  change (qI * qJ).qk = (qJ * qI).qk at hk
  have hl : (qI * qJ).qk = 1 := by simp [qI, qJ]
  have hr : (qJ * qI).qk = -1 := by simp [qI, qJ]
  have h10 : (1 : Int) = -1 := by
    calc
      (1 : Int) = (qI * qJ).qk := hl.symm
      _ = (qJ * qI).qk := hk
      _ = -1 := hr
  omega

-- ---------------------------------------------------------------------------
-- 环结构:乘法结合律(四元数是结合环)
-- ---------------------------------------------------------------------------

theorem quat_mul_assoc (q p r : Quat) : (q * p) * r = q * (p * r) := by
  apply Quat.ext <;> simp [Int.mul_add, Int.add_mul, Int.sub_mul, Int.mul_sub, Int.mul_assoc] <;> omega

-- ---------------------------------------------------------------------------
-- 复数嵌入:ℂ 是四元数的子环
-- ---------------------------------------------------------------------------

/-- 复数嵌入四元数:z = a + bi ↦ a + bi + 0j + 0k。 -/
def cToQuat (z : ℂ) : Quat := ⟨z.re, z.im, 0, 0⟩

theorem cToQuat_add (z w : ℂ) : cToQuat (z + w) = cToQuat z + cToQuat w := by
  apply Quat.ext <;> simp [cToQuat] <;> omega

/-- 复数乘法对应四元数乘法:ℂ 是 ℍ 的子环(四元数扩展复数,不丢结构)。 -/
theorem cToQuat_mul (z w : ℂ) : cToQuat (z * w) = cToQuat z * cToQuat w := by
  apply Quat.ext <;> simp [cToQuat] <;> omega

-- ---------------------------------------------------------------------------
-- (Q4) Clifford 表示:Φ(a+bi+cj+dk) = aI + b(iσ₁) + c(iσ₂) + d(iσ₃)
-- ---------------------------------------------------------------------------

/-- ℂ 减法(补 core 缺 Sub 的实例;Mat2 同款处理见 Differential 模块)。 -/
instance : Sub ℂ := ⟨fun z w => z + (-w)⟩

@[simp] theorem ℂ.sub_re (z w : ℂ) : (z - w).re = z.re - w.re := rfl
@[simp] theorem ℂ.sub_im (z w : ℂ) : (z - w).im = z.im - w.im := rfl

/-- 四元数的 Clifford/矩阵表示。
    Φ(i) = iσ₁ = [[0,i],[i,0]], Φ(j) = iσ₂ = [[0,-1],[1,0]], Φ(k) = iσ₃ = [[i,0],[0,-i]]。 -/
def quatToMat (q : Quat) : Mat2 :=
  ⟨ cSmul q.re 1 + cSmul q.qk cI
  , cSmul q.qi cI - cSmul q.qj 1
  , cSmul q.qi cI + cSmul q.qj 1
  , cSmul q.re 1 - cSmul q.qk cI ⟩

theorem quatToMat_add (q p : Quat) : quatToMat (q + p) = quatToMat q + quatToMat p := by
  apply Mat2.ext <;> apply ℂ.ext <;> simp [quatToMat, cSmul] <;> omega

/-- ★ 表示保乘法:Φ(q·p) = Φ(q)·Φ(p)(四元数乘法 = 矩阵乘法)。
    这使四元数代数完全落入 Mat2 = Cℓ(3) 表示中。 -/
theorem quatToMat_mul (q p : Quat) :
    quatToMat (q * p) = matMul (quatToMat q) (quatToMat p) := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [quatToMat, matMul, cSmul, ℂ.mul_re, ℂ.mul_im,
          Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg] <;> omega

/-- 表示下的单位:Φ(i) = iσ₁。 -/
theorem quatToMat_i : quatToMat qI = matMul (scalar2 cI) σ₁ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [quatToMat, qI, cSmul, σ₁, matMul, ℂ.mul_re, ℂ.mul_im] <;> omega

theorem quatToMat_j : quatToMat qJ = matMul (scalar2 cI) σ₂ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [quatToMat, qJ, cSmul, σ₂, matMul, ℂ.mul_re, ℂ.mul_im] <;> omega

theorem quatToMat_k : quatToMat qK = matMul (scalar2 cI) σ₃ := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [quatToMat, qK, cSmul, σ₃, matMul, ℂ.mul_re, ℂ.mul_im] <;> omega

-- ---------------------------------------------------------------------------
-- 生成元关系在表示中的验证(矩阵版 Q1–Q3)
-- ---------------------------------------------------------------------------

/-- (iσ₁)² = -1:四元数 i² = -1 在 Clifford 表示中成立。 -/
theorem iSigma1_sq :
    matMul (matMul (scalar2 cI) σ₁) (matMul (scalar2 cI) σ₁) = -1 := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, matMul, scalar2, ℂ.mul_re, ℂ.mul_im] <;> omega

theorem iSigma2_sq :
    matMul (matMul (scalar2 cI) σ₂) (matMul (scalar2 cI) σ₂) = -1 := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₂, matMul, scalar2, ℂ.mul_re, ℂ.mul_im] <;> omega

theorem iSigma3_sq :
    matMul (matMul (scalar2 cI) σ₃) (matMul (scalar2 cI) σ₃) = -1 := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₃, matMul, scalar2, ℂ.mul_re, ℂ.mul_im] <;> omega

/-- (iσ₁)(iσ₂)(iσ₃) = -1:四元数 ijk = -1 在 Clifford 表示中成立。 -/
theorem iSigmas_ijk :
    matMul (matMul (matMul (scalar2 cI) σ₁) (matMul (scalar2 cI) σ₂)) (matMul (scalar2 cI) σ₃) = -1 := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, scalar2, ℂ.mul_re, ℂ.mul_im] <;> omega

/-- 非交换在表示中的验证:(iσ₁)(iσ₂) ≠ (iσ₂)(iσ₁)。 -/
theorem iSigma1_iSigma2_ne_comm :
    matMul (matMul (scalar2 cI) σ₁) (matMul (scalar2 cI) σ₂) ≠
    matMul (matMul (scalar2 cI) σ₂) (matMul (scalar2 cI) σ₁) := by
  intro h
  have ha := congrArg (fun M : Mat2 => M.a) h
  have him := congrArg (fun z : ℂ => z.im) ha
  have h1 : (1 : Int) = -1 := by
    simpa [σ₁, σ₂, matMul, scalar2, cI] using him
  omega

-- ---------------------------------------------------------------------------
-- (Q5) 纯 Clifford 版本:σ₁σ₂σ₃ 的平方 = -1
-- ---------------------------------------------------------------------------

/-- σ₁σ₂σ₃ = -i·I(三个生成元之积回到标量层)。 -/
theorem sigma123_eq_neg_i :
    matMul σ₁ (matMul σ₂ σ₃) = matMul (scalar2 (-cI)) 1 := by
  unfold scalar2
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.mul_re, ℂ.mul_im] <;> omega

/-- ★ (σ₁σ₂σ₃)² = -1:三个反交换生成元之积的平方 = -1。
    这是四元数 ijk = -1 的纯 Clifford 版本——"隐数单元 a·b·c = -1"的已证实例。 -/
theorem triple_product_square :
    matMul (matMul σ₁ (matMul σ₂ σ₃)) (matMul σ₁ (matMul σ₂ σ₃)) = -1 := by
  apply Mat2.ext <;> apply ℂ.ext <;>
    simp [σ₁, σ₂, σ₃, matMul, ℂ.mul_re, ℂ.mul_im] <;> omega

-- ---------------------------------------------------------------------------
-- 草案:隐数单元(HiddenUnit)与旋转表示
-- ---------------------------------------------------------------------------

/-- 隐数单元草案(用户任务 Q4 猜想):隐数空间中是否存在满足
    a² = -1 且 a·b·c = -1 的特殊单元?
    ★ 答案(本模块 Q1–Q3 已证):存在——四元数单位 {i, j, k} 与
    Clifford 表示 {iσ₁, iσ₂, iσ₃} 都是实例。
    这类单元不是新公理,而是反交换生成元的必然表示。 -/
structure HiddenUnit (R : Type) (mul : R → R → R) [Neg R] [OfNat R 1] where
  a : R
  b : R
  c : R
  a_sq_minus_one : mul a a = -1
  abc_minus_one : mul (mul a b) c = -1
  ab_ne_ba : mul a b ≠ mul b a

/-- HiddenUnit 实例化(四元数环):{i, j, k}(Q1/Q2/Q3 已证)。 -/
def quatHiddenUnit : HiddenUnit Quat (fun q p => q * p) :=
  { a := qI
  , b := qJ
  , c := qK
  , a_sq_minus_one := quat_i_sq
  , abc_minus_one := quat_ijk_minus_one
  , ab_ne_ba := quat_ij_ne_ji }

/-- HiddenUnit 实例化(矩阵表示):{iσ₁, iσ₂, iσ₃}。
    i² = -1 从反交换涌现(C3 的推广),不用任何新公理。 -/
def cliffordHiddenUnit : HiddenUnit Mat2 matMul :=
  { a := matMul (scalar2 cI) σ₁
  , b := matMul (scalar2 cI) σ₂
  , c := matMul (scalar2 cI) σ₃
  , a_sq_minus_one := iSigma1_sq
  , abc_minus_one := iSigmas_ijk
  , ab_ne_ba := iSigma1_iSigma2_ne_comm }

/-- 旋转表示草案:单位四元数共轭作用 v ↦ q·v·q⁻¹ 生成 3D 旋转。
    需要范数 |q|² = 1 与逆元(ℤ 系数无逆元,同 D7' 卡点——
    实例化需升级系数环到 ℚ[i]/ℝ)。开放目标,不强证。 -/
structure QuatRotation where
  unit : Quat
  unit_norm : unit.re * unit.re + unit.qi * unit.qi + unit.qj * unit.qj + unit.qk * unit.qk = 1
  -- act : V → V 保范/保角/行列式 1:开放目标(需域系数 + 3D 几何)

end ProjectionPhysics
