-- ProjectionPhysics — Hidden Projection Algebra
--
-- Module 14: ProjectionAlgebra.lean
--
-- 隐数路线的核心修正(2026-08-06 leo 方向纠正):
--   隐数 ≠ 复数的另一种写法;隐数的第一性不是 i²=-1,而是投影幂等 P² = P。
--   路线:Hidden Space → Projection Algebra → State Space → Geometry。
--   四元数/旋转降级为"比较对象"(空间已有时的变换机制,见 Quaternion.lean)。
--
-- 本模块证明(投影代数 → 变换半群):
--
--   (PA1) 投影定义 IsProjection(幂等自映射);★ 交换投影的复合仍是投影
--   (PA2) 互补投影对 ComplementaryProjection(幂等/正交/完备)
--         ★ ℂ 实例 {Π_re, Π_im}:实部投影与虚部投影
--         幂等(PA2a) + 正交(PA2b) + 完备(PA2c) + 线性(PA2d)
--   (PA3) ★ 复合表:5 个复合全部确定(P_re, P_im, 0 构成半群)
--   (PA4) 核/像:ker Π_im = 实轴,im Π_re = 实轴(可观测层/不可观测层)
--   (PA5) ★ 半群而非群:Π_re 非单射(0 与 cI 同像)——投影不可逆,群需要可逆层
--   (PA6) ★ 量子测量骨架:投影值分解 {Π_re, Π_im} 满足幂等+正交+完备
--         (PVM 的代数骨架,无概率公理)
--
-- 只使用 core Lean 4(无 mathlib),全部定理已证(零未完成项)。

import ProjectionPhysics.HiddenSpace

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- (PA1) 投影:幂等自映射;交换投影的复合是投影
-- ---------------------------------------------------------------------------

/-- 投影:幂等自映射 P(P x) = P x(一次观测后不再改变)。 -/
def IsProjection {V : Type} (P : V → V) : Prop :=
  ∀ x : V, P (P x) = P x

/-- ★ 交换投影的复合仍是投影:若 P、Q 幂等且 PQ = QP,则 PQ 幂等。
    这是投影复合成为变换的代数前提(正交投影族自动满足交换条件)。 -/
theorem comp_of_commuting_projections_is_projection {V : Type} (P Q : V → V)
    (hP : IsProjection P) (hQ : IsProjection Q) (hcomm : ∀ x : V, P (Q x) = Q (P x)) :
    IsProjection (fun x : V => P (Q x)) := by
  intro x
  dsimp
  have hswap : Q (P (Q x)) = P (Q (Q x)) := (hcomm (Q x)).symm
  rw [hswap]
  rw [hQ x]
  rw [hP (Q x)]

-- ---------------------------------------------------------------------------
-- (PA2) 互补投影对:幂等 + 正交 + 完备
-- ---------------------------------------------------------------------------

/-- 互补投影对:P 与 Q 满足
    (1) 幂等:P² = P, Q² = Q
    (2) 正交:P∘Q = 0 = Q∘P(不同方向互不可见)
    (3) 完备:P + Q = id(信息不丢失,无第三自由度)
    这是"状态生成机制"的代数公理:任何元素分解为两个互补观测方向。 -/
structure ComplementaryProjection (V : Type) [Add V] [Zero V] where
  P : V → V
  Q : V → V
  idemP : ∀ x : V, P (P x) = P x
  idemQ : ∀ x : V, Q (Q x) = Q x
  ortho : ∀ x : V, P (Q x) = 0 ∧ Q (P x) = 0
  complete : ∀ x : V, P x + Q x = x

/-- 虚部投影 Π_im : ℂ → ℂ,投影到虚轴(与 H4 的 Π_re = ι∘Re 互补)。 -/
def hiddenImProj (z : ℂ) : ℂ := ⟨0, z.im⟩

theorem hiddenImProj_re : (hiddenImProj z).re = 0 := rfl

theorem hiddenImProj_im : (hiddenImProj z).im = z.im := rfl

-- (PA2a) 幂等

theorem hiddenImProj_idempotent (z : ℂ) : hiddenImProj (hiddenImProj z) = hiddenImProj z := by
  apply ℂ.ext <;> simp [hiddenImProj]

-- (PA2b) 正交

theorem hiddenReProj_comp_im_zero (z : ℂ) : hiddenReProj (hiddenImProj z) = 0 := by
  apply ℂ.ext <;> simp [hiddenReProj, hiddenImProj, realEmbed, reProj]

theorem hiddenImProj_comp_re_zero (z : ℂ) : hiddenImProj (hiddenReProj z) = 0 := by
  apply ℂ.ext <;> simp [hiddenReProj, hiddenImProj, realEmbed, reProj]

-- (PA2c) 完备

/-- ★ 完备性:Π_re z + Π_im z = z。任何元素 = 实部观测 + 虚部核分量,无第三自由度。 -/
theorem hiddenProj_complete (z : ℂ) : hiddenReProj z + hiddenImProj z = z := by
  apply ℂ.ext <;> simp [hiddenReProj, hiddenImProj, realEmbed, reProj] <;> omega

-- (PA2d) 线性

theorem hiddenImProj_linear : LinearMap cVecSpace cVecSpace hiddenImProj := by
  constructor
  · intro x y
    apply ℂ.ext <;> simp [hiddenImProj]
  · intro a x
    apply ℂ.ext <;> simp [hiddenImProj, cSmul, cVecSpace]

/-- ★ 互补投影对实例:{Π_re, Π_im}(实部/虚部观测分解,全部字段已证)。 -/
def realImagProjection : ComplementaryProjection ℂ :=
  { P := hiddenReProj
  , Q := hiddenImProj
  , idemP := hiddenReProj_idempotent
  , idemQ := hiddenImProj_idempotent
  , ortho := by
      intro z
      constructor
      · exact hiddenReProj_comp_im_zero z
      · exact hiddenImProj_comp_re_zero z
  , complete := hiddenProj_complete }

-- ---------------------------------------------------------------------------
-- (PA3) ★ 复合表:变换集合 {Π_re, Π_im, 0} 构成半群
-- ---------------------------------------------------------------------------

/-- 复合表 1:Π_re ∘ Π_re = Π_re(幂等,即 H4)。 -/
theorem comp_table_re_re (z : ℂ) : hiddenReProj (hiddenReProj z) = hiddenReProj z :=
  hiddenReProj_idempotent z

/-- 复合表 2:Π_im ∘ Π_im = Π_im(幂等)。 -/
theorem comp_table_im_im (z : ℂ) : hiddenImProj (hiddenImProj z) = hiddenImProj z :=
  hiddenImProj_idempotent z

/-- 复合表 3:Π_re ∘ Π_im = 0(正交:实部观测看不到虚部)。 -/
theorem comp_table_re_im (z : ℂ) : hiddenReProj (hiddenImProj z) = 0 :=
  hiddenReProj_comp_im_zero z

/-- 复合表 4:Π_im ∘ Π_re = 0(正交:虚部观测看不到实部)。 -/
theorem comp_table_im_re (z : ℂ) : hiddenImProj (hiddenReProj z) = 0 :=
  hiddenImProj_comp_re_zero z

/-- 复合表 5:零变换是吸收元(与任何投影复合得零)。 -/
theorem comp_table_zero_absorbs (z : ℂ) :
    hiddenReProj 0 = 0 ∧ hiddenImProj 0 = 0 ∧
    (fun _ : ℂ => 0) (hiddenReProj z) = 0 ∧
    (fun _ : ℂ => 0) (hiddenImProj z) = 0 := by
  constructor
  · apply ℂ.ext <;> simp [hiddenReProj, realEmbed, reProj]
  · constructor
    · apply ℂ.ext <;> simp [hiddenImProj]
    · constructor <;> rfl

/-- ★ 半群乘法表汇总:{Π_re, Π_im, 0} 在复合下封闭,表为
    re∘re=re  im∘im=im  re∘im=0  im∘re=0  0∘任何=0。
    封闭性 = 状态生成机制的可迭代性:变换复合仍是变换。 -/
theorem projection_composition_semigroup (z : ℂ) :
    hiddenReProj (hiddenReProj z) = hiddenReProj z ∧
    hiddenImProj (hiddenImProj z) = hiddenImProj z ∧
    hiddenReProj (hiddenImProj z) = 0 ∧
    hiddenImProj (hiddenReProj z) = 0 := by
  constructor
  · exact comp_table_re_re z
  · constructor
    · exact comp_table_im_im z
    · constructor
      · exact comp_table_re_im z
      · exact comp_table_im_re z

-- ---------------------------------------------------------------------------
-- (PA4) 核/像:可观测层与不可观测层
-- ---------------------------------------------------------------------------

/-- ker Π_im = 实轴:Π_im z = 0 ⟺ z 是实数(无虚部)。 -/
theorem hiddenImProj_kernel_iff (z : ℂ) : hiddenImProj z = 0 ↔ z.im = 0 := by
  constructor
  · intro h
    have him := congrArg (fun w : ℂ => w.im) h
    simp [hiddenImProj] at him
    exact him
  · intro hzi
    apply ℂ.ext <;> simp [hiddenImProj, hzi]

/-- im Π_re = 实轴:可观测层 = 实数(Π_re 的像恰是实轴)。 -/
theorem hproj_re_image (v : ℂ) : (∃ w : ℂ, hiddenReProj w = v) ↔ v.im = 0 := by
  constructor
  · intro h
    rcases h with ⟨w, hw⟩
    have him := congrArg (fun z : ℂ => z.im) hw
    simp [hiddenReProj, realEmbed, reProj] at him
    exact him.symm
  · intro hvi
    refine ⟨v, ?_⟩
    apply ℂ.ext <;> simp [hiddenReProj, realEmbed, reProj, hvi]

-- ---------------------------------------------------------------------------
-- (PA5) ★ 半群而非群:投影不可逆
-- ---------------------------------------------------------------------------

/-- ★ 投影代数生成的是半群,不是群:Π_re 非单射
    (0 与 cI 有相同观测 0——核分量对观测不可见,故投影不可逆)。 -/
theorem hproj_re_not_injective : ¬ Function.Injective hiddenReProj := by
  intro h
  have h0 : hiddenReProj (0 : ℂ) = 0 := by apply ℂ.ext <;> simp [hiddenReProj, realEmbed, reProj]
  have hc : hiddenReProj cI = 0 := by apply ℂ.ext <;> simp [hiddenReProj, realEmbed, reProj]
  have heq : hiddenReProj (0 : ℂ) = hiddenReProj cI := by rw [h0, hc]
  have h01 : (0 : ℂ) = cI := h heq
  have him := congrArg (fun z : ℂ => z.im) h01
  simp at him

/-- 推论:非平凡投影(核非零)不能是双射——状态生成有损,信息在核方向丢失。
    这是"投影产生状态"的代价:确定性来自信息损失(K3 的推论)。 -/
theorem hproj_re_not_bijective :
    ¬ (Function.Injective hiddenReProj ∧ Function.Surjective hiddenReProj) := by
  intro h
  exact hproj_re_not_injective h.1

-- ---------------------------------------------------------------------------
-- (PA6) ★ 量子测量骨架:投影值分解(PVM 的代数骨架)
-- ---------------------------------------------------------------------------

/-- ★ 投影值分解:互补投影对 {Π_re, Π_im} 对应测量基 {1, i} 的两个结果。
    幂等(PA2a) + 正交(PA2b) + 完备(PA2c) 正是投影值测度的代数骨架;
    无概率公理——Born 规则不在此框架内。 -/
theorem pvm_skeleton (z : ℂ) :
    hiddenReProj (hiddenReProj z) = hiddenReProj z ∧
    hiddenImProj (hiddenImProj z) = hiddenImProj z ∧
    hiddenReProj (hiddenImProj z) = 0 ∧
    hiddenImProj (hiddenReProj z) = 0 ∧
    hiddenReProj z + hiddenImProj z = z := by
  constructor
  · exact comp_table_re_re z
  · constructor
    · exact comp_table_im_im z
    · constructor
      · exact comp_table_re_im z
      · constructor
        · exact comp_table_im_re z
        · exact hiddenProj_complete z

-- ---------------------------------------------------------------------------
-- (PA7) ★ 核质量泄露:核乘法不封闭(核是加法子空间,但不是乘法理想)
-- ---------------------------------------------------------------------------

/-- cI² = -1:虚轴(核)元素的平方落在实轴(像)——泄漏的代数事实。 -/
theorem cI_sq_neg_one : cI * cI = -1 := by
  apply ℂ.ext <;> simp

/-- 核质量泄漏量:核元平方的观测值(核结构对像空间的泄漏)。 -/
def kernelLeak (k : KernelOf reProj) : Int := reProj (k.val * k.val)

/-- 泄漏量实例:κ(i·i) = Re(i²) = -1(非零,核向像泄漏)。 -/
theorem kernelLeak_i : kernelLeak ⟨cI, by simp [reProj]⟩ = -1 := by
  simp [kernelLeak, cI_sq_neg_one, reProj]

/-- ★ 核质量泄露:存在核元素,其平方的观测非零。
    核是加法子空间(K1),但乘法不封闭——核非理想,
    "Goldstone 被吃掉"的代数原型(SB 文档 i⊗i = -1 ∈ ℝ)。 -/
theorem kernel_mul_leaks_to_image :
    ∃ k : KernelOf reProj, reProj (k.val * k.val) ≠ 0 := by
  refine ⟨⟨cI, by simp [reProj]⟩, ?_⟩
  rw [cI_sq_neg_one]
  simp [reProj]

/-- 双核元版本:两个核元素的乘积泄漏到像。 -/
theorem kernel_pair_mul_leaks :
    ∃ k₁ k₂ : KernelOf reProj, reProj (k₁.val * k₂.val) ≠ 0 := by
  refine ⟨⟨cI, by simp [reProj]⟩, ⟨cI, by simp [reProj]⟩, ?_⟩
  rw [cI_sq_neg_one]
  simp [reProj]

/-- 泄漏产物是可观测的:-1 ∈ im reProj(泄漏不是丢失,是流向可观测层)。 -/
theorem leak_product_in_image :
    ∃ k : KernelOf reProj, ∃ v : Int, reProj (k.val * k.val) = v ∧ v ≠ 0 := by
  refine ⟨⟨cI, by simp [reProj]⟩, -1, ?_⟩
  constructor
  · rw [cI_sq_neg_one]
    simp [reProj]
  · omega

end ProjectionPhysics
