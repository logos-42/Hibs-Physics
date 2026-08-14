-- ProjectionPhysics — Hidden Space: state-less vectors and state generation
--
-- Module 12: HiddenSpace.lean
--
-- 形式化"无状态万向向量"(任务 Phase 2):
--
--   (H1) HiddenVector:载体源 + Option 状态标签
--        none    = 无状态(方向未定,万向)
--        some v  = 已投影,状态 v(方向已定)
--   (H2) 投影产生状态:∀ s : S, 无状态源经投影获得状态表示(状态 = 观测值)
--   (H3) 状态真实性:标签 Some v ⟹ π(source) = v(标签是事实,不是装饰)
--   (H4) 不同投影 ⟹ 不同状态:Re 与 Im 在 cI 上区分(π₁ s ≠ π₂ s ⟹ 状态不同)
--   (H5) 幂等投影 Π = ι∘Re : ℂ → ℂ(观测后再观测不变;投影是"塌缩"而非"过程")
--   (H6) 方向涌现:z = Re(z)·1 + Im(z)·i(可观测方向 + 核方向,复述 L7 正交分解)
--
-- 本模块只使用 core Lean 4(无 mathlib),全部定理已证(零未完成项)。

import ProjectionPhysics.Archive.LinearAlgebra

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- (H1) 隐向量:无状态向量的形式化
-- ---------------------------------------------------------------------------

/-- 隐向量:载体源 + 状态标签。
    state = none   ⟹ 无状态(方向未定,万向)
    state = some v ⟹ 已投影,状态 v(方向已定)
    consistency 字段保证标签真实:若标 Some v,则 π(source) = v。 -/
structure HiddenVector (S V : Type) (π : S → V) where
  source : S
  observed : Option V
  consistency : ∀ v : V, observed = some v → π source = v

/-- 无状态隐向量:任何源元素都处于无状态形态。 -/
def hvUnprojected {S V : Type} (π : S → V) (s : S) : HiddenVector S V π :=
  ⟨s, none, by intro v h; cases h⟩

/-- 投影后的隐向量:源元素经投影获得状态。 -/
def hvProjected {S V : Type} (π : S → V) (s : S) : HiddenVector S V π :=
  ⟨s, some (π s), by intro v hv; cases hv; rfl⟩

-- ---------------------------------------------------------------------------
-- (H2) 投影产生状态
-- ---------------------------------------------------------------------------

/-- ★ 投影产生状态:无状态源经投影获得状态表示,且状态 = 观测值 π(s)。 -/
theorem projection_generates_state {S V : Type} (π : S → V) (s : S) :
    (hvProjected π s).observed = some (π s) :=
  rfl

/-- 状态生成的存在形式:每个源元素都存在一个有状态表示。 -/
theorem state_generation {S V : Type} (π : S → V) (s : S) :
    ∃ hv : HiddenVector S V π, hv.observed = some (π s) := by
  refine ⟨hvProjected π s, rfl⟩

/-- 无状态形态存在:每个源元素也都可以保持无状态(方向未定)。 -/
theorem stateless_form_exists {S V : Type} (π : S → V) (s : S) :
    ∃ hv : HiddenVector S V π, hv.observed = none := by
  refine ⟨hvUnprojected π s, rfl⟩

-- ---------------------------------------------------------------------------
-- (H3) 状态真实性
-- ---------------------------------------------------------------------------

/-- 标签即事实:observed = some v ⟹ π(source) = v。 -/
theorem state_consistency {S V : Type} (π : S → V) (hv : HiddenVector S V π) :
    ∀ v : V, hv.observed = some v → π hv.source = v :=
  hv.consistency

/-- 已投影向量的源与标签一致:π(source of hvProjected) = 标签值。 -/
theorem projected_consistent {S V : Type} (π : S → V) (s : S) :
    π (hvProjected π s).source = π s :=
  rfl

-- ---------------------------------------------------------------------------
-- (H4) 不同投影 ⟹ 不同状态
-- ---------------------------------------------------------------------------

/-- ★ 不同投影产生不同状态:若 π₁ 与 π₂ 在某源元素上给出不同观测,
    则对应的状态表示必然不同(状态由投影决定,不是源元素的内在属性)。 -/
theorem distinct_projections_distinct_states {S V : Type} (π₁ π₂ : S → V) (s : S)
    (hdiff : π₁ s ≠ π₂ s) :
    (hvProjected π₁ s).observed ≠ (hvProjected π₂ s).observed := by
  intro h
  have h1 : (hvProjected π₁ s).observed = some (π₁ s) := rfl
  have h2 : (hvProjected π₂ s).observed = some (π₂ s) := rfl
  rw [h1, h2] at h
  injection h with hπ
  exact hdiff hπ

/-- 虚部投影 Im : ℂ → Int(与 Re 对偶的第二个投影)。 -/
def imProj (z : ℂ) : Int := z.im

/-- 两个不同的投影:Re 与 Im。cI 在 Re 下为 0,在 Im 下为 1。 -/
theorem re_im_proj_distinguish : ∃ z : ℂ, reProj z ≠ imProj z := by
  refine ⟨cI, ?_⟩
  simp [reProj, imProj]

/-- 同一源元素的两个不同状态:cI 经 Re 投影得 0,经 Im 投影得 1。
    (H4) 的 ℂ 实例化:万向向量 cI 在"实部观测"与"虚部观测"下给出不同状态。 -/
theorem cI_has_two_states :
    (hvProjected reProj cI).observed = some 0 ∧
    (hvProjected imProj cI).observed = some 1 := by
  constructor <;> rfl

-- ---------------------------------------------------------------------------
-- (H5) 幂等投影:Π = ι∘Re(观测后再观测不变)
-- ---------------------------------------------------------------------------

/-- 观测嵌入 ι : Int → ℂ(实轴嵌入)。 -/
def realEmbed (a : Int) : ℂ := ⟨a, 0⟩

/-- 幂等投影 Π : ℂ → ℂ,先取实部再嵌入(投影 = 观测 + 固定方向)。 -/
def hiddenReProj (z : ℂ) : ℂ := realEmbed (reProj z)

theorem hiddenReProj_re : (hiddenReProj z).re = z.re := rfl

theorem hiddenReProj_im : (hiddenReProj z).im = 0 := rfl

/-- ★ 幂等性:P(P(x)) = P(x)。投影是"塌缩":一旦观测,再观测不变。 -/
theorem hiddenReProj_idempotent (z : ℂ) : hiddenReProj (hiddenReProj z) = hiddenReProj z := by
  apply ℂ.ext <;> simp [hiddenReProj, realEmbed, reProj]

theorem hiddenReProj_add (x y : ℂ) :
    hiddenReProj (x + y) = hiddenReProj x + hiddenReProj y := by
  apply ℂ.ext <;> simp [hiddenReProj, realEmbed, reProj]

theorem hiddenReProj_smul (a : Int) (x : ℂ) :
    hiddenReProj (cSmul a x) = cSmul a (hiddenReProj x) := by
  apply ℂ.ext <;> simp [hiddenReProj, realEmbed, cSmul, reProj]

/-- 线性性:P(a·x + b·y) = a·P(x) + b·P(y)(LinearMap 定义)。 -/
theorem hiddenReProj_linear : LinearMap cVecSpace cVecSpace hiddenReProj := by
  constructor
  · exact hiddenReProj_add
  · intro a x
    apply ℂ.ext <;> simp [hiddenReProj, realEmbed, cSmul, cVecSpace, reProj]

/-- 投影不改变已观测值:Re(Π z) = Re z。 -/
theorem hiddenReProj_preserves_observation (z : ℂ) :
    reProj (hiddenReProj z) = reProj z :=
  rfl

/-- 核 = 无状态方向:Π z = 0 ⟺ z.re = 0(核 = 虚轴 = ker(Re))。 -/
theorem hiddenReProj_kernel_iff (z : ℂ) : hiddenReProj z = 0 ↔ z.re = 0 := by
  constructor
  · intro h
    have hre := congrArg (fun w : ℂ => w.re) h
    simp [hiddenReProj, realEmbed] at hre
    exact hre
  · intro hzr
    apply ℂ.ext
    · simpa [hiddenReProj, realEmbed, reProj] using hzr
    · rfl

-- ---------------------------------------------------------------------------
-- (H6) 方向涌现:可观测方向 + 核方向
-- ---------------------------------------------------------------------------

/-- ★ 方向涌现:任何隐向量 z 分解为可观测方向 Re(z)·1(实轴)
    与不可观测核方向 Im(z)·i(虚轴)。"无状态" = 方向在投影前未定;
    投影后方向 = 实轴分量(复述 L7 正交分解,用 imProj 命名)。 -/
theorem direction_emerges_from_projection (z : ℂ) :
    z = cSmul (reProj z) 1 + cSmul (imProj z) cI := by
  simpa [imProj] using cOrthogonalDecomp z

end ProjectionPhysics
