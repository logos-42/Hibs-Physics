-- ProjectionPhysics — Foundational Definitions
--
-- 工程草案：从 HIBS 三公理出发的"代数涌现物理学"
-- (gemini 对话系列整理：Representation Completeness / Kernel Null / 五座桥梁)
--
-- Module 1: Definitions.lean
--   投影 π : S → V、核 ker π、像 im π、信息守恒（等变）、不变量、
--   二次型/双线性形式、零锥条件、投影-嵌入对。
--
-- 只使用 core Lean 4（无 mathlib），Int 为值类型。

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- 投影的核 (Kernel) 与像 (Image)
-- ---------------------------------------------------------------------------

/-- 核空间 ker π := { s : S // π s = 0 }。核元素对观测完全不可见。 -/
def KernelOf {S V : Type} [Zero V] (π : S → V) : Type :=
  { s : S // π s = 0 }

/-- 像空间 im π := { v : V // ∃ s, π s = v }。可观测值的集合。 -/
def ImageOf {S V : Type} (π : S → V) : Type :=
  { v : V // ∃ s : S, π s = v }

-- ---------------------------------------------------------------------------
-- 信息守恒与不变量
-- ---------------------------------------------------------------------------

/-- 信息守恒（Aut 等变）：π(σ_S(s)) = σ_V(π(s))。
    投影不抹去代数对称性，而是把它同构地搬到目标空间。 -/
def InfoPreserving {S V : Type} (π : S → V) (σS : S → S) (σV : V → V) : Prop :=
  ∀ s : S, π (σS s) = σV (π s)

/-- 不变量：I 在变换 σ 下不变（∀ s, I(σ s) = I s）。 -/
def InvariantUnder {S : Type} (I : S → Int) (σ : S → S) : Prop :=
  ∀ s : S, I (σ s) = I s

/-- 观测等价（同一纤维）：两个微观态给出同一观测值。 -/
def ObservationallyEquivalent {S V : Type} (π : S → V) (s₁ s₂ : S) : Prop :=
  π s₁ = π s₂

/-- 可观测量：在观测等价类上取常值的量（不区分同一观测值的微观态）。 -/
def IsObservable {S V : Type} (π : S → V) (I : S → Int) : Prop :=
  ∀ s₁ s₂ : S, π s₁ = π s₂ → I s₁ = I s₂

-- ---------------------------------------------------------------------------
-- 二次型与双线性形式（Metric Representation 的基础）
-- ---------------------------------------------------------------------------

/-- 双线性形式 B : V → V → Int。 -/
abbrev BilinearForm (V : Type) : Type := V → V → Int

/-- 由双线性形式诱导的二次型 Q(v) := B(v, v)。 -/
def quadOfBilinear {V : Type} (B : BilinearForm V) : V → Int :=
  fun v => B v v

/-- 零锥（光锥）条件：Q(p) = 0。Kernel Null Theorem 的结论形态。 -/
def OnNullCone {V : Type} (Q : V → Int) (p : V) : Prop :=
  Q p = 0

-- ---------------------------------------------------------------------------
-- 投影-嵌入对（HIBS 定理 6.5 与粗粒化投影的共同结构）
-- ---------------------------------------------------------------------------

/-- 投影-嵌入对：ι : A → S 单射嵌入，π : S → A 左逆，π ∘ ι = id。 -/
structure ProjectionPair (A S : Type) where
  embed : A → S
  proj  : S → A
  left_inverse : ∀ a : A, proj (embed a) = a

end ProjectionPhysics
