-- ProjectionPhysics — Representation Completeness
--
-- Module 3: Completeness.lean
--   Representation Completeness Theorem 的代数核心与草案陈述。
--
--   已证明（★）：不变量因子化定理 —— 任何可观测量（在观测等价类上取常值）
--   必然因子化通过投影：I = J ∘ π。这是"Q 来自 Image"的精确代数内容，
--   也是完备性中"没有第三自由度"的骨架。
--
--   草案：完整的 Representation Completeness（I = F(Q, κ)，
--   κ 为核不变量）作为带假设的结构陈述 —— 证明留作研究目标。

import ProjectionPhysics.Definitions
import ProjectionPhysics.Kernel

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- ★ 不变量因子化定理 (Invariant Factorization)
-- ---------------------------------------------------------------------------

/-- 任何"不区分同一观测值的微观态"的可观测量 I，都是投影的函数：
    I(s) = J(π(s))。即：可观测量在核纤维上取常值，当且仅当它通过 π 因子化。 -/
theorem invariant_factor_through_projection {S V : Type} [Nonempty S]
    (π : S → V) (I : S → Int) (hI : IsObservable π I) :
    ∃ J : V → Int, ∀ s : S, I s = J (π s) := by
  classical
  let J : V → Int := fun v =>
    if h : ∃ s : S, π s = v then I (Classical.choose h) else 0
  refine ⟨J, ?_⟩
  intro s
  have hπ : ∃ s' : S, π s' = π s := ⟨s, rfl⟩
  simp [J, hπ]
  exact hI s (Classical.choose hπ) (Classical.choose_spec hπ).symm

/-- 因子化的等价刻画：观测等价不变 ⟺ 通过投影因子化。 -/
theorem invariant_factor_iff {S V : Type} [Nonempty S]
    (π : S → V) (I : S → Int) :
    IsObservable π I ↔ ∃ J : V → Int, ∀ s : S, I s = J (π s) := by
  constructor
  · intro hI
    exact invariant_factor_through_projection π I hI
  · rintro ⟨J, hJ⟩ s₁ s₂ hπ
    rw [hJ, hJ, hπ]

-- ---------------------------------------------------------------------------
-- 推论：核加法不变量的因子化
-- ---------------------------------------------------------------------------

/-- 若 I 保持加法且是观测等价不变的，则 J 也保持加法（J 是 π 的像上的态射）。 -/
theorem factor_preserves_add {S V : Type} [Nonempty S] [Add S] [Add V]
    (π : S → V) (hadd : ∀ a b : S, π (a + b) = π a + π b)
    (I : S → Int) (hI : IsObservable π I)
    (hIadd : ∀ a b : S, I (a + b) = I a + I b) :
    ∃ J : V → Int, (∀ s : S, I s = J (π s)) ∧
      (∀ v w : V, (∃ s₁ s₂ : S, π s₁ = v ∧ π s₂ = w) →
        J (v + w) = J v + J w) := by
  rcases invariant_factor_through_projection π I hI with ⟨J, hJ⟩
  refine ⟨J, hJ, ?_⟩
  intro v w hvw
  rcases hvw with ⟨s₁, s₂, h₁, h₂⟩
  -- J(v + w) = J(π s₁ + π s₂) = J(π(s₁ + s₂)) = I(s₁ + s₂)
  --          = I s₁ + I s₂ = J(π s₁) + J(π s₂) = J v + J w
  rw [← h₁, ← h₂]
  rw [← hadd]
  rw [← hJ (s₁ + s₂)]
  rw [hIadd, hJ s₁, hJ s₂]

-- ---------------------------------------------------------------------------
-- 草案：Representation Completeness Theorem
-- ---------------------------------------------------------------------------

/-- 表示完备性定理（草案声明）。
    设 (S, ⊕, ⊗) 满足 HIBS 公理 A1–A3 的代数结构，π : S → V 为非单射
    信息守恒投影。则任意可观测量 I 可唯一分解为：

        I(s) = F( Q(π(s)), κ(ζ_κ(s)) )

    其中 Q 是像空间上由 π 诱导的二次型（Image 不变量），
    κ 是核空间 ker π 的标量不变量（Kernel 不变量，质量之根）。
    完备性：不存在独立于 {Q, κ} 的第三种自由度。

    本结构中，Q 部分已被 invariant_factor_through_projection 证明；
    κ 部分（核内部表示论）与分解 s ↦ ζ_κ(s) 为开放研究目标，
    此处作为假设字段如实标注。 -/
structure RepresentationCompleteness (S V : Type) [Add S] [Add V] [Zero V]
    [Nonempty S] (π : S → V) where
  -- 投影保持加法（A2 相容）
  hadd : ∀ a b : S, π (a + b) = π a + π b
  -- 投影非单射（A1）：核非平凡
  non_injective : ∃ a b : S, a ≠ b ∧ π a = π b
  -- Q：像空间上的二次型（Image 不变量）
  Q : V → Int
  Q_quadratic : Q 0 = 0
  -- 核分量提取：s ↦ ζ_κ(s)（需要分解 S ≅ im π ⊕ ker π，作为数据给出）
  kernelComponent : S → KernelOf π
  -- κ：核空间的标量不变量（Aut(ker π) 等变，质量之根）
  κ : KernelOf π → Int
  -- 完备性（可证部分，= C1）：任意可观测量因子化通过 π：I = J ∘ π
  -- （"Q 来自 Image"；κ 的独立贡献见范数分解定理，如 completeness_complex）
  complete : ∀ (I : S → Int), IsObservable π I →
    ∃ J : V → Int, ∀ s : S, I s = J (π s)

/-- 完备性定理的"Q 半"（已证明）：可观测量通过投影因子化。 -/
theorem completeness_Q_half {S V : Type} [Add S] [Add V] [Zero V] [Nonempty S]
    (π : S → V) (I : S → Int) (hI : IsObservable π I) :
    ∃ J : V → Int, ∀ s : S, I s = J (π s) :=
  invariant_factor_through_projection π I hI

end ProjectionPhysics
