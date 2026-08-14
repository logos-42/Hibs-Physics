-- ProjectionPhysics — Kernel Algebra
--
-- Module 2: Kernel.lean
--   核空间的可证明代数性质。这里的每个定理都是真正被 Lean 证明的，
--   它们构成 Representation Completeness 与 Kernel Null Theorem 的代数地基：
--
--   (K1) 核在加法下封闭          —— 核是子空间
--   (K2) 核包含零                —— 核非空
--   (K3) 可观测只依赖 Image 分量  —— "Kernel 不可观测"（完备性的核心）
--   (K4) 非平凡核 ⟹ 存在内部自由度 —— Kernel Null 论证链第一步
--   (K5) 单射嵌入 ⟹ 存在左逆投影  —— 投影的存在性来自嵌入的单射性

import ProjectionPhysics.Archive.Definitions

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- (K1) 核在加法下封闭
-- ---------------------------------------------------------------------------

theorem kernel_add_closed {S V : Type} [Add S] [Add V] [Zero V]
    (π : S → V) (hadd : ∀ a b : S, π (a + b) = π a + π b)
    (hzero : ∀ v : V, 0 + v = v)
    {a b : S} (ha : π a = 0) (hb : π b = 0) :
    π (a + b) = 0 := by
  rw [hadd, ha, hb]
  exact hzero 0

-- ---------------------------------------------------------------------------
-- (K2) 核包含零
-- ---------------------------------------------------------------------------

theorem kernel_contains_zero {S V : Type} [Zero S] [Zero V]
    (π : S → V) (h0 : π (0 : S) = 0) :
    π (0 : S) = 0 := h0

-- ---------------------------------------------------------------------------
-- (K3) 可观测只依赖 Image 分量 ★
--      "Kernel 不可观测"：往态里加任意核元素，观测值不变。
-- ---------------------------------------------------------------------------

theorem observables_depend_only_on_image {S V : Type} [Add S] [Add V] [Zero V]
    (π : S → V) (hadd : ∀ a b : S, π (a + b) = π a + π b)
    (hzero : ∀ v : V, v + 0 = v)
    (s_im s_ker : S) (hker : π s_ker = 0) :
    π (s_im + s_ker) = π s_im := by
  rw [hadd, hker]
  exact hzero (π s_im)

-- ---------------------------------------------------------------------------
-- (K4) 非平凡核 ⟹ 存在内部自由度
--      Kernel 不是垃圾桶：核里至少有两个不同的元素，
--      即系统拥有观测不到的内部结构。
-- ---------------------------------------------------------------------------

theorem nontrivial_kernel_gives_internal_degree {S V : Type} [Zero S] [Zero V]
    (π : S → V) (h0 : π (0 : S) = 0)
    (hnontriv : ∃ s : S, s ≠ 0 ∧ π s = 0) :
    ∃ a b : S, π a = 0 ∧ π b = 0 ∧ a ≠ b := by
  rcases hnontriv with ⟨s, hs_ne, hs_ker⟩
  refine ⟨s, (0 : S), hs_ker, h0, ?_⟩
  simpa using hs_ne

-- ---------------------------------------------------------------------------
-- (K5) 单射嵌入 ⟹ 存在左逆投影 ★
--      投影的存在性从嵌入的单射性推出（HIBS 定理 6.5 的一般化）。
-- ---------------------------------------------------------------------------

theorem left_inverse_of_injective {S V : Type} [Nonempty S]
    (ι : S → V) (hι : Function.Injective ι) :
    ∃ π : V → S, ∀ s : S, π (ι s) = s := by
  classical
  let π : V → S := fun v =>
    if h : ∃ s : S, ι s = v then Classical.choose h else Classical.choice (inferInstance : Nonempty S)
  refine ⟨π, ?_⟩
  intro s
  have hπ : ∃ s' : S, ι s' = ι s := ⟨s, rfl⟩
  simp [π, hπ]
  apply hι
  exact Classical.choose_spec hπ

-- ---------------------------------------------------------------------------
-- (K6) 投影-嵌入对 ⟹ 嵌入单射
-- ---------------------------------------------------------------------------

theorem pair_embed_injective {A S : Type} (P : ProjectionPair A S) :
    Function.Injective P.embed := by
  intro a₁ a₂ h
  have h₁ : P.proj (P.embed a₁) = P.proj (P.embed a₂) := congrArg P.proj h
  simpa [P.left_inverse] using h₁

end ProjectionPhysics
