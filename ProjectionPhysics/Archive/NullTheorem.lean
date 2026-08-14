-- ProjectionPhysics — Kernel Null Theorem
--
-- Module 5: NullTheorem.lean
--   Kernel Null Theorem 的草案与可证明的代数核心。
--
--   论证链（gemini 对话 6 轮修正版）：
--     核容量 C_κ → 0
--       ⇒ 投影完全进入 Image，不存在内部自由度
--       ⇒ 系统没有承载"静止"的代数空间
--       ⇒ 唯一允许的路径是 Q(p) = 0（零测地线）
--       ⇒ "以光速传播"成为推论而非假设
--
--   可证明（★）：核平凡 ⟹ 无内部自由度、核质量为零。
--   草案：完整 Kernel Null Theorem（C_κ → 0 ⇒ p 在零锥上）。

import ProjectionPhysics.Archive.Definitions
import ProjectionPhysics.Archive.Kernel
import ProjectionPhysics.Archive.Mass

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- 无内部自由度
-- ---------------------------------------------------------------------------

/-- 无内部自由度：核平凡（唯一的核元素是 0）。
    "投影完全进入 Image"的代数表述。 -/
def NoInternalDegree {S V : Type} [Zero S] [Zero V] (π : S → V) : Prop :=
  ∀ s : S, π s = 0 → s = 0

-- ---------------------------------------------------------------------------
-- ★ 可证明：核平凡 ⟺ 无内部自由度
-- ---------------------------------------------------------------------------

theorem trivial_kernel_iff_no_internal_degree {S V : Type} [Zero S] [Zero V]
    (π : S → V) :
    NoInternalDegree π ↔ ∀ s : S, π s = 0 → s = 0 := by
  rfl

-- ---------------------------------------------------------------------------
-- ★ 可证明：核平凡 ⟹ 核质量为零
--      （从 Kernel.lean / Mass.lean 的组合）
-- ---------------------------------------------------------------------------

theorem no_internal_degree_implies_no_kernel_mass {S V : Type} [Zero S] [Zero V]
    (π : S → V) (h0 : π (0 : S) = 0)
    (hno : NoInternalDegree π)
    (κ : KernelOf π → Int) (hκ0 : κ ⟨0, h0⟩ = 0) :
    ∀ ζ_κ : KernelOf π, κ ζ_κ = 0 :=
  kernel_mass_zero_on_trivial_kernel π h0 hno κ hκ0

-- ---------------------------------------------------------------------------
-- ★ 可证明：态在核上的分量
-- ---------------------------------------------------------------------------

/-- 若态 s 完全在核中（π s = 0），且核平凡，则 s = 0。
    "完全进入 Image 之外无物存在"。 -/
theorem fully_in_kernel_of_trivial {S V : Type} [Zero S] [Zero V]
    (π : S → V) (hno : NoInternalDegree π) :
    ∀ s : S, π s = 0 → s = 0 := hno

-- ---------------------------------------------------------------------------
-- 草案：Kernel Null Theorem
-- ---------------------------------------------------------------------------

/-- Kernel Null Theorem（草案声明）。
    当核容量归零（C_κ → 0，即投影完全进入 Image）时，
    投影后的动量 p 必须落在零锥上：Q(p) = 0。

    注意（诚实声明）：本结构把"核平凡 ⟹ 无核质量"（已证明）与
    "无核质量 ⟹ 零测地线"（需要动量 Q 的定义与色散关系的推导，
    即 Metric Representation 完成后的工作）分开陈述。
    后者是开放研究目标，不是已证定理。 -/
structure KernelNullTheorem (S V : Type) [Zero S] [Zero V] [Add V]
    (π : S → V) (Q : V → Int) where
  -- 核容量归零：核平凡（已证部分见 NoInternalDegree）
  kernel_capacity_zero : NoInternalDegree π
  -- 动量：Flow 的投影（草案：p(s) 的定义依赖 Flow Representation）
  -- 结论：动量在零锥上（草案声明，待 Metric Representation 后证明）
  null_cone : ∀ (p : V), (∃ s : S, π s = p) → OnNullCone Q p

/-- 草案的平凡实例：若 Q 恒为零函数，则 KernelNullTheorem 的结论平凡成立。 -/
def trivialKernelNull {S V : Type} [Zero S] [Zero V] [Add V]
    (π : S → V) (hno : NoInternalDegree π) :
    KernelNullTheorem S V π (fun _ => 0) where
  kernel_capacity_zero := hno
  null_cone := by
    intro p h
    rfl

end ProjectionPhysics
