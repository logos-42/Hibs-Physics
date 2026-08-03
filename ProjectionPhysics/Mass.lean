-- ProjectionPhysics — Kernel Mass
--
-- Module 4: Mass.lean
--   Kernel Representation：质量 = 核空间的标量表示（草案 + 可证明核心）。
--
--   可证明（★）：平凡核 ⟹ 核质量项可归一化为零。
--   草案：非平凡核的质量 m = Φ(κ(ker π)) 作为结构陈述。

import ProjectionPhysics.Definitions
import ProjectionPhysics.Kernel

namespace ProjectionPhysics

-- ---------------------------------------------------------------------------
-- 核质量的定义
-- ---------------------------------------------------------------------------

/-- 核质量平方 m² := κ(ζ_κ)，其中 κ 是核空间上的标量不变量。
    注意：质量不能是 Q(π(ζ_κ))（那恒等于 Q(0) = 0），
    而必须是核**内部**结构 κ 的取值 —— 这正是 Kernel Representation
    与"质量不是定义"的核心。 -/
def kernelMassSq {S V : Type} [Zero V] (π : S → V)
    (κ : KernelOf π → Int) (ζ_κ : KernelOf π) : Int :=
  κ ζ_κ

-- ---------------------------------------------------------------------------
-- ★ 平凡核 ⟹ 核质量为零
-- ---------------------------------------------------------------------------

/-- 若核平凡（唯一的核元素是 0），且核不变量在零元素上取 0，
    则所有核元素的核质量为零。这是 Kernel Null Theorem 的代数第一段：
    "无内部自由度 ⟹ 无核质量"。 -/
theorem kernel_mass_zero_on_trivial_kernel {S V : Type} [Zero S] [Zero V]
    (π : S → V) (h0 : π (0 : S) = 0)
    (htriv : ∀ s : S, π s = 0 → s = 0)
    (κ : KernelOf π → Int) (hκ0 : κ ⟨0, h0⟩ = 0) :
    ∀ ζ_κ : KernelOf π, κ ζ_κ = 0 := by
  intro ζ_κ
  have hζ : ζ_κ.val = 0 := htriv ζ_κ.val ζ_κ.property
  have hsub : (⟨ζ_κ.val, ζ_κ.property⟩ : KernelOf π) = ⟨0, h0⟩ := by
    apply Subtype.ext
    exact hζ
  change κ ⟨ζ_κ.val, ζ_κ.property⟩ = 0
  rw [hsub]
  exact hκ0

-- ---------------------------------------------------------------------------
-- 草案：Kernel Representation Theorem
-- ---------------------------------------------------------------------------

/-- 核表示定理（草案声明）。
    核 ker π 不是"垃圾桶"，而是拥有内部代数结构的空间：
    Aut(ker π) 上的标量表示唯一（质量 m = Φ(dim ker π) 或 rank 的
    标量函数），由以下三条件刻画：
      (a) 在 Image 下不可见（π 输出恒 0）
      (b) 在 Aut(ker π) 下不变
      (c) 与投影秩无关
    则它只能依赖 dim(ker π) 或 rank(κ)。证明需要核上的表示论，为开放目标。 -/
structure KernelRepresentation (S V : Type) [Zero S] [Zero V]
    (π : S → V) where
  -- 投影保持零（核包含 0 的前提）
  zero_proj : π (0 : S) = 0
  -- 核的自同构群（抽象类型 + 作用）
  autKernel : Type
  aut_apply : autKernel → KernelOf π → KernelOf π
  -- 核不变量：在核自同构下不变
  κ : KernelOf π → Int
  κ_invariant : ∀ (σ : autKernel) (k : KernelOf π), κ (aut_apply σ k) = κ k
  -- 质量 = 核不变量的标量函数（草案：形式未锁定）
  mass : Int
  mass_from_kernel : mass = κ ⟨0, zero_proj⟩

end ProjectionPhysics
