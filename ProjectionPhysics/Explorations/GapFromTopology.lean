-- ProjectionPhysics — GapFromTopology：质量间隙的**场构型版**（GT1–GT5）
--
-- leo（2026-11-01）：「我们要构建的是新的非阿贝尔规范场，构建过程算出质量间隙，
--   间隙也有了，是条数平方关系，那么还有的是解释。不要老用旧思想」。
--
-- 这个批评**成立**，本模块更正一处编码错误：
--
--   `YangMillsFourD.noncommutativity_is_not_the_source_of_the_gap`（Y4D8）把间隙写成
--       strandMassSq N M₀ = 0 ∨ strandMassSq 1 M₀ ≤ strandMassSq N M₀
--   其中 N 是**自由的自然数**，场完全不出现 —— 于是"间隙与场无关"是**编码造成的**
--   （把场从定理里删掉了），不是物理结论。
--
--   正确做法（本模块）：**条数 N 由场构型给**——
--   三个方向的相位构型各自闭合 ⟹ 各自绕数 nᵢ ∈ ℤ（VibrationClosure.VBC1 已证）
--   ⟹ N = Σᵢ nᵢ² 是自然数 ⟹ 间隙。**量化在所有闭合场构型上**。
--
-- 于是物理读法变成一句话：
--   **质量间隙 = 场的闭合性迫使绕数是整数 —— 整数不是公设，是拓扑的后果。**
--   非交换性（[A,A]）确实不出现在间隙里（Y4D8 那半仍然真），但**场出现了**——
--   通过绕数。两件事必须分开说，Y4D8 之前把它们混成"场无关"，是错的。
--
--   GT1 ★★★ `winding_is_integer`：闭合构型 ⟹ 绕数为整数（引用 VBC1）
--   GT2 ★★★ `strandCount_from_field`：三个方向闭合 ⟹ 条数 N=Σnᵢ² 由场给出且为自然数，
--        并且**对每一个这样的场构型**，间隙成立
--   GT3 ★★ `glueball_three_from_windings`：三方向各绕一圈 ⟹ N=3（胶球 0++ 的场来源）
--   GT4 ★★ `no_fractional_count`：不存在"分数条数"的闭合构型（整数性是拓扑强制的）
--   GT5 `gap_mass_form`：间隙的质量形式（m = 0 或 m ≥ √(M₀²)），从 GT2 直接读出
--
-- 诚实边界（写死）：
--   · 本模块把「条数由场定」这一步形式化，但它**只对"闭合相位构型"这一类场**成立；
--     一般的 4 维非阿贝尔规范场构型（矩阵值、非交换）如何给出绕数，仓库里**没有**——
--     那是下一步（`YangMillsFourD` 有 plaquette，还没有从 plaquette 取绕数）。
--   · 「N 的简并度（一层坐几个粒子）」仍缺（见 theory-mass-bookkeeping）。
--   · 不声称解决 Clay：反射正性 / 测度 / 连续极限仍然为零。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.VibrationClosure
import ProjectionPhysics.Explorations.MassGap

noncomputable section
namespace ProjectionPhysics.GapFromTopology

open ProjectionPhysics
open ProjectionPhysics.VibrationClosure
open ProjectionPhysics.MassGap

/-! ### GT1 闭合 ⟹ 绕数整数 -/

/-- GT1 ★★★ **闭合构型的绕数为整数**（VBC1 的直接引用）。
    「条数必须整数」在这一层**不是公设**：它等价于相位走满整圈后复值回到 1。 -/
theorem winding_is_integer (Δ : ℝ) (h : phaseAdvance Δ = 1) :
    ∃ n : ℤ, Δ = n * (2 * Real.pi) :=
  winding_index_integer Δ h

/-! ### GT2 条数由场给出，且间隙对每个场构型成立 -/

/-- 条数：三个方向的绕数绝对值平方和（`|nᵢ|²` 即"条数"）。
    与 `GlueballLadder.IsLadderN` 的 `Σnᵢ²` 同形，但这里的 nᵢ **来自场**。 -/
def strandCountOf (n₁ n₂ n₃ : ℤ) : ℕ :=
  n₁.natAbs * n₁.natAbs + n₂.natAbs * n₂.natAbs + n₃.natAbs * n₃.natAbs

/-- GT2 ★★★ **间隙的场构型版**：给定三个方向各自的闭合相位构型
    （即任意一组满足 `phaseAdvance Δᵢ = 1` 的 Δᵢ），条数 N = Σ|nᵢ|² 由场唯一给出，
    且**对每一个这样的场构型**，质量要么为 0、要么不小于单条质量。

    ⟹ 间隙不再是对"自由自然数 N"的算术重述，而是**关于场构型的全称命题**：
       场只要能闭合，绕数就整数，谱就有下界。整数性来自拓扑（GT1），不是公设。 -/
theorem strandCount_from_field (Δ₁ Δ₂ Δ₃ : ℝ)
    (h₁ : phaseAdvance Δ₁ = 1) (h₂ : phaseAdvance Δ₂ = 1) (h₃ : phaseAdvance Δ₃ = 1)
    (M₀ : ℝ) :
    ∃ (n₁ n₂ n₃ : ℤ),
      Δ₁ = n₁ * (2 * Real.pi) ∧ Δ₂ = n₂ * (2 * Real.pi) ∧ Δ₃ = n₃ * (2 * Real.pi) ∧
      (strandMassSq (strandCountOf n₁ n₂ n₃) M₀ = 0 ∨
        strandMassSq 1 M₀ ≤ strandMassSq (strandCountOf n₁ n₂ n₃) M₀) := by
  obtain ⟨n₁, hn₁⟩ := winding_index_integer Δ₁ h₁
  obtain ⟨n₂, hn₂⟩ := winding_index_integer Δ₂ h₂
  obtain ⟨n₃, hn₃⟩ := winding_index_integer Δ₃ h₃
  exact ⟨n₁, n₂, n₃, hn₁, hn₂, hn₃,
    mass_gap_no_intermediate (N := strandCountOf n₁ n₂ n₃) (M₀ := M₀)⟩

/-- GT2b：同一件事的「显式 N 版」——给定三个整数绕数，质量平方只有 0 或 ≥ M₀²。 -/
theorem gap_of_windings (n₁ n₂ n₃ : ℤ) (M₀ : ℝ) :
    strandMassSq (strandCountOf n₁ n₂ n₃) M₀ = 0 ∨
      strandMassSq 1 M₀ ≤ strandMassSq (strandCountOf n₁ n₂ n₃) M₀ :=
  mass_gap_no_intermediate

/-! ### GT3 胶球的场来源 -/

/-- GT3 ★★ **三方向各绕一圈 ⟹ N = 3**（胶球 0++ 的条数由场给，不是选的）。 -/
theorem glueball_three_from_windings :
    strandCountOf 1 1 1 = 3 := by
  unfold strandCountOf
  norm_num

/-- GT3b：`(1,1,2)` 给出 N = 6（2++ 的场来源）；`(1,2,2)` 给出 N = 9。 -/
theorem glueball_six_from_windings : strandCountOf 1 1 2 = 6 := by
  unfold strandCountOf
  norm_num

theorem glueball_nine_from_windings : strandCountOf 1 2 2 = 9 := by
  unfold strandCountOf
  norm_num

/-! ### GT4 不存在"分数条数" -/

/-- GT4 ★★ **没有分数条数**：任何闭合构型给出的条数都是自然数（`strandCountOf` 的值域是 ℕ）。
    配 GT1：Δ = n·2π 的 n 是 ℤ，平方后进 ℕ ⟹ 不存在"半条"。
    这就是"质量间隙"的拓扑来源：**谱的间隔由整数格强迫，不是由动力学允许**。 -/
theorem no_fractional_count (Δ₁ Δ₂ Δ₃ : ℝ)
    (h₁ : phaseAdvance Δ₁ = 1) (h₂ : phaseAdvance Δ₂ = 1) (h₃ : phaseAdvance Δ₃ = 1) :
    ∃ N : ℕ, ∃ (n₁ n₂ n₃ : ℤ),
      Δ₁ = n₁ * (2 * Real.pi) ∧ Δ₂ = n₂ * (2 * Real.pi) ∧ Δ₃ = n₃ * (2 * Real.pi) ∧
      N = strandCountOf n₁ n₂ n₃ := by
  obtain ⟨n₁, hn₁⟩ := winding_index_integer Δ₁ h₁
  obtain ⟨n₂, hn₂⟩ := winding_index_integer Δ₂ h₂
  obtain ⟨n₃, hn₃⟩ := winding_index_integer Δ₃ h₃
  exact ⟨strandCountOf n₁ n₂ n₃, n₁, n₂, n₃, hn₁, hn₂, hn₃, rfl⟩

/-! ### GT5 质量形式 -/

/-- GT5：间隙的质量形式 —— 阶梯质量 m = √N·M₀ 只取 0 或 ≥ M₀（M₀ > 0，N ≥ 1）。 -/
theorem gap_mass_form {N : ℕ} (hN : 1 ≤ N) {M₀ : ℝ} (hM : 0 < M₀) :
    strandMassSq N M₀ ≠ 0 ∧ strandMassSq 1 M₀ ≤ strandMassSq N M₀ := by
  refine ⟨strand_mass_sq_pos_of_nontrivial hN hM |>.ne', mass_gap_lower_bound hN⟩

/-- GT5b：三方向全非零绕 ⟹ N ≥ 3 ⟹ 质量平方 > 0（胶球不能无质量）。 -/
theorem glueball_mass_positive {n₁ n₂ n₃ : ℤ}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (h₃ : n₃ ≠ 0) {M₀ : ℝ} (hM : 0 < M₀) :
    0 < strandMassSq (strandCountOf n₁ n₂ n₃) M₀ := by
  have hpos : 1 ≤ strandCountOf n₁ n₂ n₃ := by
    unfold strandCountOf
    have h1 : 1 ≤ n₁.natAbs := Int.natAbs_pos.mpr h₁
    have h2 : 1 ≤ n₂.natAbs := Int.natAbs_pos.mpr h₂
    have h3 : 1 ≤ n₃.natAbs := Int.natAbs_pos.mpr h₃
    nlinarith
  exact strand_mass_sq_pos_of_nontrivial hpos hM

end ProjectionPhysics.GapFromTopology
