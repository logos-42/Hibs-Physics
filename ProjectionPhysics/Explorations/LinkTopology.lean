-- ProjectionPhysics — LinkTopology：从**链路**到**绕数**到**条数**到**间隙**（LT1–LT6）
--
-- leo（2026-11-01）：「补上这个坑，开始做」。
--
-- 坑是什么（上一轮的收尾）：`GapFromTopology` 里条数来自"相位构型闭合 ⟹ 绕数整数"，
-- 但**绕数是从一个抽象的 Δ 拿来的**，不是从链路/plaquette 算出来的。中间那节是空的。
--
-- 本模块补这一节，链条变成：
--
--   链路 U_i = e^{iθ_i}（U(1) 值，即"每一段流动的相位"）
--     ⟹ 闭合回路的**乘积** ∏U_i（这就是 Wilson 环的相位）
--     ⟹ 乘积 = 1（闭合）⟹ Σθ_i = 2πk，**k ∈ ℤ**（绕数）
--     ⟹ 条数 N = Σ|k|²（三个方向的绕数平方和）
--     ⟹ 质量 = √N·M₀ ⟹ 间隙（对**每一个**闭合链路构型成立）
--
-- 与 `FlowFourD` 的关系：那里把场强写成 F_μν = d_μθ_ν − d_νθ_μ（plaquette 的相位），
-- 本模块接着把它求和成绕数。**三步合起来 = 场的拓扑决定谱的下界。**
--
--   LT1 ★★ `prod_exp_sum`：∏ e^{iθ_i} = e^{i Σθ_i}（链路乘积 = 总相位的指数）
--   LT2 ★★★ `winding_of_closed_links`：闭合链路（乘积 = 1）⟹ Σθ = 2πk，k ∈ ℤ
--   LT3 ★★★ `small_loops_have_no_winding`：若每段 |θ_i| < 2π/n，则 k = 0
--        —— **绕数需要足够大的总相位**，小回路必然是平凡拓扑（刚性）
--   LT4 ★★★ `strandCount_from_links`：三个方向的闭合链路 ⟹ 条数由链路给出 ⟹ 间隙
--   LT5 ★★ `glueball_count_from_links`：三方向各绕一圈 ⟹ N = 3（胶球 0++ 的链路来源）
--   LT6 `gap_mass_from_links`：间隙的质量形式（m = 0 或 ≥ M₀）
--
-- 诚实边界（写死）：
--   · 本模块做的是 **U(1)（相位）** 那层。矩阵值（非阿贝尔）链路的拓扑荷需要
--     Pontryagin 指数 / 绕数密度，仓库里**没有**——这是下一节，本模块不假装有。
--     （`YangMillsFourD.Y4D2` 已有 plaquette；从矩阵 plaquette 取绕数还没写。）
--   · 绕数用**主值分支**（|θ| ≤ π 的假设在 LT3 里以 n·2π 的形式出现），不做分支切割的完整讨论。
--   · 不声称解决 Clay：反射正性 / 测度 / 连续极限仍为零。

import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.MassGap
import ProjectionPhysics.Explorations.VibrationClosure

noncomputable section
open Finset
open scoped BigOperators

namespace ProjectionPhysics.LinkTopology

open ProjectionPhysics
open ProjectionPhysics.MassGap
open ProjectionPhysics.VibrationClosure

/-! ### LT1 链路乘积 = 总相位的指数 -/

/-- 一条链路：相位 θ 对应的 U(1) 元素 e^{iθ}。 -/
def link (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/-- LT1 ★★ **链路乘积 = 总相位的指数**：∏ᵢ e^{iθᵢ} = e^{i Σθᵢ}。
    这是把"逐段相位"汇总成"整圈相位"的唯一一步。 -/
theorem prod_link_eq_exp_sum {n : ℕ} (θ : Fin n → ℝ) :
    (∏ i, link (θ i)) = Complex.exp (((∑ i, θ i : ℝ) : ℂ) * Complex.I) := by
  unfold link
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]

/-! ### LT2 闭合 ⟹ 绕数整数（从链路算出） -/

/-- LT2 ★★★ **闭合链路的绕数是整数**：若一圈链路的乘积 = 1（Wilson 环闭合），
    则总相位 Σθᵢ = 2πk，k ∈ ℤ。
    ⟹ 绕数**不是输入的整数，是从链路算出来的整数**。 -/
theorem winding_of_closed_links {n : ℕ} (θ : Fin n → ℝ)
    (hclosed : (∏ i, link (θ i)) = 1) :
    ∃ k : ℤ, ∑ i, θ i = k * (2 * Real.pi) := by
  have hexp : Complex.exp (((∑ i, θ i : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← prod_link_eq_exp_sum]; exact hclosed
  exact winding_index_integer (∑ i, θ i) hexp

/-! ### LT3 刚性：小回路没有绕数 -/

/-- LT3 ★★★ **小回路必然平凡**：若每段相位 |θᵢ| < 2π/n，则总相位绝对值 < 2π，
    于是绕数只能是 0。
    ⟹ **绕数需要足够大的总相位**——拓扑不是连续的，它有个门槛。
    （这是"为什么低能看不出拓扑"的代数形式。） -/
theorem small_loops_have_no_winding {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hsmall : ∀ i, |θ i| < 2 * Real.pi / n)
    (hclosed : (∏ i, link (θ i)) = 1) :
    ∃ k : ℤ, k = 0 ∧ ∑ i, θ i = k * (2 * Real.pi) := by
  obtain ⟨k, hk⟩ := winding_of_closed_links θ hclosed
  have hbound : |∑ i, θ i| < 2 * Real.pi := by
    have h1 : |∑ i, θ i| ≤ ∑ i, |θ i| := by
      simpa using Finset.abs_sum_le_sum_abs (fun i => θ i) (univ : Finset (Fin n))
    have h2 : ∑ i, |θ i| < ∑ _i : Fin n, (2 * Real.pi / n) := by
      exact Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun i _ => hsmall i)
    have h3 : ∑ _i : Fin n, (2 * Real.pi / n) = 2 * Real.pi := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    linarith
  have hk0 : k = 0 := by
    have h1 : |(k : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by rw [← hk]; exact hbound
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have h2 : |(k : ℝ)| < 1 := by nlinarith [h1, hpi]
    have hlt := abs_lt.mp h2
    have hk1 : k < 1 := by exact_mod_cast hlt.2
    have hk2 : -1 < k := by exact_mod_cast hlt.1
    omega
  exact ⟨k, hk0, hk⟩

/-! ### LT4 条数由链路给出，间隙对每个链路构型成立 -/

/-- 由三个方向的绕数给出条数：N = Σ|kᵢ|²（与 `GlueballLadder` 的 Σnᵢ² 同形，但 kᵢ 来自链路）。 -/
def countOfWindings (k : Fin 3 → ℤ) : ℕ :=
  ∑ j, (k j).natAbs * (k j).natAbs

/-- LT4 ★★★ **条数由链路给出 ⟹ 间隙对每一个闭合链路构型成立**。
    输入：三个方向各自的闭合链路（`hclosed`），输出：存在整数绕数，N = Σkᵢ²，
    且质量² 要么为 0、要么 ≥ M₀²。
    ⟹ 这是「构建过程算出质量间隙」的完整链条（U(1) 层）：
       **链路闭合 ⟹ 绕数整数 ⟹ 条数 ⟹ 谱有下界**。 -/
theorem strandCount_from_links {n : ℕ} (θ : Fin 3 → Fin n → ℝ)
    (hclosed : ∀ j, (∏ i, link (θ j i)) = 1) (M₀ : ℝ) :
    ∃ k : Fin 3 → ℤ,
      (∀ j, ∑ i, θ j i = k j * (2 * Real.pi)) ∧
      (strandMassSq (countOfWindings k) M₀ = 0 ∨
        strandMassSq 1 M₀ ≤ strandMassSq (countOfWindings k) M₀) := by
  choose k hk using fun j => winding_of_closed_links (θ j) (hclosed j)
  exact ⟨k, hk, mass_gap_no_intermediate (N := countOfWindings k) (M₀ := M₀)⟩

/-! ### LT5 胶球的链路来源 -/

/-- LT5 ★★ **三方向各绕一圈 ⟹ N = 3**：k = (1,1,1)。 -/
theorem glueball_count_from_links : countOfWindings (fun _ => 1) = 3 := by
  simp [countOfWindings]

/-- LT5b：(1,1,2) ⟹ N = 6；(1,2,2) ⟹ N = 9。 -/
theorem two_plus_plus_count : countOfWindings ![1, 1, 2] = 6 := by
  decide

theorem nine_count : countOfWindings ![1, 2, 2] = 9 := by
  decide

/-! ### LT6 质量形式 -/

/-- LT6：三方向绕数全非零 ⟹ N ≥ 3 ⟹ 质量² > 0（胶球不能无质量）。 -/
theorem gap_mass_from_links (k : Fin 3 → ℤ) (hk : ∀ j, k j ≠ 0) {M₀ : ℝ} (hM : 0 < M₀) :
    0 < strandMassSq (countOfWindings k) M₀ := by
  have hterm : ∀ j : Fin 3, 1 ≤ (k j).natAbs * (k j).natAbs := by
    intro j
    have hj : 1 ≤ (k j).natAbs := Int.natAbs_pos.mpr (hk j)
    nlinarith
  have hpos : 1 ≤ countOfWindings k := by
    unfold countOfWindings
    exact le_trans (hterm 0) (Finset.single_le_sum (f := fun j : Fin 3 => (k j).natAbs * (k j).natAbs)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ 0))
  exact strand_mass_sq_pos_of_nontrivial hpos hM

end ProjectionPhysics.LinkTopology
