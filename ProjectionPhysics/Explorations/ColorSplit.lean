-- ProjectionPhysics — ColorSplit：把 det 拆成三个色（CS1–CS6）
--
-- leo（2026-11-01）：「可以拆 det」。
--
-- 上一轮（`NonAbelianLinkTopology`）用**行列式**把绕数升到矩阵端，但那给的是**一个**
-- 整数（三色之和）。条数规则要的是 **Σ_c|k_c|²**（三个色各自的平方和）。本模块把
-- 那个整数**拆开**：
--
--   对角链路 diag(e^{iθ₁}, e^{iθ₂}, e^{iθ₃})（极大环面）
--     ⟹ 对角乘对角 = 对角元相乘（CS1）
--     ⟹ 回路闭合 ⟹ **每个色的乘积各自 = 1**
--     ⟹ 每个色的相位和 Σᵢθ_{c,i} = 2πk_c，**k_c ∈ ℤ，逐色独立**（CS2/CS3）
--     ⟹ det 的绕数 = Σ_c k_c（CS4：这就是"拆 det"）
--     ⟹ 条数 N = Σ_c|k_c|²（CS5）⟹ 间隙
--
--   CS1 `diag_mul_apply`：对角乘对角的对角元 = 对角元相乘（非对角项为 0）
--   CS1b `loop4_diag_apply`：四段对角回路的对角元 = 四个相位指数之积
--   CS2 ★★★ `color_windings_of_closed_diagonal_loop`：闭合 ⟹ **三个色各自给出整数绕数**
--   CS3 ★★★ `color_product_one`：闭合 ⟹ 每个色的乘积 = 1（色之间不混合）
--   CS4 ★★★ `det_winding_is_color_sum`：**det 的绕数 = Σ_c k_c**（拆 det 的结论）
--   CS5 ★★★ `gap_from_color_windings`：条数 N = Σ_c|k_c|²（`countOfWindings`）⟹ 间隙
--   CS6 `witness_one_color`：见证——只有第 1 色带相位 π/2，四圈 ⟹ k₁=1，另两色 k=0
--
-- 诚实边界（写死）：
--   · 本模块只做**对角**（极大环面）情形。**一般非对角矩阵**的逐色分解需要
--     本征值/三角化（`Module.End` 谱分解），仓库里**没有**——这是下一个坑。
--   · 对角情形的"色"是**色指标**（3 个分量），不是 SU(3) 权重的物理色荷；
--     两者在这里重合是因为对角子代数就是 3 个独立的 U(1)。
--   · 仍不声称 Pontryagin 指数；反射正性 / 测度 / 连续极限仍为零。

import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.MassGap
import ProjectionPhysics.Explorations.VibrationClosure
import ProjectionPhysics.Explorations.LinkTopology

noncomputable section
open scoped BigOperators
open Finset

namespace ProjectionPhysics.ColorSplit

open ProjectionPhysics
open ProjectionPhysics.MassGap
open ProjectionPhysics.VibrationClosure
open ProjectionPhysics.LinkTopology

/-- 色矩阵。 -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- 对角链路：第 c 个色带相位 θ c。 -/
def diagLink (θ : Fin 3 → ℝ) : Mat3 :=
  Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I))

/-! ### CS1 对角乘对角 -/

/-- CS1 ★ **对角乘对角的对角元 = 对角元相乘**（非对角项贡献为 0）。 -/
theorem diag_mul_apply (a b : Fin 3 → ℂ) (c : Fin 3) :
    (Matrix.diagonal a * Matrix.diagonal b) c c = a c * b c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · intro b' _ hne
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hne), Matrix.diagonal_apply_ne _ hne]
    simp
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- CS1a ★ **对角乘对角 = 对角（对角元相乘）**：`diag a * diag b = diag (a*b)`。 -/
theorem diag_mul_diag (a b : Fin 3 → ℂ) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal (a * b) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diag_mul_apply, Matrix.diagonal_apply_eq, Pi.mul_apply]
  · rw [Matrix.mul_apply, Matrix.diagonal_apply_ne _ hij, Finset.sum_eq_zero]
    intro k _
    by_cases hik : i = k
    · subst hik
      rw [Matrix.diagonal_apply_ne _ hij, mul_zero]
    · rw [Matrix.diagonal_apply_ne _ hik, zero_mul]

/-- CS1b：四段对角回路的对角元 = 四个相位指数之积。 -/
theorem loop4_diag_apply (Θ : Fin 4 → Fin 3 → ℝ) (c : Fin 3) :
    (diagLink (Θ 0) * diagLink (Θ 1) * diagLink (Θ 2) * diagLink (Θ 3)) c c
      = Complex.exp ((Θ 0 c : ℂ) * Complex.I) * Complex.exp ((Θ 1 c : ℂ) * Complex.I)
        * Complex.exp ((Θ 2 c : ℂ) * Complex.I) * Complex.exp ((Θ 3 c : ℂ) * Complex.I) := by
  simp only [diagLink]
  rw [diag_mul_diag, diag_mul_diag, diag_mul_diag, Matrix.diagonal_apply_eq]
  simp only [Pi.mul_apply]

/-! ### CS2/CS3 闭合 ⟹ 逐色整数 -/

/-- CS3 ★★★ **色之间不混合**：对角回路闭合 ⟹ 每个色的乘积各自 = 1。 -/
theorem color_product_one (Θ : Fin 4 → Fin 3 → ℝ)
    (hclosed : diagLink (Θ 0) * diagLink (Θ 1) * diagLink (Θ 2) * diagLink (Θ 3) = 1)
    (c : Fin 3) :
    Complex.exp ((Θ 0 c : ℂ) * Complex.I) * Complex.exp ((Θ 1 c : ℂ) * Complex.I)
      * Complex.exp ((Θ 2 c : ℂ) * Complex.I) * Complex.exp ((Θ 3 c : ℂ) * Complex.I) = 1 := by
  have h := congrArg (fun M : Mat3 => M c c) hclosed
  simpa [loop4_diag_apply, Matrix.one_apply_eq] using h

/-- CS2 ★★★ **逐色绕数整数**：闭合对角回路 ⟹ 三个色各自给出整数绕数 k_c，
    满足 Σᵢθ_{c,i} = 2πk_c。
    ⟹ 「条数」可以从**矩阵链路**逐色算出来，不是外加规则。 -/
theorem color_windings_of_closed_diagonal_loop (Θ : Fin 4 → Fin 3 → ℝ)
    (hclosed : diagLink (Θ 0) * diagLink (Θ 1) * diagLink (Θ 2) * diagLink (Θ 3) = 1) :
    ∃ k : Fin 3 → ℤ, ∀ c : Fin 3, ∑ i : Fin 4, Θ i c = k c * (2 * Real.pi) := by
  have hprod : ∀ c : Fin 3, (∏ i : Fin 4, link (Θ i c)) = 1 := by
    intro c
    rw [Fin.prod_univ_four]
    simpa [link] using color_product_one Θ hclosed c
  choose k hk using fun c : Fin 3 => winding_index_integer (∑ i : Fin 4, Θ i c) (by
    unfold phaseAdvance
    rw [← prod_link_eq_exp_sum (fun i => Θ i c)]
    exact hprod c)
  exact ⟨k, hk⟩

/-! ### CS4 拆 det：行列式绕数 = 三色之和 -/

/-- CS4 ★★★ **det 的绕数 = Σ_c k_c**（"拆 det"的结论）。
    即：上一轮那个"一个整数"，正好是三个色整数之和。
    ⟹ 行列式给的是**总和**（第一 Chern 类），逐色才给**条数**需要的分量。 -/
theorem det_winding_is_color_sum (Θ : Fin 4 → Fin 3 → ℝ)
    (hclosed : diagLink (Θ 0) * diagLink (Θ 1) * diagLink (Θ 2) * diagLink (Θ 3) = 1) :
    ∃ k : Fin 3 → ℤ,
      (∀ c : Fin 3, ∑ i : Fin 4, Θ i c = k c * (2 * Real.pi)) ∧
      (∃ K : ℤ, (∑ c : Fin 3, ∑ i : Fin 4, Θ i c) = K * (2 * Real.pi) ∧ K = ∑ c : Fin 3, k c) := by
  obtain ⟨k, hk⟩ := color_windings_of_closed_diagonal_loop Θ hclosed
  refine ⟨k, hk, ⟨∑ c : Fin 3, k c, ?_, rfl⟩⟩
  calc ∑ c : Fin 3, ∑ i : Fin 4, Θ i c
      = ∑ c : Fin 3, k c * (2 * Real.pi) := by
        exact Finset.sum_congr rfl (fun c _ => hk c)
    _ = ((∑ c : Fin 3, k c : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        rw [Finset.sum_mul]

/-! ### CS5 条数逐色给出 ⟹ 间隙 -/

/-- CS5 ★★★ **条数由逐色绕数给出 ⟹ 间隙**：一个方向上三条对角链路闭合 ⟹
    条数 N = Σ_c|k_c|²（`countOfWindings`）⟹ 质量² 要么 0、要么 ≥ 单条质量²。 -/
theorem gap_from_color_windings (Θ : Fin 4 → Fin 3 → ℝ)
    (hclosed : diagLink (Θ 0) * diagLink (Θ 1) * diagLink (Θ 2) * diagLink (Θ 3) = 1)
    (M₀ : ℝ) :
    ∃ k : Fin 3 → ℤ,
      (∀ c : Fin 3, ∑ i : Fin 4, Θ i c = k c * (2 * Real.pi)) ∧
      (strandMassSq (countOfWindings k) M₀ = 0 ∨
        strandMassSq 1 M₀ ≤ strandMassSq (countOfWindings k) M₀) := by
  obtain ⟨k, hk⟩ := color_windings_of_closed_diagonal_loop Θ hclosed
  exact ⟨k, hk, mass_gap_no_intermediate (N := countOfWindings k) (M₀ := M₀)⟩

/-! ### CS6 见证：只有一个色带相位也能给出整数绕数 -/

/-- CS6 ★★ 见证的相位序列：每段 π/2，四段合计 2π ⟹ k = 1（其余两色为 0）。 -/
theorem witness_one_color : (∑ _i : Fin 4, (Real.pi / 2)) = 1 * (2 * Real.pi) := by
  rw [Fin.sum_univ_four]
  ring

/-- CS6b：该见证下条数 N = |1|² + 0 + 0 = 1。 -/
theorem witness_count : countOfWindings ![1, 0, 0] = 1 := by
  decide

end ProjectionPhysics.ColorSplit
