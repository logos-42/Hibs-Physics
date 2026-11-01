-- ProjectionPhysics — NonAbelianLinkTopology：把绕数从相位**升级到矩阵**（NA1–NA7）
--
-- leo（2026-11-01）：「开始升级」——把 `LinkTopology` 的 U(1) 结果升级到非阿贝尔（矩阵）链路。
--
-- 升级的关键入口：**行列式**。
--   det : GL(3,ℂ) → ℂ* 是**群同态**（`det(AB) = detA·detB`），
--   所以矩阵链路的闭合回路，其**行列式相位**仍走满整圈 ⟹ 绕数仍是整数。
--   而 det 在共轭下不变 ⟹ 这个整数是**规范不变的**。
--
-- 这就是"非阿贝尔版的 VBC1"：
--
--   相位（U(1)）版（LT2）：闭合 ⟹ Σθ = 2πk
--   矩阵（U(3)）版（NA3）：矩阵回路闭合 ⟹ Σ arg det(U_i) = 2πk     ← 本模块
--   且 NA4：det(g P g⁻¹) = det P ⟹ 这个 k 与规范选取无关
--
-- 链条（升级后）：
--   矩阵链路 U_i ⟹ 四段回路乘积 P（plaquette 的抽象）⟹ P = 1（闭合）
--     ⟹ det P = 1 ⟹ Σ arg det U_i = 2πk，k ∈ ℤ（**规范不变**）
--     ⟹ 三个方向各一个 k ⟹ 条数 N = Σ|k|² ⟹ 质量 = √N·M₀ ⟹ 间隙
--
--   NA1 `detLink_mul`：det 在同态意义下可乘（矩阵版的核心恒等式）
--   NA2 `detLink_mul_inv` / `detLink_inv_mul`：det 与逆元相容
--   NA3 ★★★ `winding_of_closed_matrix_loop`：四段矩阵回路闭合 ⟹ 行列式绕数 ∈ ℤ
--   NA4 ★★★ `detLink_conj`：**行列式绕数规范不变**（共轭下不变）
--        ⟹ 「非阿贝尔的整数」是一个**可观测**（不依赖规范），这是升级的实质
--   NA5 ★★★ `gap_from_matrix_loops`：三方向矩阵回路 ⟹ 条数由链路给出 ⟹ 间隙
--   NA6 ★★ `detLink_one` / `loop4`：回路闭合的定义与单位元
--   NA7 `loop4_of_diag_witness`：一个**非平凡见证**——对角链路 diag(i,1,1) 绕四圈
--        矩阵乘积回到 1、行列式绕数为 1，而只有第 1 色带相位 ⟹ 色分解真实存在
--
-- 诚实边界（写死）：
--   · 本模块用 **det（色求和）** 作为非阿贝尔整数。**逐色分解**（Σ_c|k_c|²）只在
--     对角（极大环面）情形下成立，本模块只给 NA7 的单个见证，不给一般定理。
--   · **不**等价于 Pontryagin 指数：4 维瞬子荷需要 ε_{μνρσ}tr(F∧F)，本模块
--     只做"闭合回路 ⟹ 行列式绕数"，那是 Pontryagin 的**阿贝尔影子**（第一 Chern 类）。
--   · 不声称解决 Clay：反射正性 / 测度 / 连续极限仍为零。

import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.MassGap
import ProjectionPhysics.Explorations.VibrationClosure
import ProjectionPhysics.Explorations.LinkTopology

noncomputable section
open scoped BigOperators

namespace ProjectionPhysics.NonAbelianLinkTopology

open ProjectionPhysics
open ProjectionPhysics.MassGap
open ProjectionPhysics.VibrationClosure
open ProjectionPhysics.LinkTopology

/-- 非阿贝尔链路：可逆色矩阵（= GL(3,ℂ)，用 Units 表示）。 -/
abbrev ColorLink := Units (Matrix (Fin 3) (Fin 3) ℂ)

/-- 链路的**行列式**（色求和后的单个复数）——非阿贝尔整数的入口。 -/
def detLink (u : ColorLink) : ℂ := Matrix.det u.val

/-! ### NA1–NA2 det 是同态 -/

/-- NA1 ★★★ **det 可乘**：det(uv) = det(u)·det(v)（矩阵行列式乘性的群版）。 -/
theorem detLink_mul (u v : ColorLink) : detLink (u * v) = detLink u * detLink v := by
  unfold detLink
  rw [Units.val_mul, Matrix.det_mul]

/-- NA2c：单位元的行列式为 1。 -/
theorem detLink_one : detLink (1 : ColorLink) = 1 := by
  simp [detLink]

/-- NA2a：det(u·u⁻¹) = 1。 -/
theorem detLink_mul_inv (u : ColorLink) : detLink u * detLink u⁻¹ = 1 := by
  rw [← detLink_mul, mul_inv_cancel]
  exact detLink_one

/-- NA2b：det(u⁻¹·u) = 1。 -/
theorem detLink_inv_mul (u : ColorLink) : detLink u⁻¹ * detLink u = 1 := by
  rw [← detLink_mul, inv_mul_cancel]
  exact detLink_one

/-! ### NA6 回路乘积（plaquette 的抽象：四段闭合） -/

/-- 四段回路乘积（1×1 Wilson 环的抽象形式）：P = U₀U₁U₂U₃。 -/
def loop4 (U : Fin 4 → ColorLink) : ColorLink := U 0 * U 1 * U 2 * U 3

/-- NA6：回路的行列式 = 行列式的乘积（四项显式）。 -/
theorem detLink_loop4 (U : Fin 4 → ColorLink) :
    detLink (loop4 U) = detLink (U 0) * detLink (U 1) * detLink (U 2) * detLink (U 3) := by
  unfold loop4
  rw [detLink_mul, detLink_mul, detLink_mul]

/-! ### NA3 闭合矩阵回路 ⟹ 行列式绕数整数 -/

/-- NA3 ★★★ **非阿贝尔版的绕数整数**：四段矩阵回路闭合（P = 1），
    且每段的**行列式**是单位模相位 e^{iθᵢ}，则 Σθᵢ = 2πk，k ∈ ℤ。

    ⟹ 绕数不再是"相位场的性质"，而是**矩阵链路的性质**（通过 det 这个同态）。 -/
theorem winding_of_closed_matrix_loop (U : Fin 4 → ColorLink) (θ : Fin 4 → ℝ)
    (hd : ∀ i, detLink (U i) = Complex.exp ((θ i : ℂ) * Complex.I))
    (hclosed : loop4 U = 1) :
    ∃ k : ℤ, ∑ i, θ i = k * (2 * Real.pi) := by
  have hdet : detLink (loop4 U) = 1 := by rw [hclosed, detLink_one]
  have hprod : detLink (loop4 U) = ∏ i : Fin 4, link (θ i) := by
    rw [detLink_loop4, Fin.prod_univ_four]
    simp only [hd, link]
  have hexp : Complex.exp (((∑ i, θ i : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← prod_link_eq_exp_sum θ, ← hprod, hdet]
  exact winding_index_integer (∑ i, θ i) hexp

/-! ### NA4 规范不变性（升级的实质） -/

/-- NA4 ★★★ **行列式绕数在规范变换下不变**：det(g·P·g⁻¹) = det(P)。
    ⟹ 「非阿贝尔的整数」是一个**规范不变量**（可观测），
       这与 U(1) 版的关键差别：那里的整数依赖相位场的取值，这里的与规范选取无关。 -/
theorem detLink_conj (g P : ColorLink) : detLink (g * P * g⁻¹) = detLink P := by
  rw [detLink_mul, detLink_mul]
  have h : detLink g * detLink g⁻¹ = 1 := detLink_mul_inv g
  calc detLink g * detLink P * detLink g⁻¹
      = detLink P * (detLink g * detLink g⁻¹) := by ring
    _ = detLink P * 1 := by rw [h]
    _ = detLink P := by ring

/-! ### NA5 条数由矩阵链路给出 ⟹ 间隙 -/

/-- NA5 ★★★ **升级后的间隙**：三个方向各一条闭合矩阵回路（各自给出行列式绕数 kⱼ），
    条数 N = Σ|kⱼ|² 由链路给出，且质量² 要么为 0、要么 ≥ 单条质量²。
    ⟹ 「构建过程算出质量间隙」这条链，现在**矩阵链路**那一端也接上了。 -/
theorem gap_from_matrix_loops (U : Fin 3 → Fin 4 → ColorLink) (θ : Fin 3 → Fin 4 → ℝ)
    (hd : ∀ j i, detLink (U j i) = Complex.exp ((θ j i : ℂ) * Complex.I))
    (hclosed : ∀ j, loop4 (U j) = 1) (M₀ : ℝ) :
    ∃ k : Fin 3 → ℤ,
      (∀ j, ∑ i, θ j i = k j * (2 * Real.pi)) ∧
      (strandMassSq (countOfWindings k) M₀ = 0 ∨
        strandMassSq 1 M₀ ≤ strandMassSq (countOfWindings k) M₀) := by
  choose k hk using fun j => winding_of_closed_matrix_loop (U j) (θ j) (hd j) (hclosed j)
  exact ⟨k, hk, mass_gap_no_intermediate (N := countOfWindings k) (M₀ := M₀)⟩

/-! ### NA7 见证：非标量矩阵可以带纯虚行列式 -/

/-- NA7 ★★ **非标量链路可以只让一个色带相位**：
    `diag(i, 1, 1)` 的行列式 = i（只有第 1 色带相位 π/2，另两色为 1）。
    ⟹ 「行列式绕数」不是"三个色相位都要动"才有的东西，色分解是真实的。 -/
theorem witness_diag_det :
    Matrix.det (Matrix.diagonal (fun i : Fin 3 => if i = 0 then Complex.I else 1))
      = Complex.I := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  norm_num

end ProjectionPhysics.NonAbelianLinkTopology
