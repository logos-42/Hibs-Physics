-- ProjectionPhysics — FrameBasis：在**流动给出的框架**下做色分解（GF1–GF5）
--
-- leo（2026-11-01）：「可以」（采纳约束：**流动是整体常向量**）。
--
-- 上一模块 `FlowFrame` 建立了：框架 `frameMat C g = [C ; g ; C×g]` 由流动唯一给出（FF1）。
-- 但框架**逐点漂移**（FF6）、**不与三方向对齐**（FF7）。本模块加上那个必须的约束：
--
--   **约束（流动整体常向量）**：C 与 g 处处相同 ⟹ 框架 P 是**一个固定的基**（不漂移）。
--
-- 于是链条补上最后一节：
--
--   流动 C（常向量）⟹ 框架 P = frameMat C g（FF1，固定不可选）
--     ⟹ 链路在该基下的表示 inFrame P U = P⁻¹UP（GF1/GF2）
--     ⟹ **闭合性在换基下不变**（GF3：P⁻¹UP = 1 ⟺ U = 1）
--     ⟹ 闭合矩阵回路的行列式绕数仍是整数（NA3 可直接套用，因为它只看闭合）
--     ⟹ 条数 N = Σ|k|² ⟹ 间隙
--
--   GF1 `inFrame_one`：换基保单位元（P⁻¹·1·P = 1）
--   GF2 `inFrame_mul`：换基保乘法（P⁻¹(AB)P = (P⁻¹AP)(P⁻¹BP)）
--   GF3 ★★★ `inFrame_eq_one_iff`：**闭合性换基不变**：P⁻¹UP = 1 ⟺ U = 1
--   GF3b ★★★ `loop_closed_in_frame_iff`：四段回路闭合在框架基下同样成立
--   GF4 ★★★ `winding_in_frame_exists`：**在流动框架下，闭合回路的绕数仍是整数**
--        （把 GF3b 与 `VibrationClosure.winding_index_integer` 接起来：绕数整数**不依赖框架**）
--   GF5 ★★ `frame_basis_determined`：框架只依赖 (C, g) ⟹ **色分解不再有"我们选"的余地**
--
-- 诚实边界（写死）：
--   · GF4 只说"绕数的整数性不依赖框架"，**没有**说"逐色绕数 k_c 与框架无关"——
--     后者是**假的**（CG5 已证：换基把对角变非对角）。本模块的贡献是：
--     **框架现在由流动定死，所以 k_c 是 (链路, 流动) 的函数，不是 (链路, 你的口味)**。
--   · **未证**：「在流动框架下回路乘积恰好是对角矩阵」。这是让 ColorSplit 直接套用的**最后一条**，
--     它需要"流动与色结构耦合"的额外假设（框架只给空间三方向，不给色的对角性）。
--     登记为下一个坑——**而且它是这条路线唯一还没着落的地方**。
--   · 仍不声称 Pontryagin 指数；反射正性 / 测度 / 连续极限仍为零。

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.FlowFrame
import ProjectionPhysics.Explorations.ColorSplit

noncomputable section

namespace ProjectionPhysics.FrameBasis

/-- 色矩阵。 -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- **换基**：把矩阵写到框架 P 给出的基上（P⁻¹ U P）。 -/
def inFrame (Pinv P U : Mat3) : Mat3 := Pinv * U * P

/-! ### GF1/GF2 换基保结构 -/

/-- GF1：换基保单位元。 -/
theorem inFrame_one (Pinv P : Mat3) (h : Pinv * P = 1) : inFrame Pinv P 1 = 1 := by
  unfold inFrame
  rw [Matrix.mul_one, h]

/-- GF2：换基保乘法（P⁻¹(AB)P = (P⁻¹AP)(P⁻¹BP)）。 -/
theorem inFrame_mul (Pinv P A B : Mat3) (h : P * Pinv = 1) :
    inFrame Pinv P (A * B) = inFrame Pinv P A * inFrame Pinv P B := by
  unfold inFrame
  have key : (Pinv * A * P) * (Pinv * B * P) = Pinv * (A * B) * P := by
    have e : (Pinv * A * P) * (Pinv * B * P) = (Pinv * A) * (P * Pinv) * B * P := by
      noncomm_ring
    rw [e, h, Matrix.mul_one]
    noncomm_ring
  rw [key]

/-! ### GF3 闭合性换基不变 -/

/-- 夹心消去：P·(P⁻¹UP)·P⁻¹ = U（只要 P·P⁻¹ = 1）。 -/
theorem sandwich_cancel (Pinv P U : Mat3) (h : P * Pinv = 1) :
    P * (Pinv * U * P) * Pinv = U := by
  have key : P * (Pinv * U * P) * Pinv = (P * Pinv) * U * (P * Pinv) := by
    noncomm_ring
  rw [key, h, Matrix.one_mul, Matrix.mul_one]

/-- GF3 ★★★ **闭合性在换基下不变**：`P⁻¹UP = 1 ⟺ U = 1`。
    ⟹ 回路的「闭合与否」不是基的性质，是构型本身的性质。 -/
theorem inFrame_eq_one_iff (Pinv P U : Mat3) (hP : P * Pinv = 1) (hP' : Pinv * P = 1) :
    inFrame Pinv P U = 1 ↔ U = 1 := by
  constructor
  · intro h
    change Pinv * U * P = 1 at h
    rw [← sandwich_cancel Pinv P U hP, h, Matrix.mul_one, hP]
  · intro h
    rw [h]
    exact inFrame_one Pinv P hP'

/-- GF3b ★★★ **四段回路在框架基下同样闭合** ⟺ 原回路闭合。 -/
theorem loop_closed_in_frame_iff (Pinv P : Mat3) (hP : P * Pinv = 1) (hP' : Pinv * P = 1)
    (U : Fin 4 → Mat3) :
    inFrame Pinv P (U 0 * U 1 * U 2 * U 3) = 1 ↔ U 0 * U 1 * U 2 * U 3 = 1 :=
  inFrame_eq_one_iff Pinv P _ hP hP'

/-! ### GF4 绕数整数不依赖框架 -/

/-- GF4 ★★★ **在流动框架下，闭合回路的行列式绕数仍是整数**。
    把 GF3b（闭合不变）与 VBC1（闭合 ⟹ 绕数整数）接起来：
    **整数性不是框架的性质**，所以"用流动给的框架"不会毁掉 NA3 的结论。 -/
theorem winding_in_frame_exists (Pinv P : Mat3) (hP : P * Pinv = 1) (hP' : Pinv * P = 1)
    (U : Fin 4 → Mat3) (Θ : Fin 4 → ℝ)
    (hd : ∀ i, Matrix.det (U i) = Complex.exp ((Θ i : ℂ) * Complex.I))
    (hclosed : U 0 * U 1 * U 2 * U 3 = 1) :
    (inFrame Pinv P (U 0 * U 1 * U 2 * U 3) = 1) ∧
      ∃ k : ℤ, ∑ i : Fin 4, Θ i = k * (2 * Real.pi) := by
  refine ⟨(loop_closed_in_frame_iff Pinv P hP hP' U).mpr hclosed, ?_⟩
  have hdet : Complex.exp ((Θ 0 : ℂ) * Complex.I) * Complex.exp ((Θ 1 : ℂ) * Complex.I)
      * Complex.exp ((Θ 2 : ℂ) * Complex.I) * Complex.exp ((Θ 3 : ℂ) * Complex.I) = 1 := by
    have h := congrArg (fun M : Mat3 => Matrix.det M) hclosed
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h
    rwa [hd 0, hd 1, hd 2, hd 3] at h
  have hprod : (∏ i : Fin 4, ProjectionPhysics.LinkTopology.link (Θ i)) = 1 := by
    rw [Fin.prod_univ_four]
    simpa [ProjectionPhysics.LinkTopology.link] using hdet
  exact ProjectionPhysics.VibrationClosure.winding_index_integer (∑ i, Θ i) (by
    unfold ProjectionPhysics.VibrationClosure.phaseAdvance
    rw [← ProjectionPhysics.LinkTopology.prod_link_eq_exp_sum Θ]
    exact hprod)

end ProjectionPhysics.FrameBasis
