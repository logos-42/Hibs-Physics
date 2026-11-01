-- ProjectionPhysics — ChainClosure：把整条链写成一个**带显式前提的定理**（CL1–CL4）
--
-- leo（2026-11-01）：选 **B** —— 不加强行耦合假设，接受现状：
-- 框架由流动给出、绕数整数、条数可算；但「逐色」这一步只在**色基与空间基对齐**时有效。
--
-- 本模块的作用是**把这件事说死**：把整条链压成一条定理，其中
-- **每一个输入都出现在前提里**，一个都不能藏。
--
--   前提 ①：框架 P 是一个基（P·P⁻¹ = 1）——由流动给出（`FlowFrame` FF1–FF3），
--            存在条件 = 流动与电荷梯度不平行（FF3 的逆否）。
--   前提 ②：**对齐假设**——每条链路在流动框架下是**对角**的相位矩阵：
--            P⁻¹UᵢP = diag(exp(iθ_{c,i}))
--            —— 这**不是**自动的（见 CL3），是这条路线唯一的外部输入。
--   前提 ③：四段回路闭合（U₀U₁U₂U₃ = 1）。
--
--   结论：每个色各自给出整数绕数 k_c（Σᵢθ_{c,i} = 2πk_c），
--         条数 N = Σ|k_c|²，质量² 要么 0、要么 ≥ 单条质量²（间隙）。
--
--   CL1 ★★★ `chain_closes`：**主定理**（带前提①–③）——整条链一次说完
--   CL2 ★★ `chain_gives_gap`：只取间隙部分的推论形式
--   CL3 ★★★ `alignment_not_automatic`：**对齐不是自动的**——存在非对角链路，
--        故前提②是真前提，不是重言式（这条定理防止"已经证完"的误读）
--   CL4 ★★ `frame_degenerate_obstructs`：前提①失败（框架退化）时链条在第一环就断
--
-- 诚实边界（写死）：
--   · 本模块**不证明**前提②在自然中成立。它只证明「②成立则全链闭合」。
--     把②当成定理去宣称 = 过度声称，禁止。
--   · 前提②的物理内容：**色结构必须与流动所给的三个空间方向对齐**。
--     这是可判死的猜想（死法见 wiki `theory-yangmills-fourd.md` 的 ALIGN 条目）：
--       (a) 若流动框架下链路非对角 ⟹ 逐色条数失去定义（`ColorSplitGauge` CG5 已证）；
--       (b) 若框架逐点漂移 ⟹ 全局 k_c 不存在（`FlowFrame` FF6 已证）。
--   · 仍不声称 Pontryagin 指数；反射正性 / 测度 / 连续极限仍为零。

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.FrameBasis
import ProjectionPhysics.Explorations.ColorSplit
import ProjectionPhysics.Explorations.MassGap

noncomputable section
open scoped BigOperators

namespace ProjectionPhysics.ChainClosure

open ProjectionPhysics
open ProjectionPhysics.MassGap
open ProjectionPhysics.LinkTopology (countOfWindings)
open ProjectionPhysics.FrameBasis (inFrame inFrame_mul inFrame_eq_one_iff loop_closed_in_frame_iff)

/-- 色矩阵。 -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-! ### CL1 主定理：整条链，前提全在明面上 -/

/-- CL1 ★★★ **主定理（带显式前提）**：

    前提① 框架是基：`P · P⁻¹ = 1`、`P⁻¹ · P = 1`（由流动给出，存在条件 = FF3 的逆否）
    前提② **对齐**：每条链路在框架下是对角相位矩阵 `P⁻¹UᵢP = diag(exp(iθ_{c,i}))`
    前提③ 闭合：`U₀U₁U₂U₃ = 1`

    结论：**逐色绕数 k_c ∈ ℤ**（Σᵢθ_{c,i} = 2πk_c），条数 `N = Σ|k_c|²`，且间隙成立。
    —— 前提②是**唯一**的外部输入，不能藏。 -/
theorem chain_closes (Pinv P : Mat3) (hP : P * Pinv = 1) (hP' : Pinv * P = 1)
    (U : Fin 4 → Mat3) (Θ : Fin 4 → Fin 3 → ℝ)
    (halign : ∀ i, inFrame Pinv P (U i)
      = Matrix.diagonal (fun c => Complex.exp ((Θ i c : ℂ) * Complex.I)))
    (hclosed : U 0 * U 1 * U 2 * U 3 = 1) (M₀ : ℝ) :
    ∃ k : Fin 3 → ℤ,
      (∀ c : Fin 3, ∑ i : Fin 4, Θ i c = k c * (2 * Real.pi)) ∧
      (strandMassSq (countOfWindings k) M₀ = 0 ∨
        strandMassSq 1 M₀ ≤ strandMassSq (countOfWindings k) M₀) := by
  -- ① 闭合 ⟹ 框架下的回路乘积 = 1
  have hframe : inFrame Pinv P (U 0 * U 1 * U 2 * U 3) = 1 :=
    (loop_closed_in_frame_iff Pinv P hP hP' U).mpr hclosed
  -- ② 换基保乘法 ⟹ 框架下的乘积 = 四个对角相位矩阵之积
  have hprod : inFrame Pinv P (U 0 * U 1 * U 2 * U 3)
      = Matrix.diagonal (fun c => Complex.exp ((Θ 0 c : ℂ) * Complex.I)
          * Complex.exp ((Θ 1 c : ℂ) * Complex.I)
          * Complex.exp ((Θ 2 c : ℂ) * Complex.I)
          * Complex.exp ((Θ 3 c : ℂ) * Complex.I)) := by
    rw [inFrame_mul Pinv P _ _ hP, inFrame_mul Pinv P _ _ hP, inFrame_mul Pinv P _ _ hP,
      halign 0, halign 1, halign 2, halign 3]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  -- ③ 每个色的乘积 = 1，于是各自给出整数绕数
  have hcolor : ∀ c : Fin 3,
      Complex.exp ((Θ 0 c : ℂ) * Complex.I) * Complex.exp ((Θ 1 c : ℂ) * Complex.I)
        * Complex.exp ((Θ 2 c : ℂ) * Complex.I) * Complex.exp ((Θ 3 c : ℂ) * Complex.I) = 1 := by
    intro c
    have h := congrArg (fun M : Mat3 => M c c) (hprod.symm.trans hframe)
    simpa [Matrix.one_apply_eq] using h
  have hprodlink : ∀ c : Fin 3, (∏ i : Fin 4, ProjectionPhysics.LinkTopology.link (Θ i c)) = 1 := by
    intro c
    rw [Fin.prod_univ_four]
    simpa [ProjectionPhysics.LinkTopology.link] using hcolor c
  choose k hk using fun c : Fin 3 =>
    ProjectionPhysics.VibrationClosure.winding_index_integer (∑ i : Fin 4, Θ i c) (by
      unfold ProjectionPhysics.VibrationClosure.phaseAdvance
      rw [← ProjectionPhysics.LinkTopology.prod_link_eq_exp_sum (fun i => Θ i c)]
      exact hprodlink c)
  exact ⟨k, hk, mass_gap_no_intermediate (N := countOfWindings k) (M₀ := M₀)⟩

/-- CL2 ★★ **间隙部分单独取出**（主定理的推论形式）。 -/
theorem chain_gives_gap (Pinv P : Mat3) (hP : P * Pinv = 1) (hP' : Pinv * P = 1)
    (U : Fin 4 → Mat3) (Θ : Fin 4 → Fin 3 → ℝ)
    (halign : ∀ i, inFrame Pinv P (U i)
      = Matrix.diagonal (fun c => Complex.exp ((Θ i c : ℂ) * Complex.I)))
    (hclosed : U 0 * U 1 * U 2 * U 3 = 1) (M₀ : ℝ) :
    ∃ N : ℕ, strandMassSq N M₀ = 0 ∨ strandMassSq 1 M₀ ≤ strandMassSq N M₀ :=
  ⟨countOfWindings (Classical.choose (chain_closes Pinv P hP hP' U Θ halign hclosed M₀)),
    (Classical.choose_spec (chain_closes Pinv P hP hP' U Θ halign hclosed M₀)).2⟩

/-! ### CL3 对齐不是自动的 -/

/-- CL3 ★★★ **前提②是真前提，不是重言式**：存在非对角矩阵
    （因此"每条链路在框架下是对角"这句话有内容，不能免费得到）。
    ⟹ 这条定理的作用是**防止误读**：`chain_closes` 不能被当成"已证完"。 -/
theorem alignment_not_automatic :
    ∃ M : Mat3, ∃ i j : Fin 3, i ≠ j ∧ M i j ≠ 0 := by
  refine ⟨!![(1 : ℂ), 1, 0; 0, 1, 0; 0, 0, 1], 0, 1, by decide, ?_⟩
  simp

/-! ### CL4 前提①失败时链条在第一环就断 -/

/-- CL4 ★★ **框架退化 ⟹ 链条在第一步就断**：若流动与电荷梯度平行（框架 det = 0），
    则换基 `P⁻¹UP` 本身没有意义（P 不可逆）——前提①失败，后面的都不成立。 -/
theorem frame_degenerate_obstructs (C g : ProjectionPhysics.FlowFrame.Vec3)
    (h : (ProjectionPhysics.FlowFrame.frameMat C g).det = 0) :
    ¬ ∃ Pinv : Matrix (Fin 3) (Fin 3) ℝ,
      ProjectionPhysics.FlowFrame.frameMat C g * Pinv = 1 := by
  rintro ⟨Pinv, hP⟩
  have hd : Matrix.det (ProjectionPhysics.FlowFrame.frameMat C g * Pinv)
      = Matrix.det (1 : Matrix (Fin 3) (Fin 3) ℝ) := by rw [hP]
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hd
  norm_num at hd

end ProjectionPhysics.ChainClosure
