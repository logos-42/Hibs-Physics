-- ProjectionPhysics — VibrationClosure：从「空间是振动、并以光速运动」开始推
--
-- leo（2026-10-01）起点（原话）：
--   「空间在振动，和一切本身都是振动，这件事情是一致的。你可以把空间的振动和
--     空间以光速运动本身，理解为一种振动的状态。」
--
-- 本模块把这个起点当作公设面（= SLS1 的振动版），只做一件事：**把相位场在空间中的
-- 两条拓扑路径分开，看能推出什么**。
--
--   θ(x, t) = 相位场（"空间在振动"）；相位以 c 推进（"空间以光速运动"）——同一句话。
--   相位沿一条路径推进。路径只有两种拓扑：
--     (a) 开放路径：相位单调推进、永不回到自身  → 无闭包相因子（IsOpen）
--     (b) 闭合路径：相位沿回路推进、必须回到自身 → 闭包相因子 σ（ClosureFactor）
--
-- 推出的东西（本模块）：
--   VBC1 ★★ 闭合 ⟹ 整数：exp(IΔ) = 1 ⟹ Δ ∈ 2πℤ。
--        「绕数必须整数化」不是公设，是**相位单值性**的直接后果。
--   VBC2 开放模的定义 + 见证（θ ↦ θ 是开放的：无任何 σ 使其闭合）。
--   VBC3 ★ 开放 / 玻色型 / 费米型 三者互斥（开放的振动不可能是闭包型）。
--   VBC4 ★★ 闭合 ⟹ 时间：闭合的相位推进满足 f(θ+n·2π) = σⁿ·f(θ)。
--        即「固有时 = 闭合次数」（n 的每一步 = 一个时间单位）。
--   VBC5 ★ 闭合 ⟹ 有周期：σⁿ = 1 ⟹ f 有周期 n·2π（**周期 = 时间存在的条件**）。
--        VBS2（费米型 4π 复原）是本定理 n = 2、σ = −1 的特例。
--
-- 诚实边界（写死，防后续 session 过度声称）：
--   · 公设面没动：起点仍是 SLS1（空间以 c 运动），本模块只把它的**语言**换成相位场。
--   · VBC1 是拓扑学标准事实（S¹ → S¹ 的映射度是整数）；本模块只是把它写成
--     「绕数整数化」并指出它**给出缺口 C 的整数那一半**。
--   · VBC1 **不给**「相位 = 作用量/ħ」（即 ∮p dq = nħ 里的那个 ħ）——从单值性只能得到
--     **n 是整数**，得不到**量子单位是 ħ**。ħ 的身份仍是输入（详见 wiki §诚实边界）。
--   · 本模块**不**引入任何新公设、**不**引入新标度；全仓库无 `axiom`。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import ProjectionPhysics.Explorations.VibrationStatistics

namespace ProjectionPhysics.VibrationClosure

open ProjectionPhysics.VibrationStatistics

/-- 相位推进的复实现：走一段相位 Δ 后的复值 = exp(iΔ)。 -/
noncomputable def phaseAdvance (Δ : ℝ) : ℂ := Complex.exp (Δ * Complex.I)

-- ---------------------------------------------------------------------------
-- VBC1 ★★ 闭合 ⟹ 整数（绕数整数化）
-- ---------------------------------------------------------------------------

/-- ★★ 若相位走满一圈后复值回到 1（相位闭合），则推进量 Δ 必是 2π 的整数倍。

    ——「绕数必须整数化」**不是公设**，是相位单值性的直接后果。
    这是本轮对缺口 C「绕数为何整数化」的**整数那一半**的形式化关闭。 -/
theorem winding_index_integer (Δ : ℝ) (h : phaseAdvance Δ = 1) :
    ∃ n : ℤ, Δ = n * (2 * Real.pi) := by
  have hx : Complex.exp ((Δ : ℂ) * Complex.I) = 1 := by simpa [phaseAdvance] using h
  rcases (Complex.exp_eq_one_iff.mp hx) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hn' : (Δ : ℂ) * Complex.I = ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
    rw [hn]; ring
  have hΔ : (Δ : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) :=
    mul_right_cancel₀ Complex.I_ne_zero hn'
  have hΔ' : (Δ : ℂ) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
    rw [hΔ]; push_cast; ring
  exact Complex.ofReal_injective hΔ'

/-- VBC1 的逆（存在性方向）：任何 2π 的整数倍推进都是闭合的。 -/
theorem int_mul_two_pi_is_closed (n : ℤ) :
    phaseAdvance (n * (2 * Real.pi)) = 1 := by
  have : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  simp only [phaseAdvance]
  rw [← this]
  exact Complex.exp_int_mul_two_pi_mul_I n

-- ---------------------------------------------------------------------------
-- VBC2 开放模：没有闭包相因子的振动
-- ---------------------------------------------------------------------------

/-- 开放模：不存在任何相因子 σ 使 f 在 2π 旋转下闭合。
    ——「相位一路推进、永不回到自身」= 无内部周期 = 无固有时（光子）。 -/
def IsOpen (f : ℝ → ℂ) : Prop := ¬ ∃ σ : ℂ, ClosureFactor f σ

theorem isOpen_iff (f : ℝ → ℂ) : IsOpen f ↔ ¬ ∃ σ : ℂ, ClosureFactor f σ := Iff.rfl

/-- ★ 开放模的见证：相位本身（f(θ) = θ）是开放的。 -/
theorem phase_itself_is_open : IsOpen (fun θ : ℝ => (θ : ℂ)) := by
  rintro ⟨σ, hσ⟩
  have h0 : ((2 * Real.pi : ℝ) : ℂ) = 0 := by simpa using hσ 0
  have hR : (2 * Real.pi : ℝ) = 0 := Complex.ofReal_injective h0
  linarith [Real.pi_pos]

-- ---------------------------------------------------------------------------
-- VBC3 ★ 三分互斥：开放 / 玻色型 / 费米型
-- ---------------------------------------------------------------------------

theorem open_not_bosonic (f : ℝ → ℂ) (h : IsOpen f) : ¬ IsBosonicF f := by
  intro hb
  exact h ⟨1, hb⟩

theorem open_not_fermionic (f : ℝ → ℂ) (h : IsOpen f) : ¬ IsFermionicF f := by
  intro hf
  exact h ⟨-1, hf⟩

/-- ★ 开放的振动有非零值也不能是闭包型：三类互斥（这就是「光子 / 玻色子 / 费米子」的框架内三分）。 -/
theorem open_excludes_closed (f : ℝ → ℂ) (h : IsOpen f) (σ : ℂ) :
    ¬ ClosureFactor f σ := by
  intro hc
  exact h ⟨σ, hc⟩

-- ---------------------------------------------------------------------------
-- VBC4 ★★ 闭合 ⟹ 时间：f(θ + n·2π) = σⁿ · f(θ)
-- ---------------------------------------------------------------------------

/-- ★★ 闭合模的相位推进可加：每走一个 2π，就乘上一个 σ。
    ——「固有时 = 闭合次数 n」的代数内核：n 的每一步 = 一个时间单位。 -/
theorem clos_translate (f : ℝ → ℂ) (σ : ℂ) (h : ClosureFactor f σ) :
    ∀ (n : ℕ) (θ : ℝ), f (θ + (n : ℝ) * (2 * Real.pi)) = σ ^ n * f θ := by
  intro n
  induction n with
  | zero => intro θ; simp
  | succ k ih =>
      intro θ
      have hstep : f (θ + (k : ℝ) * (2 * Real.pi) + 2 * Real.pi)
          = σ * f (θ + (k : ℝ) * (2 * Real.pi)) := h _
      have harith : θ + ((Nat.succ k : ℕ) : ℝ) * (2 * Real.pi)
          = θ + (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
        push_cast; ring
      rw [harith, hstep, ih θ, pow_succ]
      ring

-- ---------------------------------------------------------------------------
-- VBC5 ★ 闭合 ⟹ 有周期（σⁿ = 1 时）
-- ---------------------------------------------------------------------------

/-- ★ 闭合模在 σ 是 n 次单位根时具有周期 n·2π。
    ——「有周期」= 有内部时钟 = 有时间；VBS2（费米型 4π 复原）是本定理 n = 2、σ = −1 的特例。 -/
theorem clos_periodic_of_root (f : ℝ → ℂ) (σ : ℂ) (n : ℕ)
    (h : ClosureFactor f σ) (hσ : σ ^ n = 1) :
    ∀ θ : ℝ, f (θ + (n : ℝ) * (2 * Real.pi)) = f θ := by
  intro θ
  rw [clos_translate f σ h n θ, hσ, one_mul]

/-- ★ 玻色型（σ = 1）：一拍即复原（周期 2π）。 -/
theorem bosonic_period_two_pi (f : ℝ → ℂ) (h : IsBosonicF f) :
    ∀ θ : ℝ, f (θ + 2 * Real.pi) = f θ := by
  intro θ
  have := h θ
  simpa using this

/-- ★ 费米型（σ = −1）：两拍复原（周期 4π）——**VBS2 的重新表述**。 -/
theorem fermionic_period_four_pi (f : ℝ → ℂ) (h : IsFermionicF f) :
    ∀ θ : ℝ, f (θ + 4 * Real.pi) = f θ :=
  ProjectionPhysics.VibrationStatistics.fermionic_four_pi f h

end ProjectionPhysics.VibrationClosure
