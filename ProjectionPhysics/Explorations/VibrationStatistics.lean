-- ProjectionPhysics — VibrationStatistics：振动闭包 ⟹ 费米/玻色（探索）
--
-- leo（2026-10-01）问题：
--   「把费米子和玻色子的基本属性用量子场论描述，通过我的方法实现会怎么样？
--    量子力学里所有粒子本身是一个场——有没有可能只是因为振动频率不同产生了
--    不同的场，但实际上所有的场都是同一种场？」
--
-- 本模块把这个问题拆成**一个可证的命题**：
--   场是否同一种 ⟹ 见 GQF2/FM（仓库已是「四力合一单场」）；
--   费米/玻色的差别**不是** ω（能量频率）而是**闭包的相因子 σ**：
--      σ = +1 ⟹ 玻色型（旋转 2π 复原）
--      σ = −1 ⟹ 费米型（旋转 2π 变号，必须 4π 才复原）
--      σ ∈ ℂ  一般（|σ| = 1）⟹ 任意子（分数统计）
--   相因子在**逐股相乘下可乘（= 统计相位相加）**，于是 ℤ₂ 群律
--   （玻色×玻色=玻色、玻色×费米=费米、费米×费米=玻色）自动成立
--   ——这正是「同一种场、不同振动」能走到的最远处。
--
--   显式见证（振动本体）：半角螺旋 θ ↦ (cos(θ/2), sin(θ/2)) 是费米型
--   （2π 变号 ⟹ 4π 复原）；全角螺旋 θ ↦ (cos θ, sin θ) 是玻色型。
--   ——两者是**同一个振动**，只差基础周期（4π vs 2π）。
--
-- 诚实边界：
--   · 闭包相因子是**定义选择**（把「统计性」翻译成闭合相因子），不是公理推出；
--     它与 SFS5（Cℓ(3) 最小表示 2 维 / SU(2) 双重覆盖 / 2π 变号）同构，
--     但本模块不重证 SFS —— 只把它提炼成「一个相因子」。
--   · **ω 与统计性正交**：本模块证的是「统计性只由闭包相因子决定」；
--     ω 是否恰好整数/半整数 ⟹ 玻色/费米 —— 那是**绕数**不是能量频率
--     （数值层 N1/N4 钉死：同一个 ω 下光子（秩1）与电子（秩2）并存）。
--   · 耗散：闭包缺陷 ε := f(θ+2π) − σ f(θ)；ε ≡ 0 ⟺ 守恒（GQC1 的信息守恒）；
--     ε ≠ 0 的**来源**= 仓库的「第二输入缺口」（未变）。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProjectionPhysics.VibrationStatistics

/-- 闭包相因子：振动 f 在**旋转 2π** 后按相因子 σ 变换。
    σ = 1 玻色型；σ = −1 费米型；一般 σ（|σ|=1）任意子。 -/
noncomputable def ClosureFactor (f : ℝ → ℂ) (σ : ℂ) : Prop :=
  ∀ θ : ℝ, f (θ + 2 * Real.pi) = σ * f θ

/-- 玻色型：旋转 2π 复原（整数绕数）。 -/
def IsBosonicF (f : ℝ → ℂ) : Prop := ClosureFactor f 1

/-- 费米型：旋转 2π 变号（半整数绕数 ⟹ 必须 4π 才复原）。 -/
def IsFermionicF (f : ℝ → ℂ) : Prop := ClosureFactor f (-1)

/-- 闭包缺陷：ε(θ) = f(θ+2π) − σ f(θ)。ε ≡ 0 ⟺ 闭包（守恒）；ε ≠ 0 = 耗散。 -/
noncomputable def ClosureDefect (f : ℝ → ℂ) (σ : ℂ) (θ : ℝ) : ℂ :=
  f (θ + 2 * Real.pi) - σ * f θ

-- ---------------------------------------------------------------------------
-- VBS1：两圈闭包 —— σ² 因子（费米型 σ²=1 ⟹ 4π 复原）
-- ---------------------------------------------------------------------------

theorem closure_two_turns (f : ℝ → ℂ) (σ : ℂ) (h : ClosureFactor f σ) :
    ∀ θ : ℝ, f (θ + 4 * Real.pi) = (σ * σ) * f θ := by
  intro θ
  have h1 : f (θ + 2 * Real.pi) = σ * f θ := h θ
  have h2 : f ((θ + 2 * Real.pi) + 2 * Real.pi) = σ * f (θ + 2 * Real.pi) :=
    h (θ + 2 * Real.pi)
  have harith : θ + 4 * Real.pi = (θ + 2 * Real.pi) + 2 * Real.pi := by ring
  rw [harith, h2, h1]
  ring

-- ---------------------------------------------------------------------------
-- VBS2 ★ 费米型必须两圈复原（4π）——2π 变号 ⟹ 4π 复原
-- ---------------------------------------------------------------------------

theorem fermionic_four_pi (f : ℝ → ℂ) (h : IsFermionicF f) :
    ∀ θ : ℝ, f (θ + 4 * Real.pi) = f θ := by
  intro θ
  have hh := closure_two_turns f (-1) h θ
  rw [hh]
  ring

-- ---------------------------------------------------------------------------
-- VBS3 ★ 玻色型与费米型互斥（除非恒为 0）——统计性的 ℤ₂ 二分
-- ---------------------------------------------------------------------------

theorem not_bosonic_and_fermionic (f : ℝ → ℂ) (hb : IsBosonicF f)
    (hf : IsFermionicF f) : ∀ θ : ℝ, f θ = 0 := by
  intro θ
  have h1 : f (θ + 2 * Real.pi) = 1 * f θ := hb θ
  have h2 : f (θ + 2 * Real.pi) = (-1) * f θ := hf θ
  have h6 : (2 : ℂ) * f θ = 0 := by
    calc (2 : ℂ) * f θ = (1 : ℂ) * f θ - (-1 : ℂ) * f θ := by ring
      _ = f (θ + 2 * Real.pi) - f (θ + 2 * Real.pi) := by rw [← h1, ← h2]
      _ = 0 := by ring
  exact (mul_eq_zero.mp h6).resolve_left (by norm_num)

-- ---------------------------------------------------------------------------
-- VBS4 ★★ 统计相位可加：逐股相乘 ⟹ 相因子相乘
--        （「同一种场 + 不同振动」的代数内核）
-- ---------------------------------------------------------------------------

theorem closure_factor_mul (f g : ℝ → ℂ) (σ τ : ℂ)
    (hf : ClosureFactor f σ) (hg : ClosureFactor g τ) :
    ClosureFactor (fun θ => f θ * g θ) (σ * τ) := by
  intro θ
  show f (θ + 2 * Real.pi) * g (θ + 2 * Real.pi) = (σ * τ) * (f θ * g θ)
  rw [hf θ, hg θ]
  ring

-- ---------------------------------------------------------------------------
-- VBS5 ★ ℤ₂ 群律（玻色/费米的组合代数）
-- ---------------------------------------------------------------------------

theorem bosonic_mul_bosonic (f g : ℝ → ℂ) (hf : IsBosonicF f) (hg : IsBosonicF g) :
    IsBosonicF (fun θ => f θ * g θ) := by
  have h := closure_factor_mul f g 1 1 hf hg
  simpa using h

theorem bosonic_mul_fermionic (f g : ℝ → ℂ) (hf : IsBosonicF f) (hg : IsFermionicF g) :
    IsFermionicF (fun θ => f θ * g θ) := by
  have h := closure_factor_mul f g 1 (-1) hf hg
  simpa using h

theorem fermionic_mul_fermionic (f g : ℝ → ℂ) (hf : IsFermionicF f) (hg : IsFermionicF g) :
    IsBosonicF (fun θ => f θ * g θ) := by
  have h := closure_factor_mul f g (-1) (-1) hf hg
  simpa using h

-- ---------------------------------------------------------------------------
-- VBS6 ★ n 股相因子 σⁿ ⟹ 奇偶律（奇数股费米仍是费米，偶数股费米是玻色）
-- ---------------------------------------------------------------------------

theorem closure_factor_pow (f : ℝ → ℂ) (σ : ℂ) (h : ClosureFactor f σ) :
    ∀ n : ℕ, ClosureFactor (fun θ => (f θ) ^ n) (σ ^ n) := by
  intro n
  induction n with
  | zero => intro θ; simp
  | succ k _ih =>
      intro θ
      show (f (θ + 2 * Real.pi)) ^ (k + 1) = (σ ^ (k + 1)) * (f θ) ^ (k + 1)
      rw [h θ, mul_pow]

/-- ★ 偶数股费米型 = 玻色型（费米子成对 ⟹ 玻色子，ℤ₂ 的直接后果）。 -/
theorem even_fermion_strands_bosonic (f : ℝ → ℂ) (h : IsFermionicF f) (k : ℕ) :
    IsBosonicF (fun θ => (f θ) ^ (2 * k)) := by
  have hh := closure_factor_pow f (-1) h (2 * k)
  have hσ : (-1 : ℂ) ^ (2 * k) = 1 := Even.neg_one_pow ⟨k, by ring⟩
  rw [hσ] at hh
  simpa using hh

/-- ★ 奇数股费米型仍是费米型。 -/
theorem odd_fermion_strands_fermionic (f : ℝ → ℂ) (h : IsFermionicF f) (k : ℕ) :
    IsFermionicF (fun θ => (f θ) ^ (2 * k + 1)) := by
  have hh := closure_factor_pow f (-1) h (2 * k + 1)
  have hσ : (-1 : ℂ) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, by ring⟩
  rw [hσ] at hh
  simpa using hh

-- ---------------------------------------------------------------------------
-- VBS7 ★★ 显式振动见证：半角螺旋 = 费米型；全角螺旋 = 玻色型
--         （两者的差别只是**基础周期** 4π vs 2π —— 「振动本身」）
-- ---------------------------------------------------------------------------

/-- 半角螺旋（截面相位 θ/2）：基础周期 4π —— 费米型振动。 -/
noncomputable def halfAngleHelix : ℝ → ℂ := fun θ => ⟨Real.cos (θ / 2), Real.sin (θ / 2)⟩

/-- 全角螺旋（截面相位 θ）：基础周期 2π —— 玻色型振动。 -/
noncomputable def fullAngleHelix : ℝ → ℂ := fun θ => ⟨Real.cos θ, Real.sin θ⟩

theorem halfAngleHelix_fermionic : IsFermionicF halfAngleHelix := by
  intro θ
  have hx : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by ring
  have hc : Real.cos ((θ + 2 * Real.pi) / 2) = -Real.cos (θ / 2) := by
    rw [hx, Real.cos_add_pi]
  have hs : Real.sin ((θ + 2 * Real.pi) / 2) = -Real.sin (θ / 2) := by
    rw [hx, Real.sin_add_pi]
  show (⟨Real.cos ((θ + 2 * Real.pi) / 2), Real.sin ((θ + 2 * Real.pi) / 2)⟩ : ℂ)
      = (-1 : ℂ) * ⟨Real.cos (θ / 2), Real.sin (θ / 2)⟩
  rw [hc, hs]
  apply Complex.ext <;> simp

theorem fullAngleHelix_bosonic : IsBosonicF fullAngleHelix := by
  intro θ
  have hx : θ + 2 * Real.pi = (θ + Real.pi) + Real.pi := by ring
  have hc : Real.cos (θ + 2 * Real.pi) = Real.cos θ := by
    rw [hx, Real.cos_add_pi, Real.cos_add_pi, neg_neg]
  have hs : Real.sin (θ + 2 * Real.pi) = Real.sin θ := by
    rw [hx, Real.sin_add_pi, Real.sin_add_pi, neg_neg]
  show (⟨Real.cos (θ + 2 * Real.pi), Real.sin (θ + 2 * Real.pi)⟩ : ℂ)
      = 1 * ⟨Real.cos θ, Real.sin θ⟩
  rw [hc, hs]
  simp

-- ---------------------------------------------------------------------------
-- VBS8 ★ 耗散 = 闭包缺陷（守恒 ⟺ ε ≡ 0）
-- ---------------------------------------------------------------------------

theorem closureDefect_zero_iff (f : ℝ → ℂ) :
    (∀ θ : ℝ, ClosureDefect f 1 θ = 0) ↔ IsBosonicF f := by
  constructor
  · intro h θ
    have hθ := h θ
    simp only [ClosureDefect, one_mul, sub_eq_zero] at hθ
    simpa using hθ
  · intro h θ
    have hθ : f (θ + 2 * Real.pi) = 1 * f θ := h θ
    simp only [ClosureDefect]
    rw [hθ]
    ring

/-- ★ 闭包 ⟹ 任意整数步守恒（守恒不是一步的事，是所有步）。 -/
theorem closure_arbitrary_steps (f : ℝ → ℂ) (h : IsBosonicF f) :
    ∀ (n : ℕ) (θ : ℝ), f (θ + (n : ℝ) * (2 * Real.pi)) = f θ := by
  intro n
  induction n with
  | zero => intro θ; simp
  | succ k ih =>
      intro θ
      have hstep : f (θ + (k : ℝ) * (2 * Real.pi) + 2 * Real.pi)
          = f (θ + (k : ℝ) * (2 * Real.pi)) := by
        have hk := h (θ + (k : ℝ) * (2 * Real.pi))
        simpa using hk
      have harith : θ + ((Nat.succ k : ℕ) : ℝ) * (2 * Real.pi)
          = θ + (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
        push_cast; ring
      rw [harith, hstep, ih θ]

end ProjectionPhysics.VibrationStatistics
