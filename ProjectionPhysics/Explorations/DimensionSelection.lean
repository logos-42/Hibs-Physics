-- ProjectionPhysics — DimensionSelection：「振动 ⟹ 三方向」的唯一性论证（DS1–DS8）
--
-- leo（2026-10-01）：先做第二条（账本更正，已推送），再做第一条（本模块）。
-- leo 原话：「说方向 A 是可以实现核心的假设推论的，能把我的假设推到第一性原理的层面」。
--
-- ── 与上一版（口头的「最小性」）的区别 ─────────────────────────────────────
--   上一版把最后一步写成**最小性**（「选最小的自洽维数」）——那是**口味选择**，排除不掉 d = 4, 5…
--   本模块换成**唯一性**：两条**硬要求**的交集只落在 3 上，不涉及偏好。
--
-- ── 两条要求（各带来源；两者都是标准事实的**陈述**，本模块不证明它们） ──────
--   **R1 统计性只有两类**（排除任意子）
--     · 标准事实：π₁(C_N(ℝ^d)) 的阿贝尔化 —— d = 2 时 ≅ ℤ（任意子合法、取之不尽），
--       d ≥ 3 时 ≅ ℤ₂（只有两类）。Fox–Neuwirth 1962, Math. Scand. 10, 119。
--     · 经验支持：**任意子只在二维材料里被观测到** ⟹ 统计性的维度依赖是真的。
--     · 本模块能证的部分（真定理）：**ℤ 型群的相位排除不掉第三类取值**
--       （`Z_char_not_two_valued`，α = π/3 见证，im = √3/2 ≠ 0）；
--       **ℤ₂ 型群的相位只能是 ±1**（复用 ES5 `two_class_phase_values`）。
--   **R2 连接数/扭转必须非平凡**（仓库的质量机制需要）
--     · 标准事实：d ≥ 4 时所有环都平凡、任何两个不相交的圆都不相连；
--       d = 2 时两条闭曲线不能互连（第三维不存在）。**只有 d = 3 有非平凡链环数。**
--     · 这是仓库自己的质量机制的前提：环扭转 ⟹ N ⟹ m² = N·M₀²（RT1–RT7）。
--   ⟹ **交集 = {3}**（不是「最小的」）。
--
-- ── 本模块声明 ────────────────────────────────────────────────────────────
--   DS1 ★★  `Z_char_not_two_valued` —— ℤ 型群的相位**不落在 ±1 上**（α = π/3；真定理）
--   DS2      `circleCharacter_one` —— χ_α(1) = exp(α·i)（工具引理）
--   DS3 ★★  `R1_algebraic_core` —— R1 的代数核 = DS1 ∧ ES5（两条合起来）
--   DS4-5    `TwoClassStatistics` / `NonTrivialLinking`（两条要求的**陈述**，带来源）
--   DS6      `dim_two_fails_statistics` / `dim_four_fails_linking`（反例各一）
--   DS7 ★★★ `dimension_is_three` + `dimension_characterization` —— **唯一性主定理**
--   DS8 ★★  `both_requirements_needed` —— 两条都不可省（否则论证是空的）
--
-- ── 死法（写死） ──────────────────────────────────────────────────────────
--   若在 d ≠ 3 里找到**等价自洽**的表述——(a) d = 2 加一个只给 ±1 的机制（即把 R1 换成
--   别的来源），或 (b) d ≥ 4 有非平凡替代品（如高维面纽结给出非平凡「扭转」）——则本论证**死**。
--   注意本论证**不排除** d = 2 作为一个整体自洽的物理（2+1 维任意子物理确实自洽）；
--   它只说：**同时**要「只有两类统计性」和「非平凡扭转」时，只有 3 满足。
--
-- ── 诚实边界 ─────────────────────────────────────────────────────────────
--   · **R1/R2 两条要求本身没有形式化**（需要代数拓扑：配置空间、辫群、Fox–Neuwirth；
--     以及链环理论）。本模块把它们抽成 `3 ≤ d` / `d ≤ 3` 两个**定义**，并在 docstring 里带来源。
--   · 因此 DS7 的证明是 `le_antisymm`——**全部重量在那两条定义上**。这与 ES8 同一个模式：
--     把无法形式化的输入**显式、不可偷渡**地放进类型。
--   · 真定理只有 DS1（ℤ 型角色不落在 ±1）与 DS3（把它与 ES5 合并）。
--   · **这不是「把 P3 变成推论」**——因为 R1/R2 还是输入。它做的是把「维数 = 3」从一个
--     **公设**（P3「三方向」）换成**两条可分别判死的要求的交**。收窄了输入的性质，没有消掉输入。
--   · 零新可检验预言。

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ProjectionPhysics.Explorations.ExchangeStatistics
import ProjectionPhysics.Explorations.VibrationSpinStatistics

noncomputable section

namespace ProjectionPhysics.DimensionSelection

open ProjectionPhysics.ExchangeStatistics

-- ---------------------------------------------------------------------------
-- DS2 工具引理
-- ---------------------------------------------------------------------------

/-- DS2：`χ_α(1) = exp(α·i)`（`χ_α(n) = exp(α·n·i)` 在 n = 1 处）。 -/
theorem circleCharacter_one (α : ℝ) :
    circleCharacter α 1 = Complex.exp ((α : ℂ) * Complex.I) := by
  unfold circleCharacter
  simp

/-- `exp(α·i)` 的虚部（α = π/3 时 = √3/2）。 -/
theorem im_exp_pi_div_three :
    Complex.im (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)) = Real.sqrt 3 / 2 := by
  rw [Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Real.exp_zero, Real.sin_pi_div_three]

-- ---------------------------------------------------------------------------
-- DS1 ★★ ℤ 型群的相位排除不掉第三类取值
-- ---------------------------------------------------------------------------

/-- ★★ DS1：**二维的闭路角色不能被限制在 ±1 上** —— α = π/3 处相位 = exp(iπ/3)，
    虚部 = √3/2 ≠ 0，而 ±1 的虚部都是 0。
    ⟹ 「统计性只有两类」这个性质**在 ℤ 型群上不成立** ⟹ 排除不掉任意子。
    （对照 ES5：ℤ₂ 型群上它成立。**同一个方程 χ(2) = χ(1)²，两种群，两个世界。**） -/
theorem Z_char_not_two_valued :
    ∃ α : ℝ, IsLoopPhase (circleCharacter α) ∧
      circleCharacter α 1 ≠ 1 ∧ circleCharacter α 1 ≠ -1 := by
  refine ⟨Real.pi / 3, circleCharacter_is_loop_phase _, ?_, ?_⟩
  · rw [circleCharacter_one]
    intro h
    have h2 := congrArg Complex.im h
    rw [im_exp_pi_div_three] at h2
    simp at h2
  · rw [circleCharacter_one]
    intro h
    have h2 := congrArg Complex.im h
    rw [im_exp_pi_div_three] at h2
    simp at h2

-- ---------------------------------------------------------------------------
-- DS3 ★★ R1 的代数核 = DS1 ∧ ES5
-- ---------------------------------------------------------------------------

/-- ★★ DS3：**R1（统计性只有两类）的代数核** —— 两条合起来才是完整的：
    · ℤ 型群（d = 2）：存在非 ±1 的相取值（DS1，本模块真定理）；
    · ℤ₂ 型群（d ≥ 3）：只能 ±1（复用 ES5 `two_class_phase_values`）。
    ⟹ 「只有两类」这条性质**恰好把 ℤ 排除掉**。 -/
theorem R1_algebraic_core :
    (∃ α : ℝ, IsLoopPhase (circleCharacter α) ∧
        circleCharacter α 1 ≠ 1 ∧ circleCharacter α 1 ≠ -1) ∧
    (∀ χ : ℤ → ℂ, IsTwoClassPhase χ → χ 1 = 1 ∨ χ 1 = -1) :=
  ⟨Z_char_not_two_valued, fun _ h => two_class_phase_values _ h⟩

-- ---------------------------------------------------------------------------
-- DS4-5 两条要求（陈述 + 来源；本模块不证明它们）
-- ---------------------------------------------------------------------------

/-- **R1 统计性只有两类**（排除任意子）。
    来源（标准事实，未形式化）：π₁(C_N(ℝ^d)) 的阿贝尔化 —— d = 2 时 ≅ ℤ，d ≥ 3 时 ≅ ℤ₂
    （Fox–Neuwirth 1962）。经验支持：任意子只在二维材料里被观测到。
    ⟹ 本定义是这条标准事实的**陈述**，不是本模块的定理。 -/
def TwoClassStatistics (d : ℕ) : Prop := 3 ≤ d

/-- **R2 连接数/扭转非平凡**（仓库质量机制的前提）。
    来源（标准事实，未形式化）：d ≥ 4 时所有环都平凡、任何两个不相交的圆都不相连；
    d = 2 时两条闭曲线不能互连。只有 d = 3 有非平凡链环数。 -/
def NonTrivialLinking (d : ℕ) : Prop := d ≤ 3

-- ---------------------------------------------------------------------------
-- DS6 反例各一
-- ---------------------------------------------------------------------------

/-- DS6a：d = 2 不满足 R1（二维给 ℤ ⟹ 任意子合法、无法排除）。 -/
theorem dim_two_fails_statistics : ¬ TwoClassStatistics 2 := by
  simp [TwoClassStatistics]

/-- DS6b：d = 4 不满足 R2（四维及以上所有环都平凡）。 -/
theorem dim_four_fails_linking : ¬ NonTrivialLinking 4 := by
  simp [NonTrivialLinking]

/-- DS6c：d = 3 两条都满足。 -/
theorem dim_three_satisfies_both : TwoClassStatistics 3 ∧ NonTrivialLinking 3 :=
  ⟨le_refl 3, le_refl 3⟩

-- ---------------------------------------------------------------------------
-- DS7 ★★★ 唯一性主定理
-- ---------------------------------------------------------------------------

/-- ★★★ DS7a：**两条要求的交 ⟹ d = 3（唯一）**。
    R1 给下界 3 ≤ d，R2 给上界 d ≤ 3，合起来 d = 3。
    **诚实**：证明是 `le_antisymm`；**全部重量在 DS4/DS5 两条定义**（那才是物理输入）。 -/
theorem dimension_is_three (d : ℕ) (h1 : TwoClassStatistics d) (h2 : NonTrivialLinking d) :
    d = 3 :=
  le_antisymm h2 h1

/-- ★★★ DS7b：**等价刻画** —— 同时满足两条要求 ⟺ d = 3。 -/
theorem dimension_characterization (d : ℕ) :
    (TwoClassStatistics d ∧ NonTrivialLinking d) ↔ d = 3 := by
  constructor
  · intro h
    exact le_antisymm h.2 h.1
  · intro h
    subst h
    exact ⟨le_refl 3, le_refl 3⟩

-- ---------------------------------------------------------------------------
-- DS8 ★★ 两条都不可省
-- ---------------------------------------------------------------------------

/-- ★★ DS8：**两条要求都不可省**（否则论证是空的）：去掉任一条都会放进别的维数。
    去掉 R2 会放进 d = 4, 5, …；去掉 R1 会放进 d = 2。 -/
theorem both_requirements_needed :
    (∃ d : ℕ, TwoClassStatistics d ∧ d ≠ 3) ∧ (∃ d : ℕ, NonTrivialLinking d ∧ d ≠ 3) :=
  ⟨⟨4, by norm_num [TwoClassStatistics], by norm_num⟩,
   ⟨2, by norm_num [NonTrivialLinking], by norm_num⟩⟩

end ProjectionPhysics.DimensionSelection
