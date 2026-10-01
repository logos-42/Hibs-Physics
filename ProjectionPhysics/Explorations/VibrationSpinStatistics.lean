-- ProjectionPhysics — VibrationSpinStatistics：把 σ ∈ {±1} 从「定义」升级成「定理」
--
-- 缺口 A（上一轮 VBS / VBC 登记的：「为什么自然界只取 σ = ±1 这个二元子群，
-- 而不是一般任意子相」）。本模块把它推出来。
--
-- ── 推导链（三块已有碎料 + 一条角色性）────────────────────────────────────
--
--   碎料 1（相位是角色）：两次连续旋转的相位相乘 ⟹ g(a+b) = g(a)·g(b)。
--           这不是新公设——它是「相位」这个概念本身的要求（相位可加 ⟹ 取指数后相乘）。
--           VBS4（统计相位可加）是它的另一面。
--   碎料 2（SU(2) 双覆盖 / 4π 复原）：g(4π) = 1。这是 SFS5 的内容
--           （Cℓ(3) 最小表示 2 维 ⟹ SU(2) 双重覆盖；数值层 e^{2iπσ₁} = I）。
--           同时它也是「三方向（3D）」的后果：π₁(SO(3)) = ℤ₂（3D 旋转群的基本群是二元群），
--           所以闭路的类只有两种，相位只能取两个值；2D 才是 π₁(SO(2)) = ℤ（任意子的来源）。
--
--   ⟹ 核心定理（VSS3）：σ := g(2π) 满足 σ² = g(4π) = 1 ⟹ **σ = +1 或 σ = −1**。
--   ⟹ 推论（VSS4）：**任意子被排除** —— σ² = 1 在 ℂ 中只有 ±1 两个解。
--   ⟹ 推论（VSS5/VSS6）：σ=+1 ⟹ g 以 2π 为周期（单值 ⟹ 降到 SO(3) ⟹ 玻色型）；
--                        σ=−1 ⟹ g(θ+2π) = −g(θ) 且 g(θ+4π) = g(θ)（真双值 ⟹ 费米型）。
--   ⟹ 直连 VBS（VSS7）：只用 VBS 的闭包定义 + 4π 复原，就能得出 σ = ±1。
--
-- ── 诚实边界（写死）───────────────────────────────────────────────────────
--   · 本模块**不**引入新公设、**不**引入新标度；全仓库无 `axiom`。
--   · 拓扑前提 π₁(SO(3)) = ℤ₂ **未形式化**（那需要代数拓扑）。仓库里与之等价、
--     且**已有**的形式是「4π 复原」（SFS5 / 双重覆盖），本模块用它作前提。
--   · 标准 Pauli 自旋-统计定理的另一半——「相因子 ⟹ 场算符反对易」——需要**场算符**
--     语言（QFT 公理：微观因果 + 正定性），仓库里没有；那一半**不在本模块里**，也未闭合。
--   · GQC2（格点化 ⟹ 光锥 ⟹ 不可通信）的角色是**许可性**的（它保证闭包相位是态自身的
--     角色、而不是环境的函数），不是本定理的证明前提——这一点更正了上一轮把它列为
--     「三块碎料之一」的说法：真正的第三块是**三方向（P3）**，不是 GQC2。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import ProjectionPhysics.Explorations.VibrationStatistics

namespace ProjectionPhysics.VibrationSpinStatistics

open ProjectionPhysics.VibrationStatistics

-- ---------------------------------------------------------------------------
-- VSS1 角色性：相位是旋转的角色
-- ---------------------------------------------------------------------------

/-- 旋转相位：态在旋转角 θ 下累积的相位 g(θ)。
    角色性 = g(0)=1（不转则不变）∧ g(a+b) = g(a)·g(b)（两次连续旋转的相位相乘）。
    这是「相位」概念本身的要求（相位可加 ⟹ 取指数后相乘），不是新公设。 -/
def IsRotationPhase (g : ℝ → ℂ) : Prop :=
  g 0 = 1 ∧ ∀ a b : ℝ, g (a + b) = g a * g b

-- ---------------------------------------------------------------------------
-- VSS4（前置）二次单位根只有两个：σ² = 1 ⟹ σ = ±1
-- ---------------------------------------------------------------------------

/-- ★ 在 ℂ 中，σ² = 1 只有两个解：σ = 1 或 σ = −1。
    —— 这就是**任意子被排除**的代数内核（任意子相 σ = e^{iθ} 一般不满足 σ² = 1）。 -/
theorem sq_one_two_values (σ : ℂ) (h : σ * σ = 1) : σ = 1 ∨ σ = -1 := by
  have hfac : (σ - 1) * (σ + 1) = 0 := by
    have : (σ - 1) * (σ + 1) = σ * σ - 1 := by ring
    rw [this, h]; ring
  rcases mul_eq_zero.mp hfac with h1 | h2
  · left
    calc σ = σ - 1 + 1 := by ring
      _ = 0 + 1 := by rw [h1]
      _ = 1 := by ring
  · right
    calc σ = σ + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h2]
      _ = -1 := by ring

-- ---------------------------------------------------------------------------
-- VSS2 角色性 + 4π 复原 ⟹ σ² = 1
-- ---------------------------------------------------------------------------

theorem closure_phase_sq_one (g : ℝ → ℂ) (hg : IsRotationPhase g)
    (h4 : g (4 * Real.pi) = 1) :
    g (2 * Real.pi) * g (2 * Real.pi) = 1 := by
  have h := hg.2 (2 * Real.pi) (2 * Real.pi)
  have harith : 2 * Real.pi + 2 * Real.pi = 4 * Real.pi := by ring
  rw [harith, h4] at h
  exact h.symm

-- ---------------------------------------------------------------------------
-- VSS3 ★★ 核心定理：σ 只能取 ±1
-- ---------------------------------------------------------------------------

/-- ★★ **自旋-统计的代数内核**：角色性（相位相乘）+ SU(2) 双覆盖（旋转 4π 复原，SFS5）
    ⟹ 闭包相因子 σ := g(2π) **只能是 +1 或 −1**。

    这就是把「σ ∈ {±1}」从**定义**升级成**定理**的那一步。
    两个前提都不是新公设：角色性是相位概念本身的要求，4π 复原是 SFS5/双覆盖。 -/
theorem closure_phase_two_values (g : ℝ → ℂ) (hg : IsRotationPhase g)
    (h4 : g (4 * Real.pi) = 1) :
    g (2 * Real.pi) = 1 ∨ g (2 * Real.pi) = -1 :=
  sq_one_two_values _ (closure_phase_sq_one g hg h4)

-- ---------------------------------------------------------------------------
-- VSS5 / VSS6 两个分支的物理身份
-- ---------------------------------------------------------------------------

/-- ★ σ = +1 ⟹ g 以 2π 为周期（**单值** ⟹ 可降到 SO(3) ⟹ 玻色型）。 -/
theorem bosonic_descends (g : ℝ → ℂ) (hg : IsRotationPhase g)
    (h : g (2 * Real.pi) = 1) :
    ∀ θ : ℝ, g (θ + 2 * Real.pi) = g θ := by
  intro θ
  have hh := hg.2 θ (2 * Real.pi)
  rw [hh, h, mul_one]

/-- ★ σ = −1 ⟹ g(θ+2π) = −g(θ) 且 g(θ+4π) = g(θ)：
    **真双值**（不降到 SO(3)，只在 SU(2) 上单值）⟹ 费米型。
    ——这正是 VBS2「2π 变号、4π 复原」在角色语言下的形式。 -/
theorem fermionic_double_valued (g : ℝ → ℂ) (hg : IsRotationPhase g)
    (h : g (2 * Real.pi) = -1) :
    (∀ θ : ℝ, g (θ + 2 * Real.pi) = -g θ) ∧ (∀ θ : ℝ, g (θ + 4 * Real.pi) = g θ) := by
  have h4 : g (4 * Real.pi) = 1 := by
    have hh := hg.2 (2 * Real.pi) (2 * Real.pi)
    have harith : 2 * Real.pi + 2 * Real.pi = 4 * Real.pi := by ring
    rw [harith] at hh
    rw [hh, h]; ring
  constructor
  · intro θ
    have hh := hg.2 θ (2 * Real.pi)
    rw [hh, h]; ring
  · intro θ
    have hh := hg.2 θ (4 * Real.pi)
    rw [hh, h4, mul_one]

-- ---------------------------------------------------------------------------
-- VSS7 ★ 直连 VBS：只用「闭包」+「4π 复原」，也得出 σ = ±1
-- ---------------------------------------------------------------------------

/-- ★ 从 VBS 的闭包定义 + 4π 复原（非零态）直接得 σ = ±1，不需要角色性：
    f(θ+4π) = σ²·f(θ)（VBS1 closure_two_turns）与 f(θ+4π) = f(θ) 联立 ⟹ σ² = 1 ⟹ σ = ±1。
    ——这是与 VSS3 平行的第二条路，走的是仓库自己的闭包语言。 -/
theorem closure_factor_two_values (f : ℝ → ℂ) (σ : ℂ) (h : ClosureFactor f σ)
    (h4 : ∀ θ : ℝ, f (θ + 4 * Real.pi) = f θ) (θ₀ : ℝ) (hne : f θ₀ ≠ 0) :
    σ = 1 ∨ σ = -1 := by
  have h2 := closure_two_turns f σ h θ₀
  rw [h4 θ₀] at h2
  have htmp : (σ * σ) * f θ₀ = f θ₀ := h2.symm
  have hz : (σ * σ - 1) * f θ₀ = 0 := by
    rw [sub_mul, one_mul, htmp]; ring
  have hss : σ * σ - 1 = 0 := (mul_eq_zero.mp hz).resolve_right hne
  exact sq_one_two_values σ (sub_eq_zero.mp hss)

-- ---------------------------------------------------------------------------
-- VSS8 角色 ⟹ VBS 闭包（接口定理）
-- ---------------------------------------------------------------------------

/-- ★ 接口：若态 f 按旋转角色 g 变换（f(θ) = g(θ)·f(0)），则 f 的闭包相因子 = g(2π)。
    ——把「角色」与 VBS 的「闭包相因子」接上：**σ 就是 2π 旋转的相位**。 -/
theorem rotation_phase_gives_closure (f g : ℝ → ℂ) (hg : IsRotationPhase g)
    (hf : ∀ θ : ℝ, f θ = g θ * f 0) :
    ClosureFactor f (g (2 * Real.pi)) := by
  intro θ
  have h1 : f (θ + 2 * Real.pi) = g (θ + 2 * Real.pi) * f 0 := hf _
  have h2 : g (θ + 2 * Real.pi) = g θ * g (2 * Real.pi) := hg.2 θ (2 * Real.pi)
  rw [h1, h2, hf θ]
  ring

end ProjectionPhysics.VibrationSpinStatistics
