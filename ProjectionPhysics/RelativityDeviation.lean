-- ProjectionPhysics — RelativityDeviation：相对论公式的差值项（mathlib 版）
--
-- leo（2026-08-11）：我们构造的相对论公式里面应该多了一个
--   矢量光速和质量物体速度的差值。
--
-- 分析：传统相对论中 v = 物质相对观测者速度，c = 光速（绝对）。
--   新假设下：c = 空间本身的流动速度（矢量光速），物质偏离空间流动。
--   ⟹ 关键量是差值 (c − v) = 空间流动 − 物质速度：
--     · 经典速度合成（伽利略）：w = c − v（差值显式出现）
--     · 相对论速度加法：w = (c−v)/(1−cv/c²)（差值在分子）
--       ⟹ 恒等于 c（★ 差值被分母精确抵消 = 光速不变的代数根源）
--     · 洛伦兹因子：γ² = 1/(1−v²/c²)，v = c−u 时
--       γ² = 1/(2u/c − u²/c²)（差值参数化）
--       u=0（光子完全随空间）⟹ 分母 0 ⟹ γ=∞ ⟹ dτ=0（不花时间）
--       u=c（物质静止）⟹ γ=1
--
-- 定理（mathlib）：
--   RD1  photon_velocity_sum_invariant: (c−v)/(1−cv/c²) = c（光速不变=差值抵消）
--   RD2  galilean_difference: 经典合成 w = c − v（差值显式）
--   RD3  gammaSq_eq_deviation_form: γ²(c, v) = γ²_dev(c, c−v)（差值参数化等价）
--   RD4  photon_gamma_diverges: u=0 ⟹ 1−(c−u)²/c² = 0（γ=∞, dτ=0）
--   RD5  rest_gamma_one: u=c ⟹ 1−(c−u)²/c² = 1（γ=1, 正常时间）

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
namespace RelativityDeviation

/-! ### 速度合成：差值项的角色 -/

/-- 经典（伽利略）速度合成：光子相对空间 c，物质相对观测者 v（同向相减）⟹
    观测者测光子 w = c − v（★ 差值项显式出现）。 -/
def galileanDiff (c v : ℝ) : ℝ := c - v

/-- 相对论速度加法（同向相减情形）：w = (c−v)/(1−cv/c²)。 -/
def relativisticDiff (c v : ℝ) : ℝ := (c - v) / (1 - c * v / c^2)

/-- ★ RD1：相对论速度加法下，光子速度恒为 c——
    分子中的差值 (c−v) 被分母 (1−v/c) 精确抵消。
    （"公式里多了一个矢量光速和质量物体速度的差值"：
     差值确实出现，但被分母消灭 ⟹ 光速不变） -/
theorem photon_velocity_sum_invariant (c v : ℝ) (hc : c ≠ 0) (hv : v ≠ c) :
    relativisticDiff c v = c := by
  unfold relativisticDiff
  -- 约去 (c−v)：先证 c−v ≠ 0
  have hcv : c - v ≠ 0 := by
    intro hz
    apply hv
    linarith
  field_simp [hc, hcv]
/-- ★ RD2：经典与相对论之差——
    w_经典 = c − v（差值显式，光速依赖观测者速度）
    w_相对论 = c（差值被抵消，光速不变）
    差值项 (c−v) 是经典极限的产物，相对论把它消除。 -/
theorem galilean_vs_relativistic (c v : ℝ) (hc : c ≠ 0) (hv : v ≠ c) :
    galileanDiff c v ≠ relativisticDiff c v → v ≠ 0 := by
  -- 若 v = 0 则两者都是 c
  intro hneq hzero
  apply hneq
  simp [galileanDiff, relativisticDiff, hzero]

/-! ### 洛伦兹因子的差值参数化 -/

/-- 洛伦兹因子平方（标准）：γ²(v) = 1/(1−v²/c²)。 -/
def gammaSq (c v : ℝ) : ℝ := 1 / (1 - v^2 / c^2)

/-- 洛伦兹因子平方（差值参数化）：v = c − u（u = 物质相对空间流动的偏离量），
    γ²(u) = 1/(1−(c−u)²/c²) = 1/(2u/c − u²/c²)。 -/
def gammaSqDeviation (c u : ℝ) : ℝ := 1 / (1 - (c - u)^2 / c^2)

/-- ★ RD3：两种参数化等价——γ²(c, c−u) = γ²_dev(c, u)。
    （差值参数化不是新公式，是同一公式用 (c−v) 重写） -/
theorem gammaSq_eq_deviation_form (c u : ℝ) (hc : c ≠ 0) :
    gammaSq c (c - u) = gammaSqDeviation c u := by
  unfold gammaSq gammaSqDeviation
  congr 1

/-- ★ RD4：光子完全随空间（u = 0）⟹ γ² 分母为 0 ⟹ γ = ∞ ⟹ dτ = 0。
    "无质量视角下是空间本身在运动，所以不花时间"的代数形式。 -/
theorem photon_gamma_diverges (c : ℝ) (hc : c ≠ 0) :
    1 - (c - 0)^2 / c^2 = 0 := by
  field_simp [hc]
  ring
/-- ★ RD5：物质静止（u = c，相对空间流动偏离 = 光速）⟹ γ² 分母为 1 ⟹ γ = 1。
    静止物质经历正常时间（dτ = dt）。 -/
theorem rest_gamma_one (c : ℝ) (hc : c ≠ 0) :
    1 - (c - c)^2 / c^2 = 1 := by
  field_simp [hc]
  ring

/-- RD6：差值参数化的分母恒等式——1−(c−u)²/c² = u(2c−u)/c²。
    u=0 ⟹ 0（光子）；u=c ⟹ 1（静止）；0<u<c ⟹ 0<·<1（质量物体）。 -/
theorem deviation_denominator (c u : ℝ) (hc : c ≠ 0) :
    1 - (c - u)^2 / c^2 = (2 * c * u - u^2) / c^2 := by
  field_simp [hc]
  ring

/-- RD7：质量物体（0 < u < c）⟹ γ² 分母为正（0 < 2cu − u²）。
    这保证 γ² > 0（有限），与 RD4 的光子极限（分母 = 0）区分。 -/
theorem massive_deviation_positive_denominator (c u : ℝ)
    (hc : 0 < c) (hu : 0 < u) (huc : u < c) :
    0 < 2 * c * u - u^2 := by
  -- 2cu − u² = u(2c−u)；u > 0 且 2c−u > 0
  have h2c : 0 < 2 * c - u := by
    nlinarith [huc, hc]
  nlinarith [hu, h2c]

end RelativityDeviation
