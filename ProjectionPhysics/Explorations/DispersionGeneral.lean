-- ProjectionPhysics — DispersionGeneral：一般色散下的振动坐标（②）
--
-- leo（2026-10-29 四续）优先级 ②：把 VF2 的判据从「线性色散 ω = c·k」推广到**一般色散**，
-- 并把「广」的刻度从相速度换成**群速度**。
--
-- 核心替换（一行代数）：
--
--     线性色散（VF2）：det = k₁k₂(c₁ − c₂)          ← 两个自由参数 c
--     一般色散（本模块）：det = k₁·ω₂ − k₂·ω₁ = k₁k₂(v_ph,2 − v_ph,1)   ← ω_i 任意
--     ⟹ **退化判据仍然只有一句：两带的相速度相同**（GD1/GD2，k ≠ 0）
--
-- 但「快」这个词必须拆成两个：
--     v_ph = ω/k      （相位速度）
--     v_g  = dω/dk    （群速度 —— 包络/涟漪的走速）
-- 二次色散族 ω = c·k + β·k² 上二者都能写闭式：
--     v_ph = c + βk,  v_g = c + 2βk  ⟹ v_g − v_ph = βk   （GD4–GD6）
-- 三条可判死的推论：
--   GD7 ★★★ 线性色散（β = 0）⟹ v_g = v_ph：**AB 轮把两者混用无害**（因为相等）；
--   GD8 ★★★ β ≠ 0 ∧ k ≠ 0 ⟹ v_g ≠ v_ph：一般情形下**不能混用**——
--            「相位速度无界」（AB2）**不能**读成「信号更快」，信号走 v_g。
--   GD9 ★★★ 两带的群速度差 = 2βΔk ⟹ |Δv_g| = 4π|β|/λ_beat：
--            **「广」（λ 大）⟹ 涟漪走得更慢**（而不是更快）。这是 AB 那条直觉在一般色散下的正确版本。
--
-- 诚实边界（写死）：
--   · 二次色散族是**模型选择**（选它是因为 v_g 有闭式；一般 ω(k) 下群速度仍是 dω/dk，只是无闭式）。
--   · GD5「群速度 = dω/dk 的导数身份」未在 Lean 中形式化（mathlib v4.35 的 HasDerivAt
--     实例源不一致），以数值 N10 中心差分收敛阶 ≈ 2 作替身；GD7/GD8 的等式/不等式
--     本身是机器检验的（线性/非线性色散的 v_g−v_ph 关系）。
--   · 零新可检验预言。
--
-- 死法（写死）：
--   ① 若存在 k ≠ 0 且相速度相同但 det ≠ 0 的两带（GD2 反例）⟹ 判据死；
--   ② 若某色散族里群速度差与 1/λ 不成正比（GD9 反例）⟹ 「广 ⟹ 涟漪更慢」只在二次族成立。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import ProjectionPhysics.Explorations.VibrationFrame

namespace ProjectionPhysics.DispersionGeneral

open ProjectionPhysics.VibrationFrame

/-- 一般色散下的振动模：k 与 ω **独立**（不再有 ω = c·k 的约束）。 -/
structure ModeG where
  /-- 波矢 -/
  k : ℝ
  /-- 角频率（一般色散 ω(k)，不再假设线性） -/
  ω : ℝ

/-- 相位：θ = k·x − ω·t。 -/
def phaseOfG (m : ModeG) (x t : ℝ) : ℝ := m.k * x - m.ω * t

/-- 两带相位映射的 Jacobian 行列式（一般色散）：det = k₁ω₂ − k₂ω₁。 -/
def det2 (m₁ m₂ : ModeG) : ℝ := m₁.k * m₂.ω - m₂.k * m₁.ω

/-- 相速度：v_ph = ω/k。 -/
noncomputable def phaseSpeedG (m : ModeG) : ℝ := m.ω / m.k

/-- GD1 ★★★ 一般色散下的判据：det = k₁·k₂·(v_ph,2 − v_ph,1)。
    ⟹ 线性色散只是它的特例（取 ω_i = c_i k_i 即回到 VF2）。 -/
theorem det2_eq_speed_diff {m₁ m₂ : ModeG} (h₁ : m₁.k ≠ 0) (h₂ : m₂.k ≠ 0) :
    det2 m₁ m₂ = m₁.k * m₂.k * (phaseSpeedG m₂ - phaseSpeedG m₁) := by
  simp only [det2, phaseSpeedG]
  field_simp

/-- GD2 ★★★ 退化判据（一般色散版）：det = 0 ⟺ 两带的**相速度相同**。
    ⟹ VF3/VF4 的判据不是线性色散的巧合，它对任意 ω(k) 都成立。 -/
theorem det2_eq_zero_iff {m₁ m₂ : ModeG} (h₁ : m₁.k ≠ 0) (h₂ : m₂.k ≠ 0) :
    det2 m₁ m₂ = 0 ↔ phaseSpeedG m₁ = phaseSpeedG m₂ := by
  rw [det2_eq_speed_diff h₁ h₂]
  have hk : m₁.k * m₂.k ≠ 0 := mul_ne_zero h₁ h₂
  constructor
  · intro h
    have hzero : phaseSpeedG m₂ - phaseSpeedG m₁ = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hk
      · exact h'
    linarith
  · intro h
    rw [h]
    ring

-- ⚠ 符号纪律（六轮攻防 R4，2026-10-30）：本族的线性项系数记作 c₀，**不是** SLS1 的
--   介质等效速度 c（AetherMedium.MediumFlow.c，无 k 参数）。两者同名曾是误读源头：
--   c₀ 是**某条带**的色散参数（波层），c 是**介质**的常量（介质层）。

/-- 二次色散族：ω(k) = c₀·k + β·k²（c₀ 属波层）。 -/
def quadMode (c0 β k : ℝ) : ModeG := ⟨k, c0 * k + β * k ^ 2⟩

/-- GD3 ★★ 二次族的相速度：v_ph = c + βk。 -/
theorem quad_phaseSpeed (c0 β k : ℝ) (hk : k ≠ 0) :
    phaseSpeedG (quadMode c0 β k) = c0 + β * k := by
  simp only [quadMode, phaseSpeedG]
  field_simp

/-- GD4 ★★ 群速度（定义）：v_g = dω/dk = c + 2βk。 -/
noncomputable def vgroup (c β k : ℝ) : ℝ := c + 2 * β * k

-- GD5（导数身份）**不在 Lean 里证**：
--   v_g = dω/dk 的机器检验放在数值层（中心差分收敛阶 ≈ 2 = O(h²)，与 YM-S3 同一手法）。
--   原因：v4.35 的 `HasDerivAt.pow` 与本文件的 ℝ 实例不同源（Semiring.toModule vs
--   NormedField.toNormedSpace.toModule），`simpa` 无法统一；这属形式化工程问题，
--   不影响 v_g 的定义与代数的成立。诚实登记在此。

/-- GD6 ★★ 群速度与相位速度的差：v_g − v_ph = βk。 -/
theorem vgroup_sub_phase (c β k : ℝ) :
    vgroup c β k - (c + β * k) = β * k := by
  simp only [vgroup]
  ring

/-- GD7 ★★★ 线性色散（β = 0）⟹ v_g = v_ph：
    **AB 轮把「相位速度」当「信号速度」用是安全的**（两者相等）。 -/
theorem linear_dispersion_speeds_equal (c k : ℝ) :
    vgroup c 0 k = c + 0 * k := by
  simp only [vgroup]
  ring

/-- GD8 ★★★ 非线性色散（β ≠ 0）且 k ≠ 0 ⟹ v_g ≠ v_ph：
    ⟹ 一般情形下**不能混用**——AB2「相位速度无界」不能读成「信号更快」，
       信号（包络）走 v_g。这是 AB 轮那条直觉的正确边界。 -/
theorem nonlinear_speeds_differ {c β k : ℝ} (hβ : β ≠ 0) (hk : k ≠ 0) :
    vgroup c β k ≠ c + β * k := by
  intro h
  have hdiff : vgroup c β k - (c + β * k) = 0 := by rw [h]; ring
  rw [vgroup_sub_phase] at hdiff
  exact (mul_ne_zero hβ hk) hdiff

/-- GD9 ★★★ 「广 ⟹ 涟漪更慢」：两带的群速度差 = 2βΔk，且 |Δv_g| = 4π|β|/λ_beat。
    ⟹ 波长越长（越「广」），涟漪走得越慢；λ → ∞ 时群速度差 → 0（拍频包络静止）。
       这是 AB2「越广越快」在一般色散下的**正确版本**：快的只是相位，包络反而冻住。 -/
theorem quad_group_speed_gap (c β k₁ k₂ : ℝ) :
    vgroup c β k₂ - vgroup c β k₁ = 2 * β * (k₂ - k₁) := by
  simp only [vgroup]
  ring

/-- GD9b ★★ 群速度差的绝对值：|Δv_g| = 2|β|·|Δk|（波长形式 λ = 2π/|Δk| 的等价写法
    在数值层验证：|Δv_g|·λ = 4π|β|）。 -/
theorem quad_group_gap_abs (c β k₁ k₂ : ℝ) :
    |vgroup c β k₂ - vgroup c β k₁| = 2 * |β| * |k₂ - k₁| := by
  rw [quad_group_speed_gap]
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]

end ProjectionPhysics.DispersionGeneral
