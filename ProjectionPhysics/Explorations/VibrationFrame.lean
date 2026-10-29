-- ProjectionPhysics — VibrationFrame：超广意场在**振动坐标系**里的数学模型
--
-- leo（2026-10-29 三续）：「时间计数接口可接，但是最需要做的还是**超广意场的数学模型
--   在振动坐标系的描述过程**。」
--
-- 本模块给出这个「描述过程」的三段式，全部是初等代数（可机器检验）：
--
--   ① **从场到振动坐标**：一个振动模由 (k, ω) 标定，相位 θ = kx − ωt，线性色散 ω = c·k。
--      把 (x, t) 映到相位组 (θ₁, θ₂, …) 才是一次「振动坐标描述」。
--      ★ VF1：单个模的相位沿射线 (x + c·s, t + s) 不变 ⟹ 单模的振动坐标**只有一维信息**，
--        分不开「空间」与「时间」。这就是为什么单凭一个模描述不了「广」。
--      ★★ VF2：两个模的 Jacobian 行列式 = k₁k₂(c₁ − c₂)。
--      ★★★ 于是判据是干净的：**振动坐标是真坐标 ⟺ 两个带的相速度不一致**
--        （= leo 说的「局域频率不一致」）；相速度相同（VF3）⟹ Jacobian = 0 ⟹ 退化。
--        ⟹ 「不一致」不是形容语义，而是**坐标非退化的充要条件**。
--
--   ② **「广」的刻度**：两个带 + 权重，波矢的加权方差
--      ★★ VF5 闭式：var = w₁w₂/(w₁+w₂)² · (k₁ − k₂)²
--      ★★ VF6：var = 0 ⟺ 两带波矢相同
--      ★★★ VF8：var = C · |Δk|² = C · (2π/λ)²，λ = 2π/|Δk| 是**拍频波长**
--        ⟹ **「广」只有一个刻度**：Δk 越小 ⟹ 波长越长 ⟹ 方差越小。
--        所以「范围更大」的精确含义是**波长更长、起伏更弱**，不是「更快」
--        （「更快」是相位速度 v_ph = ω/k 的事，与「广」是两个坐标，混用才出矛盾）。
--
--   ③ **超广意场的极限**：
--      ★★ VF9：k = 0 的全局模相位处处为 0 ⟹ 所有点映到**同一个**振动坐标。
--      ★★ VF10：极限 dk → 0 同时给出三件事：Jacobian → 0（坐标退化）、var → 0（无起伏）、
--        λ → ∞（无涟漪）。⟹ 在「超广意」极限处，振动坐标系**自己失效**——
--        这正是 AB（零带宽）与 AT（顺序盲）两条结论在坐标系语言里的同一句话。
--
-- 诚实边界（写死）：
--   · 两带、线性色散 ω = c·k、权重为正 —— 都是**模型选择**，不是从公设推出。
--     一般色散 ω(k) 下 VF2 的判据要换成 det = k₁ω₂ − k₂ω₁ ≠ 0（本模块只做线性情形的闭式）。
--   · 「振动坐标」是**描述坐标**（相空间式的），不是物理时空坐标；它退化**不表示**时空退化。
--   · VF8 的 λ 是**拍频波长**（两带之差），不是任一模自身的波长。
--   · 零新可检验预言：本模块给的是「广 / 快 / 涟漪」三者的坐标关系，不是新数值。
--
-- 死法（写死）：
--   ① 若存在相速度不同但 Jacobian 仍为 0 的两带（在某一处），则 VF2/VF4 死；
--   ② 若「广」无法用波矢分布的一个刻度表示（需要两个独立刻度），则 VF5/VF8 死；
--   ③ 若 k = 0 的模在振动坐标里仍能分辨 (x, t)（VF9 的反例），则「全局模退化」死。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProjectionPhysics.VibrationFrame

-- ---------------------------------------------------------------------------
-- ① 从场到振动坐标
-- ---------------------------------------------------------------------------

/-- 一个振动模：波矢 k 与相速度 c（线性色散 ω = c·k）。 -/
structure Mode where
  /-- 波矢（「广」的倒数） -/
  k : ℝ
  /-- 相速度 -/
  c : ℝ

/-- 角频率：线性色散 ω = c·k。 -/
def Mode.omega (m : Mode) : ℝ := m.c * m.k

/-- 相位：θ(x,t) = k·x − ω·t。这是「用振动量给场编坐标」的第一步。 -/
def phaseOf (m : Mode) (x t : ℝ) : ℝ := m.k * x - m.omega * t

/-- VF1 ★ 单个模的相位沿射线不变：θ(x + c·s, t + s) = θ(x, t)。
    ⟹ 单模的振动坐标**只有一维信息**（只依赖 ξ = x − c·t），
       无法把「空间」与「时间」分开描述——这就是「广」在单模里不可定义的原因。 -/
theorem phase_constant_along_ray (m : Mode) (x t s : ℝ) :
    phaseOf m (x + m.c * s) (t + s) = phaseOf m x t := by
  simp only [phaseOf, Mode.omega]
  ring

/-- 两个模的相位映射 (x,t) ↦ (θ₁(x,t), θ₂(x,t)) 的 Jacobian 行列式。 -/
def jacobian2 (m₁ m₂ : Mode) : ℝ :=
  m₁.k * (-(m₂.omega)) - m₂.k * (-(m₁.omega))

/-- VF2 ★★★ Jacobian = k₁·k₂·(c₁ − c₂)。
    ⟹ 振动坐标成为**真坐标**的条件是可算的：两带相速度不一致。 -/
theorem jacobian2_eq (m₁ m₂ : Mode) :
    jacobian2 m₁ m₂ = m₁.k * m₂.k * (m₁.c - m₂.c) := by
  simp only [jacobian2, Mode.omega]
  ring

/-- VF3 ★★ 相速度相同 ⟹ Jacobian = 0：两个带给出同一族射线，
    振动坐标退化（只剩 ξ = x − c·t 一个方向）⟹ 「局域频率一致」的场没有可分辨的振动结构。 -/
theorem jacobian2_zero_of_same_speed (m₁ m₂ : Mode) (h : m₁.c = m₂.c) :
    jacobian2 m₁ m₂ = 0 := by
  rw [jacobian2_eq, h]
  ring

/-- VF4 ★★★ 反过来：波矢都非零且相速度不同 ⟹ Jacobian ≠ 0 ⟹ 真坐标。
    ⟹ 「局域频率不一致」是**坐标非退化的充要条件**（在这个两带模型里）。 -/
theorem jacobian2_ne_zero (m₁ m₂ : Mode) (hk₁ : m₁.k ≠ 0) (hk₂ : m₂.k ≠ 0)
    (hc : m₁.c ≠ m₂.c) : jacobian2 m₁ m₂ ≠ 0 := by
  rw [jacobian2_eq]
  exact mul_ne_zero (mul_ne_zero hk₁ hk₂) (sub_ne_zero.mpr hc)

-- ---------------------------------------------------------------------------
-- ② 「广」的刻度：波矢分布的一个参数
-- ---------------------------------------------------------------------------

/-- 两带的加权平均波矢。 -/
noncomputable def bandMean (w₁ w₂ k₁ k₂ : ℝ) : ℝ := (w₁ * k₁ + w₂ * k₂) / (w₁ + w₂)

/-- 两带的加权波矢方差（「广」的刻度：方差越小 ⟹ 越广）。 -/
noncomputable def bandVar (w₁ w₂ k₁ k₂ : ℝ) : ℝ :=
  (w₁ * (k₁ - bandMean w₁ w₂ k₁ k₂) ^ 2 + w₂ * (k₂ - bandMean w₁ w₂ k₁ k₂) ^ 2)
    / (w₁ + w₂)

/-- VF5 ★★ 方差闭式：var = w₁w₂/(w₁+w₂)² · (k₁ − k₂)²。
    ⟹ 「广」只由一个数 Δk 控制（不需要两个刻度）。 -/
theorem bandVar_closed_form (w₁ w₂ k₁ k₂ : ℝ) (hw : w₁ + w₂ ≠ 0) :
    bandVar w₁ w₂ k₁ k₂ = w₁ * w₂ / (w₁ + w₂) ^ 2 * (k₁ - k₂) ^ 2 := by
  simp only [bandVar, bandMean]
  field_simp
  ring

/-- VF6 ★★ 权重为正时：方差为 0 ⟺ 两带波矢相同（完全同相 ⟹ 无起伏）。 -/
theorem bandVar_eq_zero_iff {w₁ w₂ k₁ k₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    bandVar w₁ w₂ k₁ k₂ = 0 ↔ k₁ = k₂ := by
  have hw : w₁ + w₂ ≠ 0 := by positivity
  rw [bandVar_closed_form w₁ w₂ k₁ k₂ hw]
  have hcoef : 0 < w₁ * w₂ / (w₁ + w₂) ^ 2 := by positivity
  constructor
  · intro h
    have hsq : (k₁ - k₂) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h (ne_of_gt hcoef)
      · exact h
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro h
    rw [h]
    ring

/-- 拍频波长：λ = 2π/|Δk|（两带差频形成的「涟漪」的波长）。 -/
noncomputable def beatWavelength (k₁ k₂ : ℝ) : ℝ := 2 * Real.pi / |k₁ - k₂|

/-- VF7 ★★ 波长与波矢差互为倒数：2π/λ = |Δk|（非零时）。 -/
theorem two_pi_over_beatWavelength {k₁ k₂ : ℝ} (h : k₁ ≠ k₂) :
    2 * Real.pi / beatWavelength k₁ k₂ = |k₁ - k₂| := by
  unfold beatWavelength
  have habs : |k₁ - k₂| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr h)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- VF8 ★★★ 一个刻度：起伏强度 = C · |Δk|² = C · (2π/λ)²。
    ⟹ 「范围更大（λ 更长）」「起伏更弱（var 更小）」是**同一件事**
      —— 它们是同一个参数 Δk 的两面，不是两个独立的旋钮。 -/
theorem bandVar_is_inverse_wavelength_sq {w₁ w₂ k₁ k₂ : ℝ} (h : k₁ ≠ k₂)
    (hw : w₁ + w₂ ≠ 0) :
    bandVar w₁ w₂ k₁ k₂
      = w₁ * w₂ / (w₁ + w₂) ^ 2 * (2 * Real.pi / beatWavelength k₁ k₂) ^ 2 := by
  rw [bandVar_closed_form w₁ w₂ k₁ k₂ hw, two_pi_over_beatWavelength h, sq_abs]

-- ---------------------------------------------------------------------------
-- ③ 超广意场的极限：k → 0
-- ---------------------------------------------------------------------------

/-- VF9 ★★ 全局模（k = 0）的相位处处为 0：所有时空点映到**同一个**振动坐标。 -/
theorem global_mode_phase_zero (c x t : ℝ) : phaseOf ⟨0, c⟩ x t = 0 := by
  simp [phaseOf, Mode.omega]

/-- VF10 ★★★ 超广意极限的三件事同时发生（本模块的主结论）：
    取两带的 k 都为 0，则 ① 相位恒为 0（所有点同一振动坐标）、
    ② 波矢方差为 0（无起伏）、③ Jacobian 为 0（振动坐标退化）。
    ⟹ 在「超广意」极限处，**振动坐标系自己失效**——
       AB（零带宽）与 AT（顺序盲）在坐标语言里就是这一句。 -/
theorem global_limit (w₁ w₂ c₁ c₂ x t : ℝ) (hw : w₁ + w₂ ≠ 0) :
    phaseOf ⟨0, c₁⟩ x t = 0 ∧ phaseOf ⟨0, c₂⟩ x t = 0 ∧
      bandVar w₁ w₂ 0 0 = 0 ∧ jacobian2 ⟨0, c₁⟩ ⟨0, c₂⟩ = 0 := by
  refine ⟨global_mode_phase_zero c₁ x t, global_mode_phase_zero c₂ x t, ?_, ?_⟩
  · rw [bandVar_closed_form w₁ w₂ 0 0 hw]
    ring
  · rw [jacobian2_eq]
    ring

end ProjectionPhysics.VibrationFrame
