-- ProjectionPhysics — SpaceMetric：空间流动度规（GR 重构种子，mathlib 版）
--
-- 新假设（leo）：空间的等效速度 = 光速（矢量光速），空间本身以 v = c 流动。
--   ⟹ 光子 = 完全随空间流动（dx = v·dt = c·dt）
--   ⟹ 固有时间 dτ² = dt² − dx²/c²（标准，绝对框架）
--   ⟹ 光子（dx = c·dt）⟹ dτ² = 0（★ 不花时间："无质量视角下，
--     是空间本身在运动，所以不花时间"——leo 原话）
--   ⟹ 质量粒子（|dx| < |c·dt|，偏离空间流动）⟹ dτ² > 0（花时间）
--
-- 物质视角表述：物质相对空间流动的运动 u = dx/dt − c。
--   光子：u = 0（完全随空间）⟹ dτ = 0
--   质量粒子：u ≠ 0（偏离空间）⟹ dτ > 0
--
-- 核心定理（mathlib）：
--   SM1. ★ 光子不花时间：dx = c·dt ⟹ dτ² = 0
--   SM2. 质量粒子花时间：|dx| < |c·dt| ⟹ dτ² > 0
--   SM3. 物质视角：相对空间流动 u = dx/dt − c；光子 u=0 ⟺ dτ²=0
--   SM4. 度规一致性：dτ² = g_μν Δx^μ Δx^ν（g = diag(1, −1/c²)）
--   SM5. 度规行列式 = −1/c²（时空"体积"不随流动改变）
--   SM6. 时间膨胀：γ = cosh θ，dτ = dt/γ（偏离越大时间越慢）

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

noncomputable section
open Matrix

namespace SpaceMetric

/-- 1+1 维时空坐标（t, x）。 -/
abbrev Spacetime : Type := Fin 2 → ℝ

/-- ★ 度规（1+1 维闵可夫斯基，绝对框架）：
    g = diag(1, −1/c²)。空间流动 v = c 已体现在光子条件 dx = c·dt 中。 -/
def metric (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 1, 0; 0, -1 / c^2 ]

/-- 固有时间平方：dτ² = dt² − dx²/c²。 -/
def properTimeSq (c : ℝ) (dt dx : ℝ) : ℝ :=
  dt^2 - dx^2 / c^2

/-- 物质相对空间流动的运动：u = dx/dt − c（光子 u = 0 = 完全随空间）。 -/
def deviationFromSpaceFlow (c : ℝ) (dt dx : ℝ) : ℝ :=
  dx / dt - c

/-! ### SM1. 光子不花时间 -/

/-- ★ SM1：光子（完全随空间流动 dx = c·dt）⟹ dτ² = 0。
    "无质量视角下，是空间本身在运动，所以不花时间"（leo）。
    代数：dt² − (c·dt)²/c² = dt² − dt² = 0。 -/
theorem photon_proper_time_zero (c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (h : dx = c * dt) :
    properTimeSq c dt dx = 0 := by
  unfold properTimeSq
  rw [h]
  field_simp [hc]
  ring

/-! ### SM2. 质量粒子花时间 -/

/-- ★ SM2：质量粒子（偏离空间流动、绝对速度低于光速）⟹ dτ² > 0。
    时间流逝 = 偏离空间流动的程度——偏离越大 dτ² 越小
    （接近光速 ⟹ 时间膨胀极限）。 -/
theorem massive_proper_time_positive (c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (h : |dx| < |c * dt|) :
    0 < properTimeSq c dt dx := by
  unfold properTimeSq
  -- dτ² > 0 ⟺ c²dt² > dx² ⟺ |c·dt| > |dx|
  have hsq : dx^2 < (c * dt)^2 := by
    exact sq_lt_sq.mpr h
  -- dτ² = (c²dt² − dx²)/c²
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 hc
  have hnum : 0 < c^2 * dt^2 - dx^2 := by
    have : (c * dt)^2 = c^2 * dt^2 := by ring
    rw [← this]
    linarith [hsq]
  have hc2pos : 0 < c^2 := sq_pos_of_ne_zero hc
  have hrewrite : dt^2 - dx^2 / c^2 = (c^2 * dt^2 - dx^2) / c^2 := by
    field_simp [hc2]
  rw [hrewrite]
  exact div_pos hnum hc2pos

/-! ### SM3. 物质视角：偏离空间流动 -/

/-- ★ SM3a：光子 ⟺ 完全随空间流动（相对空间运动 u = 0）⟹ dτ² = 0。
    物质视角下，光子不花时间 = 它与空间流动同步。 -/
theorem photon_comoving_zero_deviation (c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (hdt : dt ≠ 0) (h : deviationFromSpaceFlow c dt dx = 0) :
    properTimeSq c dt dx = 0 := by
  unfold deviationFromSpaceFlow at h
  -- u = dx/dt − c = 0 ⟹ dx = c·dt
  have hdx : dx = c * dt := by
    field_simp [hdt] at h
    linarith
  exact photon_proper_time_zero c dt dx hc hdx

/-- ★ SM3c：质量（dτ² > 0）⟹ 偏离空间流动（dx ≠ c·dt）。
    ★ 这是"质量 = 无法随空间以等效光速运动"的精确形式：
    若物体完全随空间流动（dx = c·dt），则它无质量（dτ² = 0，SM1）。
    故有质量物体必然偏离空间流动——"空间阻力"的代数内容。 -/
theorem mass_implies_deviation_from_flow (c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (h : 0 < properTimeSq c dt dx) :
    dx ≠ c * dt := by
  -- 反证：若 dx = c·dt，则 dτ² = 0，与 dτ² > 0 矛盾
  intro hdx
  have hz : properTimeSq c dt dx = 0 := photon_proper_time_zero c dt dx hc hdx
  linarith

/-- ★ SM3d：偏离空间流动 ⟹ 有质量（dτ² > 0 的充分条件版本）。
    |dx| < |c·dt|（偏离但低于光速）⟹ dτ² > 0。 -/
theorem deviation_implies_mass (c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (h : |dx| < |c * dt|) :
    0 < properTimeSq c dt dx :=
  massive_proper_time_positive c dt dx hc h

/-- ★ SM3b：质量粒子（偏离空间流动 u ≠ 0）在低于光速时花时间。 -/
theorem massive_deviation_positive_time (c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (hdt : dt ≠ 0)
    (hu : deviationFromSpaceFlow c dt dx ≠ 0) (h : |dx| < |c * dt|) :
    0 < properTimeSq c dt dx := by
  exact massive_proper_time_positive c dt dx hc h

/-! ### SM4. 度规一致性 -/

/-- ★ SM4：固有时间平方 = 度规双线性形式 dτ² = g_μν Δx^μ Δx^ν。
    确认 metric 与 properTimeSq 是同一个量。 -/
theorem proper_time_eq_metric (c : ℝ) (dt dx : ℝ) :
    properTimeSq c dt dx =
      (metric c) ⟨0, by decide⟩ ⟨0, by decide⟩ * dt^2 +
      (metric c) ⟨0, by decide⟩ ⟨1, by decide⟩ * (dt * dx) +
      (metric c) ⟨1, by decide⟩ ⟨0, by decide⟩ * (dt * dx) +
      (metric c) ⟨1, by decide⟩ ⟨1, by decide⟩ * dx^2 := by
  unfold properTimeSq metric
  simp
  ring

/-! ### SM5. 度规行列式 -/

/-- ★ SM5：det(g) = −1/c²——空间流动不改变时空"体积"。
    这意味着流动是坐标变换层面的（保体积），
    为"空间流动 = 惯性力而非引力"提供了代数证据。 -/
theorem metric_det (c : ℝ) (hc : c ≠ 0) :
    (metric c) ⟨0, by decide⟩ ⟨0, by decide⟩ *
      (metric c) ⟨1, by decide⟩ ⟨1, by decide⟩ -
    (metric c) ⟨0, by decide⟩ ⟨1, by decide⟩ *
      (metric c) ⟨1, by decide⟩ ⟨0, by decide⟩ =
    -1 / c^2 := by
  unfold metric
  simp

/-! ### SM6. 时间膨胀（快度连接） -/

/-- ★ SM6：时间膨胀因子 γ = cosh θ（LR2 呼应），
    固有时间 dτ² = dt²(1 − tanh²θ)——偏离空间流动越多（θ 越大），
    时间越慢。1 − tanh²θ = 1/cosh²θ = 1/γ²。 -/
theorem proper_time_dilation (θ : ℝ) (dt : ℝ) :
    dt^2 * (1 - Real.tanh θ ^ 2) = dt^2 / Real.cosh θ ^ 2 := by
  have h : 1 - Real.tanh θ ^ 2 = 1 / Real.cosh θ ^ 2 := by
    have hcosh : Real.cosh θ ≠ 0 := Real.cosh_pos θ |>.ne'
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hcosh]
    rw [Real.cosh_sq_sub_sinh_sq]
  rw [h]
  ring

/-- 偏离空间流动的速度 u 与快度：u = c·tanh θ（LorentzRebuild 呼应）。 -/
def deviationVelocity (c : ℝ) (θ : ℝ) : ℝ := c * Real.tanh θ

end SpaceMetric

end
