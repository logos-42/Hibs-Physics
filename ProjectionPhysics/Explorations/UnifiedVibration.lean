-- ProjectionPhysics — UnifiedVibration：振动→旋量→源项→四力的统一代数接口
--
-- 本模块把此前分散在 PhaseField / VibrationKappa / Twistor / GQF2 的
-- 结构接口集中起来。只形式化代数恒等、零点、正性与 product rule；
-- 不把 κ、质量单位或包络动力学偷换成定理。

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import ProjectionPhysics.Explorations.VibrationKappa

namespace ProjectionPhysics.UnifiedVibration

noncomputable section

/-- 包络×旋量相对方向的质量候选：对应 |A₁ A₂|² sin²((θ₂−θ₁)/2)。 -/
def spinorEnvelopeCandidate (a₁ a₂ dθ : ℝ) : ℝ :=
  (a₁ * a₂) ^ 2 * (Real.sin (dθ / 2)) ^ 2

/-- MS5 源项候选：κ 仍显式保留为接口参数。 -/
def sourceCandidate (κ a₁ a₂ dθ : ℝ) : ℝ :=
  κ * spinorEnvelopeCandidate a₁ a₂ dθ

/-- 动量候选：P = m(C−v)。 -/
def flowMomentum (m C v : ℝ) : ℝ :=
  m * (C - v)

/-- 四力通道：dm·C、m·dC、−dm·v、−m·dv。 -/
def fourForceSum (dm m C v dC dv : ℝ) : ℝ :=
  dm * C + m * dC - dm * v - m * dv

/-- UV1：统一质量候选的显式分解。 -/
theorem spinorEnvelopeCandidate_factor (a₁ a₂ dθ : ℝ) :
    spinorEnvelopeCandidate a₁ a₂ dθ =
      (a₁ * a₂) ^ 2 * (Real.sin (dθ / 2)) ^ 2 := by
  rfl

/-- UV2：旋量相对方向平行（相位差为 0）时，候选质量为零。 -/
theorem spinorEnvelopeCandidate_zero (a₁ a₂ : ℝ) :
    spinorEnvelopeCandidate a₁ a₂ 0 = 0 := by
  unfold spinorEnvelopeCandidate
  norm_num [Real.sin_zero]

/-- UV3：源项候选在 κ=0 或旋量候选为零时为零。 -/
theorem sourceCandidate_zero_of_kappa_zero (a₁ a₂ dθ : ℝ) :
    sourceCandidate 0 a₁ a₂ dθ = 0 := by
  unfold sourceCandidate
  ring

theorem sourceCandidate_zero_of_aligned (κ a₁ a₂ : ℝ) :
    sourceCandidate κ a₁ a₂ 0 = 0 := by
  unfold sourceCandidate spinorEnvelopeCandidate
  simp

/-- UV4：非零 κ、非零包络、非零相对正弦时，源项候选为正。 -/
theorem sourceCandidate_pos {κ a₁ a₂ dθ : ℝ}
    (hκ : 0 < κ) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0)
    (hs : Real.sin (dθ / 2) ≠ 0) :
    0 < sourceCandidate κ a₁ a₂ dθ := by
  unfold sourceCandidate spinorEnvelopeCandidate
  have h12 : 0 < (a₁ * a₂) ^ 2 := by
    exact sq_pos_of_ne_zero (mul_ne_zero h₁ h₂)
  have hs2 : 0 < (Real.sin (dθ / 2)) ^ 2 := by
    exact sq_pos_of_ne_zero hs
  exact mul_pos hκ (mul_pos h12 hs2)

/-- UV5：流动动量的 product rule 四通道。 -/
theorem flowMomentum_product_rule (dm m C v dC dv : ℝ) :
    fourForceSum dm m C v dC dv =
      dm * (C - v) + m * (dC - dv) := by
  unfold fourForceSum
  ring

/-- UV6：四通道按物理标签分组仍是同一个 product rule。 -/
theorem flow_channels_grouped (dm m C v dC dv : ℝ) :
    dm * C + m * dC - (dm * v + m * dv) =
      dm * (C - v) + m * (dC - dv) := by
  ring

/-- UV7：当前接口明确保留 κ，因此它不是绝对质量/力的推导。 -/
theorem sourceCandidate_linear_in_kappa (κ₁ κ₂ a₁ a₂ dθ : ℝ) :
    sourceCandidate (κ₁ + κ₂) a₁ a₂ dθ =
      sourceCandidate κ₁ a₁ a₂ dθ + sourceCandidate κ₂ a₁ a₂ dθ := by
  unfold sourceCandidate
  ring

end
end ProjectionPhysics.UnifiedVibration
