-- ProjectionPhysics — DecayChannels：C 守恒的三条衰变道（DC1–DC5）
--
-- leo（2026-11-02）：「可以开始推导 α、γ、自发裂变（都 C 守恒）」。
--
-- 这三条路**不破缺 C**（α/裂变：强+电磁；γ：电磁），所以 `Antimatter` AM4 不禁止它们。
-- 本模块只做框架**真能推出来**的那部分，并把它推不出来的部分写明。
--
-- 【能推的】
--
--   DC1 ★★★ `alpha_threshold`：**α 发射的阈值条件**。
--        框架的质量律是 m = √N·M₀（不是 m = N·M₀）。
--        Q = (√Nᵢ − √N_f − √N_α)·M₀ > 0 ⟺ √Nᵢ > √N_f + √N_α
--        并且（DC1b）这**严格强于**加性条件：
--            Nᵢ > N_f + N_α + 2√(N_f·N_α)
--        ⟹ **√N 质量律让衰变「更难」**：多出来的量必须超过两倍的几何平均，
--           而加性质量模型只要 Nᵢ > N_f + N_α。**这是两条质量律的可分辨差别。**
--
--   DC2 ★★★ `geiger_nuttall_slope`：**Geiger–Nuttall 的斜率与前置因子无关**。
--        设 λ = ω·exp(−C/√E)。则两个核的寿命比
--            λ₁/λ₂ = exp(−C/√E₁ + C/√E₂)
--        中 **ω 完全消掉**。⟹ 上一次算出的「框架前置因子高估 1500 倍」
--        **不会污染斜率**，只影响截距。这是这条道唯一干净可测的组合。
--
--   DC3 ★★★ `barrier_C_invariant`：**反物质核的 α/γ 寿命与物质核相同**。
--        库仑势垒只依赖电荷**乘积** q₁q₂；流动反向下两个电荷同时变号 ⟹ 乘积不变
--        ⟹ 势垒不变 ⟹ 隧穿概率不变 ⟹ 寿命相同。（可测：反质子/反氢实验。）
--
--   DC4 `fission_uses_same_threshold`：自发裂变与 α 共用同一个阈值判据（换成碎片条数）。
--
-- 【推不出的（写死）】
--   · **绝对速率**：需要 ω 的数值来源。框架只能给 ω ≈ M₀/ħ ≈ 1.5×10²⁴ s⁻¹，
--     而核能级间距给出的是 ~1.5×10²¹ s⁻¹ —— 差 ~1.5×10³ 倍（缺 ~1 MeV 的核尺度）。
--     DC2 证明这个误差**只进截距，不进斜率**。
--   · **γ 衰变的速率**：爱因斯坦 A 系数 ∝ ω³|d|²，ω³ 来自**场量子化的相空间**；
--     框架里没有场的量子化（只有运动学恒等式）⟹ γ 只能给**选择定则**，给不出速率。
--   · **势垒归一化**：Gamow 指数里的 ∫√(V−E)dr 需要把"力"积成"势"。框架有力
--     （m·dv 等），但把它写成标量势并按 WKB 积分是**外部输入**，本模块不假装有。
--
-- 不声称：不声称解决 Clay；反射正性 / 测度 / 连续极限仍为零；
--         不声称解释了 β 衰变（AM4 结构禁止）。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import ProjectionPhysics.Explorations.MassGap

noncomputable section

namespace ProjectionPhysics.DecayChannels

open ProjectionPhysics
open ProjectionPhysics.MassGap

/-- 碎片的质量（框架质量律：m = √N·M₀）。 -/
def fragMass (N : ℕ) (M₀ : ℝ) : ℝ := Real.sqrt (N : ℝ) * M₀

/-- 衰变 Q 值：母核质量 − 子核与碎片质量之和。 -/
def qValue (Ni Nf Na : ℕ) (M₀ : ℝ) : ℝ :=
  fragMass Ni M₀ - fragMass Nf M₀ - fragMass Na M₀

/-! ### DC1 α 发射的阈值条件 -/

/-- DC1 ★★★ **α 发射的阈值**：Q > 0 ⟺ √Nᵢ > √N_f + √N_α（M₀ > 0）。 -/
theorem alpha_threshold {Ni Nf Na : ℕ} {M₀ : ℝ} (hM : 0 < M₀) :
    0 < qValue Ni Nf Na M₀ ↔
      Real.sqrt (Na : ℝ) + Real.sqrt (Nf : ℝ) < Real.sqrt (Ni : ℝ) := by
  unfold qValue fragMass
  constructor <;> intro h <;> nlinarith

/-- DC1b ★★★ **√N 质量律让衰变更难**：阈值等价于
    `Nᵢ > N_f + N_α + 2√(N_f·N_α)` —— 多出来的量必须超过**两倍几何平均**，
    而加性质量律只需要 `Nᵢ > N_f + N_α`。
    ⟹ 这是「m = √N·M₀」与「m = N·M₀」的**可分辨差别**（不是措辞差别）。 -/
theorem alpha_threshold_stronger {Ni Nf Na : ℕ} {M₀ : ℝ} (hM : 0 < M₀)
    (h : 0 < qValue Ni Nf Na M₀) :
    (Nf : ℝ) + (Na : ℝ) + 2 * Real.sqrt ((Nf : ℝ) * (Na : ℝ)) < (Ni : ℝ) := by
  have hthr := (alpha_threshold hM).mp h
  have hsq : (Real.sqrt (Na : ℝ) + Real.sqrt (Nf : ℝ)) ^ 2
      = (Na : ℝ) + (Nf : ℝ) + 2 * Real.sqrt ((Nf : ℝ) * (Na : ℝ)) := by
    rw [add_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sqrt_mul (by positivity)]
    ring
  have hsq2 : (Real.sqrt (Na : ℝ) + Real.sqrt (Nf : ℝ)) ^ 2 < (Real.sqrt (Ni : ℝ)) ^ 2 := by
    nlinarith [hthr, Real.sqrt_nonneg (Na : ℝ), Real.sqrt_nonneg (Nf : ℝ),
      Real.sqrt_nonneg (Ni : ℝ)]
  rw [hsq, Real.sq_sqrt (by positivity)] at hsq2
  linarith

/-- DC1c：加性质量律（m = N·M₀）的阈值只是 `Nᵢ > N_f + N_α`；
    DC1b 说明 √N 律要求**更多**（多出 2√(N_f·N_α)）。 -/
theorem additive_threshold {Ni Nf Na : ℕ} {M₀ : ℝ} (hM : 0 < M₀) :
    0 < ((Ni : ℝ) - (Nf : ℝ) - (Na : ℝ)) * M₀ ↔ (Nf : ℝ) + (Na : ℝ) < (Ni : ℝ) := by
  constructor <;> intro h <;> nlinarith

/-! ### DC2 Geiger–Nuttall：斜率与前置因子无关 -/

/-- DC2 ★★★ **Geiger–Nuttall 的斜率不受前置因子污染**：
    设 λ = ω·exp(−C/√E)。两个核的寿命比里 **ω 完全消掉**：

      λ₁/λ₂ = exp(−C/√E₁ + C/√E₂)

    ⟹ 框架把 ω 算错 1500 倍**只影响截距，不影响斜率**。
       所以在「同一势垒形状 C 相同」的一族核里，Geiger–Nuttall 斜率是**干净的判据**。 -/
theorem geiger_nuttall_slope (ω C E₁ E₂ : ℝ) (hω : 0 < ω) :
    (ω * Real.exp (-(C / Real.sqrt E₁))) / (ω * Real.exp (-(C / Real.sqrt E₂)))
      = Real.exp (-(C / Real.sqrt E₁) + C / Real.sqrt E₂) := by
  have h : (ω * Real.exp (-(C / Real.sqrt E₁))) / (ω * Real.exp (-(C / Real.sqrt E₂)))
      = Real.exp (-(C / Real.sqrt E₁)) / Real.exp (-(C / Real.sqrt E₂)) := by
    rw [mul_div_mul_left _ _ (ne_of_gt hω)]
  rw [h, ← Real.exp_sub]
  congr 1
  ring

/-- DC2b：等价形式——对数里前置因子只加一个常数，斜率不变。 -/
theorem geiger_nuttall_log_form (ω C E : ℝ) (hω : 0 < ω) :
    Real.log (ω * Real.exp (-(C / Real.sqrt E)))
      = Real.log ω - C / Real.sqrt E := by
  rw [Real.log_mul (ne_of_gt hω) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  ring

/-! ### DC3 反物质核寿命相同 -/

/-- 库仑势垒的强度 ∝ 两个电荷的**乘积**。 -/
def coulombBarrier (q₁ q₂ : ℝ) (k : ℝ) : ℝ := k * (q₁ * q₂)

/-- DC3 ★★★ **反物质核的 α 寿命与物质核相同**：
    流动反向下两个电荷**同时变号**，乘积不变 ⟹ 势垒不变 ⟹ 隧穿概率不变 ⟹ 寿命相同。
    ⟹ 这是「干净设置」保住后可测的一条：反核的 α/γ 衰变寿命 = 正核。
       （实验上已如此：反氢光谱、反质子束缚态的强/电磁性质。） -/
theorem barrier_C_invariant (q₁ q₂ k : ℝ) :
    coulombBarrier (-q₁) (-q₂) k = coulombBarrier q₁ q₂ k := by
  unfold coulombBarrier
  ring

/-! ### DC4 自发裂变共用同一阈值 -/

/-- DC4：自发裂变与 α 发射**结构相同**——只是碎片条数换成两个碎片的条数。
    ⟹ 阈值判据（DC1）直接适用，不需要新机制。 -/
theorem fission_uses_same_threshold {Ni N₁ N₂ : ℕ} {M₀ : ℝ} (hM : 0 < M₀) :
    0 < qValue Ni N₁ N₂ M₀ ↔ Real.sqrt (N₂ : ℝ) + Real.sqrt (N₁ : ℝ) < Real.sqrt (Ni : ℝ) :=
  alpha_threshold hM

end ProjectionPhysics.DecayChannels
