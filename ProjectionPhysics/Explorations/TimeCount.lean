-- ProjectionPhysics — TimeCount：时间计数接口 —— 闭包次数 ⟷ 带指标
--
-- leo（2026-10-29 四续）：「按优先级完成，1，2，3 都做完」
--   ① 时间计数接口（VBC 的闭包次数 n ↔ 振动坐标里的带指标 k）
--
-- 接口本身只有一行：**一次闭合 = 相位走 2π = 位移一个波长**。于是
--
--     跨度 L 上的时间计数（闭合次数）  n = k·L / 2π
--     计数密度（单位长度）            ρ = k / 2π = 1/λ
--
-- 即：**时间单位数 = 带指标 × 跨度 / 2π**。这把两轮的东西接成同一个量：
--   · VBC4/VBC5（`clos_translate`）：时间单位 = 闭合次数（相位侧的定义）
--   · VF5/VF8（振动坐标）：带指标 k 与波长 λ = 2π/k（空间侧的刻度）
--   ⟹ 两者不是"类似"，是**同一个数的两种写法**（本模块 TC1–TC3）。
--
-- 三条推论（都有物理含义，且都可判死）：
--   TC4 ★★★ 时间计数依赖**所选的带**：k₁ ≠ k₂ 的带在同一跨度上给出不同的计数
--            ⟹ 「绝对时间计数」在本框架里不存在，只有"某条带上的计数"。
--   TC5 ★★  k = 0 的带（全局模）在固定跨度上**不产生任何计数** ⟹ 与 VF9/VF10 同源：
--            超广意模既不推进相位，也不产生时间单位。
--   TC6 ★★★ 两带的**计数差**密度 = |Δk|/(2π) = 1/λ_beat —— 正好是「广」的刻度
--            ⟹ 「广」= 计数差变小 = 拍频周期变长。时间计数与带宽是同一个刻度。
--
-- 诚实边界（写死）：
--   · 本模块的「时间计数」是**相位圈数**，不是钟读数；把它等同于物理时间是框架读法
--     （VBC4/VBC5 已给出口径：闭合次数 = 时间单位）。
--   · 计数密度用实数（不取整）；取整后的整数化定理见 VBC1（`winding_index_integer`），本模块不重证。
--   · 零新可检验预言。
--
-- 死法（写死）：
--   ① 若某条 k ≠ 0 的带在一个波长内不产生一次闭合（TC3 的反例），则接口死；
--   ② 若存在两条不同 k 的带在**所有**跨度上给出相同计数（TC4 的反例），则「计数依赖带」
--      这句话死（那意味着 k 已经不是刻度）。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import ProjectionPhysics.Explorations.VibrationFrame

namespace ProjectionPhysics.TimeCount

open ProjectionPhysics.VibrationFrame

/-- 计数密度：单位长度上的闭合次数 ρ = k/2π = 1/λ。 -/
noncomputable def countDensity (k : ℝ) : ℝ := k / (2 * Real.pi)

/-- 跨度 L 上的时间计数（闭合次数的实数口径）n = k·L/2π。 -/
noncomputable def timeCount (k L : ℝ) : ℝ := k * L / (2 * Real.pi)

/-- TC1 ★ 计数 = 密度 × 跨度（定义一致性）。 -/
theorem timeCount_eq_density_mul (k L : ℝ) : timeCount k L = countDensity k * L := by
  simp only [timeCount, countDensity]
  ring

/-- TC2 ★★ 计数对跨度可加：两段接起来的计数 = 两段计数之和
    （时间计数的加法性 ⟹ 它真的是一个"计数"，不是随便的函数）。 -/
theorem timeCount_add (k L₁ L₂ : ℝ) :
    timeCount k (L₁ + L₂) = timeCount k L₁ + timeCount k L₂ := by
  simp only [timeCount]
  ring

/-- TC3 ★★★ 一个波长走一圈：k ≠ 0 时 timeCount k (2π/k) = 1。
    ⟹ **时间单位长度 = 该带的波长**（VBC 的"一次闭合"与 VF 的"一个波长"是同一件事）。 -/
theorem timeCount_one_wavelength {k : ℝ} (hk : k ≠ 0) :
    timeCount k (2 * Real.pi / k) = 1 := by
  simp only [timeCount]
  field_simp

/-- 跨度 2π 上的计数就等于带指标本身（后面几条引理的枢纽）。 -/
theorem timeCount_two_pi (k : ℝ) : timeCount k (2 * Real.pi) = k := by
  simp only [timeCount]
  field_simp

/-- TC4 ★★★ 时间计数依赖**所选的带**：k₁ ≠ k₂ ⟹ 存在跨度 L 使两者计数不同
    ⟹ 「绝对时间计数」不存在，只有"某条带上的计数"。
    （见证：L = 2π，此时计数恰为 k 本身。） -/
theorem timeCount_depends_on_band {k₁ k₂ : ℝ} (h : k₁ ≠ k₂) :
    ∃ L : ℝ, timeCount k₁ L ≠ timeCount k₂ L := by
  refine ⟨2 * Real.pi, ?_⟩
  rw [timeCount_two_pi, timeCount_two_pi]
  exact h

/-- TC5 ★★ 全局模（k = 0）在固定跨度上不产生任何计数
    ⟹ 超广意模既不推进相位、也不产生时间单位（与 VF9/VF10 同源）。 -/
theorem timeCount_zero_band (L : ℝ) : timeCount 0 L = 0 := by
  simp [timeCount]

/-- TC6 ★★★ 两带的计数**差**密度 = |Δk|/(2π) = 1/λ_beat —— 正好是「广」的刻度。
    ⟹ 「更广」= 计数差更小 = 拍频周期更长；时间计数与带宽是**同一个刻度**。 -/
theorem countGap_density_eq_inverse_beatWavelength {k₁ k₂ : ℝ} (h : k₁ ≠ k₂) :
    |k₁ - k₂| / (2 * Real.pi) = 1 / beatWavelength k₁ k₂ := by
  unfold beatWavelength
  have habs : |k₁ - k₂| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr h)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- TC6b ★ 计数差的线性形式：两带计数之差 = (k₁ − k₂)·L/2π。 -/
theorem timeCount_gap (k₁ k₂ L : ℝ) :
    timeCount k₁ L - timeCount k₂ L = (k₁ - k₂) * L / (2 * Real.pi) := by
  simp only [timeCount]
  ring

end ProjectionPhysics.TimeCount
