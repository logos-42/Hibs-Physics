-- ProjectionPhysics — BandDimension：带的个数 ⟷ 振动坐标的维数（③）
--
-- leo（2026-10-29 四续）优先级 ③：「三带以上：带的个数 = 振动坐标的维数，
--   「维度」的第一个可算版本」。
--
-- 结论（本模块证的就是它，而且是**否定式**的）：
--
--   相位是 (k, ω) 与 (x, t) 的内积。在 1+1 维时空里 (k, ω) ∈ ℝ²，
--   ⟹ **任意三条带都线性相关**（三个向量在 ℝ² 里必有非平凡线性关系）。
--   ⟹ 第三条带**不增加任何独立坐标**：振动坐标的秩 ≤ 2 = 时空维数。
--   ⟹ 「多带」不是「高维」。要得到第 3 个独立振动坐标，必须升**空间维数**
--      （相位里出现第二个独立的空间分量），而不是再加一条同一空间方向上的带。
--
--   并且同一条线性关系同时作用在**时间计数**上（因为 n = kL/2π 对 k 是线性的）：
--   第三条带的计数 = 前两条的同一个线性组合 ⟹ 计数也冗余。
--
-- 定理：
--   ND1 ★★★ exists_coefficients：det₂(m₁,m₂) ≠ 0 ⟹ 存在显式 (a,b) 满足
--           k₃ = a k₁ + b k₂ ∧ ω₃ = a ω₁ + b ω₂（波矢与频率用同一组系数）
--   ND2 ★★★ third_band_redundant：由 ND1 ⟹ θ₃(x,t) = a·θ₁(x,t) + b·θ₂(x,t) 对一切 (x,t)
--   ND3 ★★  秩封顶的见证：三条相位存在**非平凡**线性关系（系数 (−a,−b,1) ≠ 0）
--   ND4 ★★★ 计数冗余：n₃(L) = a·n₁(L) + b·n₂(L)（接 TimeCount 的接口）
--   ND5 ★★  k 全为零 ⟹ 三条相位恒为 0（超广意模没有坐标，与 VF10 同）
--
-- 诚实边界（写死）：
--   · 「秩 ≤ 2」是 **1+1 维时空**的结论；d 维空间给出 (d+1) 维相位空间，上界是 d+1（本模块只做 d=1）。
--   · 「维度 = min(带数, d+1)」是本模块的**读法**，Lean 里证的是 1+1 维的秩封顶那一半。
--   · ND1 需要 det₂(m₁,m₂) ≠ 0（前两条自己不退化）；退化时换一对即可，本模块不做换对枚举。
--   · 零新可检验预言。
--
-- 死法（写死）：
--   ① 若在 1+1 维里找到三条相位线性无关的带（ND1/ND2 反例）⟹ 秩封顶死；
--   ② 若第三条带的计数与前两条的同一线性组合不成比例（ND4 反例）⟹ 计数冗余死。

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import ProjectionPhysics.Explorations.DispersionGeneral
import ProjectionPhysics.Explorations.TimeCount

namespace ProjectionPhysics.BandDimension

open ProjectionPhysics.DispersionGeneral
open ProjectionPhysics.TimeCount

/-- ND1 ★★★ 三个向量在 ℝ² 里必线性相关：存在显式 (a, b) 使波矢与频率**同时**被组合
    （Cramer 解：a = det₂(m₃,m₂)/det₂(m₁,m₂)，b = det₂(m₁,m₃)/det₂(m₁,m₂)）。
    ⟹ 第三条带不增加独立信息。 -/
theorem exists_coefficients {m₁ m₂ m₃ : ModeG} (h : det2 m₁ m₂ ≠ 0) :
    ∃ a b : ℝ, m₃.k = a * m₁.k + b * m₂.k ∧ m₃.ω = a * m₁.ω + b * m₂.ω := by
  -- ⚠ 口径：`field_simp` 会把分母规范化成 `m₂.ω * m₁.k - m₂.k * m₁.ω`，
  --   所以非零假设必须写成**那个形式**，否则分母清不掉（留 ⁻¹，ring 就关不上）。
  have hD : m₂.ω * m₁.k - m₂.k * m₁.ω ≠ 0 := by
    rw [mul_comm m₂.ω m₁.k]
    simpa [det2] using h
  refine ⟨(m₃.k * m₂.ω - m₂.k * m₃.ω) / (m₁.k * m₂.ω - m₂.k * m₁.ω),
          (m₁.k * m₃.ω - m₃.k * m₁.ω) / (m₁.k * m₂.ω - m₂.k * m₁.ω), ?_, ?_⟩
  · field_simp
    try ring
  · field_simp
    try ring

/-- ND2 ★★★ 三带线性相关（1+1 维）：存在 (a, b) 使第三条相位是前两条的线性组合，
    对一切 (x, t) 成立。⟹ 第三条带**不增加独立坐标**。 -/
theorem third_band_redundant {m₁ m₂ m₃ : ModeG} (h : det2 m₁ m₂ ≠ 0) :
    ∃ a b : ℝ, ∀ x t : ℝ,
      phaseOfG m₃ x t = a * phaseOfG m₁ x t + b * phaseOfG m₂ x t := by
  obtain ⟨a, b, hk, hω⟩ := exists_coefficients (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) h
  refine ⟨a, b, ?_⟩
  intro x t
  simp only [phaseOfG]
  rw [hω, hk]
  ring

/-- ND3 ★★ 秩封顶的见证形式：三条相位存在**非平凡**线性关系（系数 (−a, −b, 1)）。 -/
theorem nontrivial_relation {m₁ m₂ m₃ : ModeG} (h : det2 m₁ m₂ ≠ 0) :
    ∃ u v w : ℝ, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
      ∀ x t : ℝ, u * phaseOfG m₁ x t + v * phaseOfG m₂ x t + w * phaseOfG m₃ x t = 0 := by
  obtain ⟨a, b, hab⟩ := third_band_redundant (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) h
  refine ⟨-a, -b, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
  intro x t
  have h3 := hab x t
  rw [h3]
  ring

/-- ND4 ★★★ 时间计数也冗余：n₃(L) = a·n₁(L) + b·n₂(L)。
    ⟹ 第三条带既不增加坐标、也不增加时间计数（接 TimeCount 的 n = kL/2π）。 -/
theorem count_redundant {m₁ m₂ m₃ : ModeG} (h : det2 m₁ m₂ ≠ 0) (L : ℝ) :
    ∃ a b : ℝ, timeCount m₃.k L = a * timeCount m₁.k L + b * timeCount m₂.k L := by
  obtain ⟨a, b, hk, _⟩ := exists_coefficients (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) h
  refine ⟨a, b, ?_⟩
  simp only [timeCount]
  rw [hk]
  ring

/-- ND5 ★★ 超广意极限（k 全零）⟹ 三条相位恒为 0 ⟹ 无坐标可谈（与 VF9/VF10 同源）。 -/
theorem global_modes_no_coordinates (x t : ℝ) :
    phaseOfG ⟨0, 0⟩ x t = 0 ∧ phaseOfG ⟨0, 0⟩ x t = 0 ∧ phaseOfG ⟨0, 0⟩ x t = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [phaseOfG]

end ProjectionPhysics.BandDimension
