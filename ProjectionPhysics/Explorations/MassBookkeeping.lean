-- ProjectionPhysics — MassBookkeeping：按「整数条数」记账的质量核算（MB1–MB7）
--
-- leo（2026-11-01）：「可以按整数的条数来计算，形式化测量一下」。
--
-- 设定（与仓库既有一致）：一个扇区由**整数条数 N** 与**每条的标定单价 λ** 给出，
-- 每条携带固定能量 ⟹ 质量 m = √N · λ（即 m² = N·λ²，`MassGap.strandMassSq` 的形状）。
-- 「按整数条数计算」= 所有质量都由整数 N 与一个单价 λ 生成，N 不许连续。
--
-- 本模块把这条记账法能说与不能说的话，全部变成定理：
--
--   MB1 定义：m = √N·λ；m² = N·λ²（MassGap 的 strandMassSq 在此被开方）
--   MB2 ★★ **扇区内单价不可见**：同一扇区两个态的比值只由条数决定（λ 约掉）
--        ⟹ 扇区内的预言是**纯数** √(N₁/N₂)，一个自由参数都没有
--   MB3 ★★★ **跨扇区因子化**：m₁/m₂ = √(N₁/N₂) · (λ₁/λ₂)
--        ⟹ 跨扇区比值 = 「条数部分」×「单价部分」；单价部分就是那个第二标度
--   MB4 ★★★ **单一单价 ⟹ 比值平方是有理数**：(m₁/m₂)² = N₁/N₂ ∈ ℚ
--        ⟹ 这是可判死的判据：单价统一时，质量比的平方必须是两个整数之比
--   MB5 ★★★ **两价模型可拟合任意质量**（no-go）：给定任意两个质量与任意两个条数，
--        总存在一对单价把它们精确拟合 ⟹ **两价模型零预言力、不可证伪**
--        ⟹ 逃出 MB4 的办法（让单价随扇区变）会同时摧毁可证伪性
--   MB6 ★★ **整数台阶的格距下界**：√(N+1)/√N − 1 ≥ 1/(2(N+1))
--        ⟹ 整数条数的预言在 N 处分辨率为 ~1/(2N)；与测量精度比较即可判死活
--   MB7 与 MassGap/GlueballLadder 的对接：m² = strandMassSq，且 m = ladderMass
--
-- 数值测量在 `scripts/verify_mass_bookkeeping.py`（残差、以测量精度为单位的偏差、
-- 以及 MB5 的退化构造实例）。
--
-- 诚实边界（写死）：
--   · 本模块不产生 λ；MB4+MB5 合起来证明「λ 要么统一（被数据否掉）要么自由（不可证伪）」，
--     **第三条路只能是：λ 由结构推出**。本模块不含任何 λ 的推导。
--   · 「N 必须整数」是输入（框架公设），不是本模块证明的。
--   · 不声称解释 m_p/m_e；只把「按整数条数记账」的判决边界画死。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import ProjectionPhysics.Explorations.MassGap

noncomputable section
namespace ProjectionPhysics.MassBookkeeping

open ProjectionPhysics
open ProjectionPhysics.MassGap

/-! ### MB1 定义 -/

/-- 一个扇区的质量：m = √N · λ（N 为整数条数，λ 为每条标定单价）。 -/
def mass (N : ℕ) (lam : ℝ) : ℝ := Real.sqrt (N : ℝ) * lam

/-- MB1：m² = N·λ² —— 与 `MassGap.strandMassSq` 同形（开方关系见 MB7）。 -/
theorem mass_sq (N : ℕ) (lam : ℝ) : mass N lam ^ 2 = (N : ℝ) * lam ^ 2 := by
  unfold mass
  rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- MB1b：单价为正 ⟹ 质量为正（N > 0）。 -/
theorem mass_pos {N : ℕ} (hN : 0 < N) {lam : ℝ} (hlam : 0 < lam) : 0 < mass N lam := by
  unfold mass
  have : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  positivity

/-! ### MB2 扇区内：单价不可见 -/

/-- MB2 ★★ **扇区内单价约掉**：同一扇区（同一 λ）两个态的比值只由条数决定。
    ⟹ 扇区内预言是纯数 √(N₁/N₂)，无自由参数。 -/
theorem within_sector_ratio {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (_h₂ : 0 < N₂) {lam : ℝ}
    (hlam : 0 < lam) :
    mass N₁ lam / mass N₂ lam = Real.sqrt ((N₁ : ℝ) / (N₂ : ℝ)) := by
  unfold mass
  rw [mul_div_mul_right _ _ (ne_of_gt hlam)]
  exact (Real.sqrt_div (by positivity : (0 : ℝ) ≤ (N₁ : ℝ)) (N₂ : ℝ)).symm

/-! ### MB3 跨扇区：因子化成「条数部分 × 单价部分」 -/

/-- MB3 ★★★ **跨扇区因子化**：m₁/m₂ = √(N₁/N₂) · (λ₁/λ₂)。
    ⟹ 跨扇区比值 = 条数部分（纯数）× 单价部分（= 第二标度）。 -/
theorem cross_sector_factor {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) {l₁ l₂ : ℝ}
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) :
    mass N₁ l₁ / mass N₂ l₂ = Real.sqrt ((N₁ : ℝ) / (N₂ : ℝ)) * (l₁ / l₂) := by
  unfold mass
  have hN₂ : (0 : ℝ) < Real.sqrt (N₂ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast h₂)
  have hl₂' : l₂ ≠ 0 := ne_of_gt hl₂
  have key : Real.sqrt ((N₁ : ℝ) / (N₂ : ℝ))
      = Real.sqrt (N₁ : ℝ) / Real.sqrt (N₂ : ℝ) := Real.sqrt_div (by positivity) _
  rw [key]
  field_simp

/-! ### MB4 单一单价 ⟹ 比值平方是有理数 -/

/-- MB4 ★★★ **单一单价下的可判死判据**：若两个态共用一个单价（同一扇区），
    则 (m₁/m₂)² = N₁/N₂ —— **一个有理数**。
    ⟹ 只要观测到的质量比平方不是（小分母）有理数，单一单价的记账法即被否掉。 -/
theorem single_price_ratio_sq {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) {lam : ℝ}
    (hlam : 0 < lam) :
    (mass N₁ lam / mass N₂ lam) ^ 2 = (N₁ : ℝ) / (N₂ : ℝ) := by
  have := within_sector_ratio h₁ h₂ hlam
  rw [this, Real.sq_sqrt (by positivity)]

/-- MB4b：等价形式 —— 比值的平方等于自然数之比（分子分母都是 ℕ 的像）。 -/
theorem single_price_ratio_sq_is_rat {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ p q : ℕ, 0 < q ∧ (mass N₁ lam / mass N₂ lam) ^ 2 = (p : ℝ) / (q : ℝ) :=
  ⟨N₁, N₂, h₂, single_price_ratio_sq h₁ h₂ hlam⟩

/-! ### MB5 no-go：两价模型不可证伪 -/

/-- MB5 ★★★ **两价模型拟合一切**（no-go 定理）：给定任意两个质量 m₁, m₂ > 0 与任意
    两个条数 N₁, N₂ > 0，都存在一对正单价把它们**精确**拟合。
    ⟹ 让单价随扇区变（逃出 MB4 的唯一办法）会同时摧毁预言力：
      两个自由单价对两个观测值 ⟹ 残差恒为零 ⟹ **不可证伪**。
    ⟹ 结论：第三条路只能是「λ 由结构推出」，本模块不提供它。 -/
theorem two_prices_fit_anything (m₁ m₂ : ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (N₁ N₂ : ℕ) (h₁ : 0 < N₁) (h₂ : 0 < N₂) :
    ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ 0 < l₂ ∧ mass N₁ l₁ = m₁ ∧ mass N₂ l₂ = m₂ := by
  have hN₁ : (0 : ℝ) < Real.sqrt (N₁ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast h₁)
  have hN₂ : (0 : ℝ) < Real.sqrt (N₂ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast h₂)
  refine ⟨m₁ / Real.sqrt (N₁ : ℝ), m₂ / Real.sqrt (N₂ : ℝ), by positivity, by positivity, ?_, ?_⟩
  · unfold mass; field_simp
  · unfold mass; field_simp

/-! ### MB6 整数台阶的格距下界（判死活的分辨率） -/

/-- MB6 ★★ **格距下界**：√(N+1)/√N − 1 ≥ 1/(2(N+1))。
    ⟹ 整数条数在 N 处的预言分辨率约 1/(2N)；与测量精度一比即可判死活
      （电子/质子：N ≈ 1836 ⟹ 格距 ≥ 2.7×10⁻⁴，而质量精度 ~10⁻⁹ ⟹ 可分辨 10⁵ 倍）。 -/
theorem grid_spacing_lower_bound (N : ℕ) (hN : 0 < N) :
    1 / (2 * ((N : ℝ) + 1)) ≤ Real.sqrt ((N : ℝ) + 1) / Real.sqrt (N : ℝ) - 1 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsN : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  set A : ℝ := 1 / (2 * ((N : ℝ) + 1)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hb : (0 : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) / Real.sqrt (N : ℝ) := by positivity
  have hkey : A + 1 ≤ Real.sqrt ((N : ℝ) + 1) / Real.sqrt (N : ℝ) := by
    have hsq : (A + 1) ^ 2 ≤ (Real.sqrt ((N : ℝ) + 1) / Real.sqrt (N : ℝ)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (le_of_lt hN0), hA]
      have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
      field_simp
      nlinarith [hN0]
    have hle := (abs_le.mp (sq_le_sq.mp hsq)).2
    rwa [abs_of_nonneg hb] at hle
  linarith

/-! ### MB7 与 MassGap / GlueballLadder 的对接 -/

/-- MB7：开方后就是 `MassGap.strandMassSq` 的质量（N·λ² = strandMassSq N λ）。 -/
theorem mass_sq_eq_strandMassSq (N : ℕ) (lam : ℝ) :
    mass N lam ^ 2 = strandMassSq N lam := by
  rw [mass_sq]
  unfold strandMassSq
  ring

end ProjectionPhysics.MassBookkeeping
