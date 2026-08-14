-- ProjectionPhysics — 黑洞与虫洞的流动结构（探索）
--
-- 主线公设（leo）：引力 = 空间流动的非均匀性（SG：Gordon 度规
-- g = [[1−v²/c², v/c²], [v/c², −1/c²]]，弱场 Φ = ½v² 已证 SG11）。
-- 光子 = 完全随空间流动（SLS2，dτ = 0）。
--
-- 本模块回答：在流动假设下，黑洞和虫洞的结构发生什么变化？
-- 结论（本模块证的代数内核）：
--
--   BH1 ★ 视界 = 光速面：g_tt = 1 − v²/c² = 0 ⟺ |v| = c。
--       黑洞 = 空间流动速度 ≥ c 的区域（v ≥ c ⟹ g_tt ≤ 0）。
--   BH2 向外光子的世界线：Gordon 度规中类光解 dx = (v − c)dt
--       （相对空间向外 c，被流动抵消）——代入 dτ² = 0 是代数恒等。
--   BH3 ★ 逃逸不可能定理：v ≥ c 时向外光子坐标位移 (v−c)dt ≥ 0
--       （x 轴指向内）——视界处冻结 (v=c ⟹ dx=0)，内部仍被拖向内
--       （v>c ⟹ dx>0）。逃逸需要流动亚光速（BH4 逆否）。
--   BH5–BH6 白洞 = 流反转：v ↦ −v 只翻转 g_tx 符号，g_tt 不变
--       （只依赖 v²）⟹ 白洞视界与黑洞同位置，流向外（源）。
--   BH7 内部角色互换种子：v > c ⟹ g_tt < 0（类时/类空互换）。
--   WH1 喉部恢复光锥：喉部（v = 0）⟹ g_tt = 1（平直）。
--
-- 诚实边界（写死，防过度声称）：
--   - BH1/BH2/BH3 是 Gordon 度规的直接代数推论，与 Hamilton–Lisle
--     河流模型（2008, "The river model of black holes", Am. J. Phys.
--     76, 519——Schwarzschild 解 = 空间向内流动 + 平直空间）精确同构。
--     本模块是仓库公设语言的重述：黑洞结构在流动假设下**与 GR 完全
--     一致**（视界 r_s = 2GM/c² 不变），变化只在解释层。
--   - 虫洞需要 3+1 维流场 + 场方程 + 喉部负能量源项（GR 的 NEC 违背
--     在流动语言 = 流源）；仓库目前只有 1+1 维 Gordon 骨架，本模块
--     只给出"喉部 = v 峰值 < c 的可穿越流管"的代数种子与几何需求清单
--     （见 wiki theory-blackhole-wormhole.md §5）。
--   - 本模块不加内核行，放 Explorations/。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Abs

import ProjectionPhysics.SpaceGravity
import ProjectionPhysics.SpaceMetric

noncomputable section

namespace ProjectionPhysics

/-- Gordon 度规的时间-时间分量：g_tt = 1 − v²/c²。 -/
def gordonGtt (v c : ℝ) : ℝ :=
  1 - v ^ 2 / c ^ 2

/-! ### BH1. 视界 = 光速面 -/

/-- ★ 视界 = 光速面：g_tt = 0 ⟺ 空间流动速度达到光速（|v| = c）。
    黑洞 = 空间流动 ≥ c 的区域；光子随空间流动（SLS2）无法逆流逃逸。 -/
theorem horizon_iff_light_speed_flow (v c : ℝ) (hc : c ≠ 0) :
    gordonGtt v c = 0 ↔ v = c ∨ v = -c := by
  unfold gordonGtt
  constructor
  · intro h
    have hv2 : v ^ 2 = c ^ 2 := by
      field_simp [hc] at h
      nlinarith
    exact Iff.mp (abs_eq_abs (a := v) (b := c))
      (Iff.mp (sq_eq_sq_iff_abs_eq_abs v c) hv2)
  · rintro (hv | hv)
    · rw [hv]
      field_simp [hc]
      ring
    · rw [hv]
      field_simp [hc]
      ring

/-- 黑洞 = 流动 ≥ c 的区域：v ≥ c ⟹ g_tt ≤ 0（度规时间分量不再为正）。 -/
theorem horizon_region_gtt_nonpos (v c : ℝ) (hc : 0 < c) (hv : c ≤ v) :
    gordonGtt v c ≤ 0 := by
  unfold gordonGtt
  have hv2 : c * c ≤ v * v := mul_self_le_mul_self (le_of_lt hc) hv
  field_simp [ne_of_gt hc]
  nlinarith

/-! ### BH2–BH4. 向外光子与逃逸不可能 -/

/-- ★ 向外光子的 Gordon 世界线：dx = (v − c)dt（相对空间向外 c，
    被内向流动 v 抵消）——类光条件 dτ² = 0 是代数恒等。
    视界 v = c ⟹ dx = 0（冻结）；内部 v > c ⟹ dx > 0（仍向内）。 -/
theorem gordon_outward_photon_proper_time_zero (v c dt : ℝ) (hc : c ≠ 0) :
    SpaceGravity.gordonProperTimeSq v c dt ((v - c) * dt) = 0 := by
  unfold SpaceGravity.gordonProperTimeSq
  field_simp [hc]
  ring

/-- ★ 逃逸不可能定理：视界及内部（v ≥ c），向外光子的坐标位移仍 ≥ 0
    （x 轴指向内）——光子无法逃出黑洞。 -/
theorem outward_photon_cannot_escape (v c dt : ℝ) (hv : c ≤ v) (hdt : 0 < dt) :
    0 ≤ (v - c) * dt := by
  have hvc : 0 ≤ v - c := by nlinarith
  exact mul_nonneg hvc (le_of_lt hdt)

/-- 视界冻结：v = c 处向外光子坐标位移 = 0（外部观测者看到光停住）。 -/
theorem outward_photon_frozen_at_horizon (v c dt : ℝ) (hv : v = c) :
    (v - c) * dt = 0 := by
  rw [hv]
  ring

/-- 逃逸 ⟺ 流动亚光速：向外光子真的向外（dx < 0）要求 v < c。
    （BH3 的逆否——逃逸的唯一条件是空间流动慢于光。） -/
theorem escape_requires_sublight_flow (v c dt : ℝ) (hdt : 0 < dt)
    (hdx : (v - c) * dt < 0) :
    v < c := by
  have ha : v - c < 0 := by
    by_contra hnot
    have ha0 : 0 ≤ v - c := le_of_not_gt hnot
    have hnonneg : 0 ≤ (v - c) * dt := mul_nonneg ha0 (le_of_lt hdt)
    linarith
  linarith

/-! ### BH5–BH6. 白洞 = 流反转 -/

/-- 白洞 = 时间反转的黑洞（空间向外喷出，v ↦ −v）。
    g_tt 只依赖 v²，流反转不改变视界位置。 -/
theorem white_hole_gtt_invariant (v c : ℝ) :
    gordonGtt (-v) c = gordonGtt v c := by
  unfold gordonGtt
  ring

/-- 流反转翻转 g_tx（流动方向的度规分量变号）——白洞的流是源不是汇。 -/
theorem white_hole_gtx_flips (v c : ℝ) :
    (SpaceGravity.gordonMetric (-v) c) ⟨0, by decide⟩ ⟨1, by decide⟩ =
      -(SpaceGravity.gordonMetric v c) ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  unfold SpaceGravity.gordonMetric
  simp
  ring

/-! ### BH7. 内部角色互换种子 -/

/-- 黑洞内部 v > c ⟹ g_tt < 0：时间分量变负——类时/类空角色互换的
    代数种子（GR 的"内部 r 类时"在流动语言 = 流动本身超光速）。 -/
theorem gordonGtt_negative_inside_horizon (v c : ℝ) (hc : 0 < c) (hv : c < v) :
    gordonGtt v c < 0 := by
  unfold gordonGtt
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hcabs : |c| = c := abs_of_pos hc
  have hvpos : 0 < v := lt_trans hc hv
  have hvabs : |v| = v := abs_of_pos hvpos
  have hlt : |c| < |v| := by rw [hcabs, hvabs]; exact hv
  have hv2 : c ^ 2 < v ^ 2 := (sq_lt_sq).mpr hlt
  have hnum : c ^ 2 - v ^ 2 < 0 := by linarith [hv2]
  calc
    1 - v ^ 2 / c ^ 2 = (c ^ 2 - v ^ 2) / c ^ 2 := by field_simp [ne_of_gt hc]
    _ < 0 := div_neg_of_neg_of_pos hnum hc2

/-! ### WH1. 虫洞喉部：亚光速流管通道 -/

/-- 喉部（v = 0）恢复平直：g_tt = 1——可穿越虫洞的喉部必须是
    v 的亚光速峰值（|v| < c 处处），与黑洞的单调趋 c 不同。 -/
theorem wormhole_throat_restores_light_cone (c : ℝ) :
    gordonGtt 0 c = 1 := by
  unfold gordonGtt
  ring

/-- 喉部向外光子恢复光速：v = 0 ⟹ dx = −c·dt（正常光锥，无冻结）。 -/
theorem throat_outward_photon_moves_outward (c dt : ℝ) (hc : 0 < c) (hdt : 0 < dt) :
    (0 - c) * dt < 0 := by
  have hneg : 0 - c < 0 := by
    rw [zero_sub]
    exact neg_neg_of_pos hc
  exact mul_neg_of_neg_of_pos hneg hdt

/-! ### 结论注释（不证，属数值/几何侧） -/

-- BH1–BH7 + WH1 合读：
--   黑洞在流动假设下结构与 GR 完全一致（视界 = 光速面 v = c = r_s；
--   内部 v > c，光子被超光速流拖向奇点；外部观测者看到的光子在视界
--   冻结——均为 Hamilton–Lisle 河流模型的仓库语言重述）。
--   虫洞 = 亚光速流管通道（喉部 v 峰值 < c），需要 3+1 维流场 + 场
--   方程 + 喉部负能量源项（GR NEC 违背的流动语言）；1+1 维骨架只能
--   给出喉部光锥恢复（WH1）与几何需求清单——数值/图像见
--   scripts/verify_blackhole_wormhole.py，完整清单见 wiki。

end ProjectionPhysics
