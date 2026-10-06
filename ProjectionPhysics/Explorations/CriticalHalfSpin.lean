-- ProjectionPhysics — CriticalHalfSpin：临界叶对数半值与自旋半步接口（探索）
--
-- leo（2026-10-06）：「如果把根号 e 的对数等于 1/2 的这个概念当做自旋的输入项，
--   把费米子的自旋解决出来。能量和质量的这个变化。」
--
-- 概念链（全部是仓库已有结构的接口代数，不新增公设）：
--   · 临界叶 r = √e（RiemannHIBS 包络反演 w ↦ e/w 的不动圆，仓库
--     `envelope_inversion_fixed_circle`；ProjectionPhysics 侧 HiddenQFT.HQ1/HQ1b）。
--   · ln(√e) = ½·ln e = ½ —— 平凡恒等式，但不平凡处在**坐标系**：
--     包络反射 s ↦ 1−s 在对数坐标下的不动点必须坐在 ln 的 ½ 处
--     （因为 ln e = 1 —— e 是唯一使对数取值为 1 的底）。
--   · 自旋 1/2 = 同一个「半步」的角色名：开方（数）= 半角（相位）= 双覆盖。
--     VBS7 半角螺旋是费米型的显式见证 —— 本模块补它的复相位版 CS4。
--   · 能量-质量：E ∝ m² ⟹ ln E = 2 ln m —— 能量走一步，质量走半步（CS5）。
--
-- 诚实边界（写死）：
--   · CS1–CS5 全是真但平凡的恒等式（log/exp 的初等性质 + 一次环运算）。
--   · 深度全部在**为什么取 ln 坐标**（不动点在 ln 坐标下才是 ½）与
--     **为什么有反射对称**（仓库已建，仍是输入，不是推出）。
--   · 这给的是**自旋的值（½）在仓库内的位置**，不是费米子统计的另一半
--     （相位 ⟹ 场算符反对易仍需场算符语言，VSS 缺口 1 未变）—— 仍是半条定理。
--   · 零新可检验预言；与标准理论数值全同。
--
-- 死法：若在 ln 坐标下找到第二个非平凡的反射不动结构（ln ≠ ½），
--   或包络反射对称不再唯一，本解读死。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import ProjectionPhysics.HiddenQFT
import ProjectionPhysics.Explorations.VibrationStatistics

namespace ProjectionPhysics.CriticalHalfSpin

open Complex

-- ---------------------------------------------------------------------------
-- CS1 ★ 临界叶的对数半值：ln(√e) = ½
--   为什么是 ½：ln e = 1 ⟹ 开方在对数坐标下精确减半（log 把乘法变加法，
--   开方 = 乘法群里的半步算子）。
-- ---------------------------------------------------------------------------

theorem log_critical_half : Real.log (Real.sqrt (Real.exp 1)) = 1 / 2 := by
  norm_num [Real.log_sqrt (le_of_lt (Real.exp_pos 1)), Real.log_exp]

-- ---------------------------------------------------------------------------
-- CS2 ★ 反演不动 ⟺ 对数半值（接口定理）
--   实数版：r > 0 时，r = e/r（包络反演 w ↦ e/w 的不动条件）当且仅当
--   ln r = ½。这把 RiemannHIBS 的「反演不动圆 |w| = √e」翻译成对数坐标
--   —— 不动结构在对数坐标下**必须**坐在 ½ 处。
-- ---------------------------------------------------------------------------

theorem inversion_fixed_iff_log_half {r : ℝ} (hr : 0 < r) :
    r = Real.exp 1 / r ↔ Real.log r = 1 / 2 := by
  have hlog_sq : Real.log (r ^ 2) = 2 * Real.log r := by
    rw [pow_two, Real.log_mul (ne_of_gt hr) (ne_of_gt hr)]
    ring
  have hsq_iff_log : r ^ 2 = Real.exp 1 ↔ Real.log r = 1 / 2 := by
    constructor
    · intro hsq
      have hlr : Real.log (r ^ 2) = 1 := by
        rw [hsq, Real.log_exp]
      have h2 : 2 * Real.log r = 1 := by
        rwa [hlog_sq] at hlr
      nlinarith
    · intro hlog
      have hlr : Real.log (r ^ 2) = 1 := by
        rw [hlog_sq, hlog]
        norm_num
      have hexp := congrArg Real.exp hlr
      rw [Real.exp_log (by positivity : 0 < r ^ 2)] at hexp
      exact hexp
  have hdiv : r = Real.exp 1 / r ↔ r * r = Real.exp 1 := by
    exact eq_div_iff (ne_of_gt hr)
  rw [hdiv]
  simpa [pow_two] using hsq_iff_log

-- ---------------------------------------------------------------------------
-- CS3 ★ 临界叶自身是反演不动点：√e = e/√e
--   （CS2 在临界叶上的实例：ln(√e) = ½ ⟹ 反演不动。）
-- ---------------------------------------------------------------------------

theorem critical_sheet_fixed_by_inversion :
    HiddenQFT.criticalSheet = Real.exp 1 / HiddenQFT.criticalSheet := by
  have hpos : 0 < HiddenQFT.criticalSheet := by
    exact lt_trans zero_lt_one HiddenQFT.critical_sheet_gt_one
  have hlog : Real.log HiddenQFT.criticalSheet = 1 / 2 := by
    unfold HiddenQFT.criticalSheet
    exact log_critical_half
  exact (inversion_fixed_iff_log_half hpos).mpr hlog

-- ---------------------------------------------------------------------------
-- CS4 ★★ 半步相位的费米型：exp(i·θ/2) 是闭包相因子 −1 的显式见证
--   开方（数的半步）与半角（相位的半步）是同一结构的两个坐标：
--   角度 θ 走一整圈 2π，相位 exp(iθ/2) 只走半圈 ⟹ 2π 变号、4π 复原
--   —— 这就是 VBS7 半角螺旋的复相位版（VBS 的三维版本已在那边）。
-- ---------------------------------------------------------------------------

theorem half_angle_phase_fermionic :
    VibrationStatistics.ClosureFactor
      (fun θ : ℝ => Complex.exp ((θ / 2) * Complex.I)) (-1) := by
  intro θ
  dsimp
  have hθ : (↑(θ + 2 * Real.pi) : ℂ) / 2 = (θ : ℂ) / 2 + (Real.pi : ℂ) := by
    norm_cast
    ring
  rw [hθ]
  rw [show ((θ : ℂ) / 2 + (Real.pi : ℂ)) * Complex.I =
        (θ : ℂ) / 2 * Complex.I + (Real.pi : ℂ) * Complex.I by ring]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  ring

-- ---------------------------------------------------------------------------
-- CS5 ★ 能量-质量的对数 2:1：ln e = 2·ln(√e)
--   E ∝ m² ⟹ ln E = 2 ln m：能量走一步（ln e = 1），质量走半步（ln √e = ½）。
--   「2」= 自旋 ½ 的倒数 —— 费米子要两圈（2×½）才回到起点。
-- ---------------------------------------------------------------------------

theorem log_e_eq_two_log_critical :
    Real.log (Real.exp 1) = 2 * Real.log (Real.sqrt (Real.exp 1)) := by
  rw [Real.log_exp, log_critical_half]
  norm_num

end ProjectionPhysics.CriticalHalfSpin