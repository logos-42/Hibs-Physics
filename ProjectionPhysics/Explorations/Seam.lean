-- ProjectionPhysics — Seam：字典接缝的机器检验形式
--
-- leo（2026-10-30，重启后第 1 轮攻防 → 防方裁决 (e)）：
--   「最该补强的一件事 = 形式化字典接缝：在 Lean 中证一条共享判据引理，
--    令 VF4/AT5/GD1 三处作为它的实例导出」
--
-- 接缝（论文 §7）：三块结构用三个词汇说同一句判据——
--   ① VF4（振动坐标非退化）：jacobian2 m₁ m₂ ≠ 0  ⟺  c₁ ≠ c₂      （需 k₁k₂ ≠ 0）
--   ② AT5（顺序可观测）    ：交换差 ≠ 0          ⟺  v_q ≠ v_p    （需 λ ≠ 0）
--   ③ GD2（一般色散退化）  ：det2 m₁ m₂ ≠ 0      ⟺  v_ph,1 ≠ v_ph,2（需 k₁k₂ ≠ 0）
-- 三者共享同一形状 = 整环公理的一次实例：a ≠ 0 → (a·(x−y) ≠ 0 ⟺ x ≠ y)。
-- 本模块把这个形状证为一条引理 `seam_iff`，再把三个判据逐一声明为它的实例。
-- ⟹ 「三判据同形」从评注层的可见对应升级为机器检验的对应。
--
-- 诚实边界（写死）：
--   · 本模块证明的是「三个判据是同一条初等形状的实例」，**不是**「时间序 = 坐标
--     非退化」。——识别层（v_i := c_i）仍是框架的提议，不在机器检验范围内。
--   · 三个实例各自的前提来自各自模块（k₁k₂ ≠ 0 / λ ≠ 0），不是新公设。
--   · 接缝的数学含量刻意为零（它就是整环公理的三个实例）；它的价值在
--     「显式化」——叙事中枢从声明变为被核验对象，而不是更深的数学。
--
-- 死法（写死）：
--   ① 若在任何实例里前提失效（k=0 或 λ=0）而判据仍被使用 ⟹ 接缝破裂；
--     论文已标注 k→0 退化（VF10）与平坦顺序盲（AT4），前提与实例一致。
--   ② 若有人把「三判据同形」读成「三事件同一」——本模块不含此类陈述。
--   ③ 若出现第四个判据不属于这个形状而接缝仍声称包含它 ⟹ 声称失效。

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import ProjectionPhysics.Explorations.VibrationFrame
import ProjectionPhysics.Explorations.AetherTime
import ProjectionPhysics.Explorations.DispersionGeneral

namespace ProjectionPhysics.Seam

open ProjectionPhysics.VibrationFrame
open ProjectionPhysics.AetherTime
open ProjectionPhysics.DispersionGeneral
open ProjectionPhysics.YangMillsSeed

variable {ι : Type}

/-- ★ 接缝共享形状：非零系数乘非零差 ≠ 0 ⟺ 差非零（整环公理）。 -/
theorem seam_iff {a x y : ℝ} (ha : a ≠ 0) : a * (x - y) ≠ 0 ↔ x ≠ y := by
  constructor
  · intro h hxy
    exact h (by rw [hxy, sub_self, mul_zero])
  · intro hxy
    exact mul_ne_zero ha (sub_ne_zero.mpr hxy)

/-- 接缝实例 VF4：振动坐标非退化 ⟺ 两带相速度不一致（k₁k₂ ≠ 0）。
    以 a := m₁.k·m₂.k 实例化 seam_iff。 -/
theorem seam_vf4 (m₁ m₂ : Mode) (hk₁ : m₁.k ≠ 0) (hk₂ : m₂.k ≠ 0) :
    jacobian2 m₁ m₂ ≠ 0 ↔ m₁.c ≠ m₂.c := by
  rw [jacobian2_eq]
  exact seam_iff (mul_ne_zero hk₁ hk₂)

/-- 接缝实例 AT5：顺序可观测（交换差非零）⟺ 场值差非零（λ ≠ 0）。
    以 a := λ² 实例化 seam_iff，交换差由 YM3 公式锁定。 -/
theorem seam_at5 {p q : ι} {lam : ℝ} {v : ι → ℝ} (hlam : lam ≠ 0) :
    OrderVisibleAt (sinkToPoint p lam) (sinkToPoint q lam) v p ↔ v q ≠ v p := by
  unfold OrderVisibleAt
  calc
    sinkToPoint p lam (sinkToPoint q lam v) p ≠ sinkToPoint q lam (sinkToPoint p lam v) p
        ↔ sinkToPoint p lam (sinkToPoint q lam v) p - sinkToPoint q lam (sinkToPoint p lam v) p ≠ 0 :=
          sub_ne_zero.symm
    _ ↔ lam ^ 2 * (v q - v p) ≠ 0 := by
          rw [sinkToPoint_commutator_formula]
    _ ↔ v q ≠ v p := seam_iff (pow_ne_zero 2 hlam)

/-- 接缝实例 GD2：一般色散下退化 ⟺ 两带相速度相同（k₁k₂ ≠ 0）。
    以 a := m₁.k·m₂.k 实例化 seam_iff（相位速度差为 phaseSpeedG m₂ − phaseSpeedG m₁，
    目标侧差一个顺序，经 ne_comm 对齐）。 -/
theorem seam_gd2 {m₁ m₂ : ModeG} (h₁ : m₁.k ≠ 0) (h₂ : m₂.k ≠ 0) :
    det2 m₁ m₂ ≠ 0 ↔ phaseSpeedG m₁ ≠ phaseSpeedG m₂ := by
  rw [det2_eq_speed_diff h₁ h₂]
  calc
    m₁.k * m₂.k * (phaseSpeedG m₂ - phaseSpeedG m₁) ≠ 0
        ↔ phaseSpeedG m₂ ≠ phaseSpeedG m₁ := seam_iff (mul_ne_zero h₁ h₂)
    _ ↔ phaseSpeedG m₁ ≠ phaseSpeedG m₂ := ne_comm

end ProjectionPhysics.Seam