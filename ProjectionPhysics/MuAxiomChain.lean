-- ProjectionPhysics — MuAxiomChain：μ 主动产生假设（H1）下的分步闭链合成（MAC1–MAC6）
--
-- 2026-10-19 leo 收编：「把这个事情当成是已经解决了的实验缺口。我的脑子里已经有
-- 基本的物理来源了，而且代码和数学模型都已经建好了，现在是要去验证它。」
-- 同日更正：「**不能让 μ 一步到位**。我们可以开始计算，但不是一步到位。我们的
-- 推导是一步一步来的。」
--
-- ── 假设 H1（leo 提供物理来源，仓库只验证后果链；只承诺第一环）─────────
--   电磁时变场驱动空间流起伏变化（Q_A 改变），产生**有限**增益 η > 0。
--   η = flattenProgress A v v₀ = 1 − Q_A(v)/Q_A(v₀)（MUFC TD11）。
--   η 是几何/场配置的有限输出，符号可变（FRC 半径差几何给 η<0，同半径退化
--   给 η=1 上界）；数值由 G1/D1 首次标定（无实验证据）。不承诺一步到位。
--
-- ── 本模块合成什么（全部复用已有定理，不新增公设）────────────────────
--   **头条是分步语句 MAC4/MAC6**；MAC1/MAC3（抹平一次 ⟹ μ=1）是极限上界
--   （= MUFC TD14a，已有），不是递推头条。
--   MAC4 进窗判据      (1−η)ⁿ(1−μ₀) ≤ 1−μT ⟹ μ_n ≥ μT（TD7 闭式）
--   MAC5 有限步实例    μ₀=0.15、η=0.5 ⟹ 12 步到 μ≥0.9997（非一步）
--   MAC6a 有限步不可达 1（TD8，不一步到位）；MAC6b 关断即停留（TD19 语义）
--   MAC1/MAC3 极限上界 抹平一次 ⟹ μ=1 ⟹ m_eff=0 ⟹ 随流 dτ=0（TD14a+AMC1+AMC2）
--
-- ── 诚实边界 ─────────────────────────────────────────────────────────
--   · H1 只承诺「η > 0 有限」，不承诺一步到位；η 数值待 G1/D1 标定。
--   · 抹平功率从哪来 = 原第二输入缺口，由 H1 收编为假设后不再登记为缺口，
--     但仍无实验证据；G1/D1 从「存在性判决」迁移为「首次标定」。
--   · 无新物理预言；数值锚点全部对位既有产物。

import ProjectionPhysics.MuFieldCoupling
import ProjectionPhysics.MassCancellation

noncomputable section

namespace ProjectionPhysics.MuAxiomChain

open ProjectionPhysics.GravityControl
open ProjectionPhysics.MuFieldCoupling
open PlasmaDynamics
open MassCancellation

variable {ι : Type} [DecidableEq ι]

/-- ★★ MAC1（= MUFC TD14a 重述）：抹平一次（起伏能量清零）⟹ μ 一步到 1。
    H1 公设下这是「电磁驱动抹平」的直接后果：η=1 ⟹ 单步满增益。 -/
theorem mac1_flatten_once_mu_one (A : Finset ι) (hA : A.Nonempty) (v₀ v : ι → ℝ)
    (μ : ℝ) (h0 : fluctuationEnergy A v₀ ≠ 0) :
    muAfterFlatten A v₀ v μ = 1 :=
  muAfterFlatten_eq_one A hA v₀ v μ h0

/-- ★ MAC2（AMC1 实例）：μ = 1 ⟹ 有效锚定质量 m_eff = s(1−μ) = 0。
    质量取消对任意锚定强度 s 成立（电子/质子/原子同一代数）。 -/
theorem mac2_mu_one_zero_mass (s : ℝ) : effectiveAnchor s 1 = 0 := by
  unfold effectiveAnchor
  ring

/-- ★★★ MAC3（合成链，本模块核心）：抹平一次 ⟹ μ=1 ⟹ m_eff=0 ⟹ 随流 dτ=0。
    链 = TD14a（MUFC）+ AMC1（MassCancellation）+ AMC2（MassCancellation），
    全部是既有定理的合成——「公设 H1 下质量取消到随流」的机器检验。 -/
theorem mac3_flatten_chain_comoving (A : Finset ι) (hA : A.Nonempty) (v₀ v : ι → ℝ)
    (μ s : ℝ) (h0 : fluctuationEnergy A v₀ ≠ 0) :
    deviationFromFlow (effectiveAnchor s (muAfterFlatten A v₀ v μ)) = 0 := by
  rw [muAfterFlatten_eq_one A hA v₀ v μ h0]
  have hz : MassCancellation.anchorMassSq (effectiveAnchor s 1) = 0 := by
    unfold MassCancellation.anchorMassSq effectiveAnchor
    ring
  exact amc2_massless_comoving (effectiveAnchor s 1) hz

/-- ★ MAC4（TD7 闭式的可达判据）：μ_n = 1 − (1−η)ⁿ(1−μ₀) ⟹
    「(1−η)ⁿ(1−μ₀) ≤ 1−μT」⟺「n 步后 μ ≥ μT」。
    窗口可达 ⟺ 剩余容量被吃到目标以下——纯代数，是关闭步判据 TD21 的
    同族语句（TD21 问「何时关窗」，这里问「何时进窗」）。 -/
theorem mac4_reach_window_iff (μ₀ η μT : ℝ) (n : ℕ)
    (hn : (1 - η) ^ n * (1 - μ₀) ≤ 1 - μT) :
    μT ≤ muChain μ₀ η n := by
  rw [muChain_closed_form]
  nlinarith

/-- ★★ MAC5（数值实例，对位 verify_mu_axiom_chain.py 锚点）：
    μ₀=0.15、η=0.5（径向容差 0.240 m 内可达的增益，design-two-flow-ring-gravity
    容差表）⟹ 12 步到 μ ≥ 0.9997（输运解锁门槛）。 -/
theorem mac5_window_reached_example :
    (0.9997 : ℝ) ≤ muChain 0.15 0.5 12 := by
  rw [muChain_closed_form]
  norm_num

/-- ★ MAC6a（= TD8 重述）：0<η<1 时任意有限步 μ_n < 1——
    质量永不归零（天花板纪律的代数核，恒定增益必停在 1 之下）。 -/
theorem mac6a_finite_steps_below_one (μ η : ℝ) (hμ : μ < 1) (hη0 : 0 < η) (hη1 : η < 1) :
    ∀ n : ℕ, muChain μ η n < 1 :=
  muChain_lt_one μ η hμ hη0 hη1

/-- ★ MAC6b（反馈关断 TD19 语义）：在 μT 处关断增益（η=0）⟹ μ 停留在 μT。
    「停在窗口」的代数内容：注入停止 = 状态冻结，约束时间可任意延续。 -/
theorem mac6b_freeze_at_window (μT : ℝ) : muChain μT 0 1 = μT := by
  simp [muChain, muStep]

/-! ### 控制律（MAC7–MAC10，2026-10-19 续：S5 的一般化）

S5 的「末步调小增益 + 关断」写成显式反馈律：

    η_control(μ) = 0                          if μ ≥ μT   （关断）
                 = min(η_inj, (μT−μ)/(1−μ))   if μ < μT   （钳制到精确落窗）

性质（全部纯代数，复用 muStep/TD 语义）：
    MAC7a 单步不越目标：η ≤ (μT−μ)/(1−μ) ⟹ μ+η(1−μ) ≤ μT
    MAC7b 控制律单步不越目标（min 的两支都 ≤ ramp）
    MAC8  归纳不变量：控制律轨道 μ_n ≤ μT 恒成立（μT < 1 ⟹ 永不越天花板）
    MAC9  钳制未激活段与开环一致：η_inj ≤ ramp 时 η_control = η_inj
          ⟹ 进窗步数与开环相同（数值对位 S4 的 {2,2,4,12,36}）
    MAC10 到目标即冻结：μT ≤ μ ⟹ μ_{n+1} = μ_n（关断即停留，TD19）
-/

/-- 反馈控制律：μ ≥ μT 时关断（η=0）；否则取「注入增益」与「精确落窗所需增益」的较小者。 -/
noncomputable def etaControl (μT ηInj μ : ℝ) : ℝ :=
  if μT ≤ μ then 0 else min ηInj ((μT - μ) / (1 - μ))

/-- 闭环轨道：μ_{n+1} = muStep μ_n (etaControl μT ηInj μ_n)。 -/
noncomputable def muControl (μT ηInj μ₀ : ℝ) : ℕ → ℝ
  | 0 => μ₀
  | n + 1 => muStep (muControl μT ηInj μ₀ n) (etaControl μT ηInj (muControl μT ηInj μ₀ n))

/-- ★ MAC7a（单步不越目标）：η ≤ (μT−μ)/(1−μ) 且 η ≥ 0 ⟹ μ 一步不越过 μT。
    这是「末步调小增益」的代数内核：增益最多吃掉剩余容量 (μT−μ)。 -/
theorem mac7_clamped_step_le_target (μT η μ : ℝ) (hμle : μ ≤ μT) (hμ : μ < 1)
    (hη : 0 ≤ η) (h : η ≤ (μT - μ) / (1 - μ)) :
    muStep μ η ≤ μT := by
  unfold muStep
  have hb : 1 - μ ≠ 0 := by linarith
  have hdiff : 0 ≤ 1 - μ := by linarith
  have hdiv : η * (1 - μ) ≤ ((μT - μ) / (1 - μ)) * (1 - μ) :=
    mul_le_mul_of_nonneg_right h hdiff
  have hdiv' : η * (1 - μ) ≤ μT - μ := by
    calc
      η * (1 - μ) ≤ ((μT - μ) / (1 - μ)) * (1 - μ) := hdiv
      _ = μT - μ := by field_simp [hb]
  nlinarith

/-- ★★ MAC7b（控制律单步不越目标）：μ ≤ μT、0 ≤ η_inj、μT < 1 时，
    闭环一步 μ_{n+1} = muStep μ (etaControl μT ηInj μ) ≤ μT。
    min 的两支都被 ramp 钳住（关断支 η=0 不变，钳制支走 MAC7a）。 -/
theorem mac7_control_step_le_target (μT ηInj μ : ℝ) (hμle : μ ≤ μT) (hμ : μ < 1)
    (hη : 0 ≤ ηInj) (hT : μT < 1) :
    muStep μ (etaControl μT ηInj μ) ≤ μT := by
  unfold etaControl
  by_cases hgate : μT ≤ μ
  · rw [if_pos hgate]
    simp [muStep]
    exact hμle
  · rw [if_neg hgate]
    have hlt : μ < μT := by linarith
    have hramp0 : 0 ≤ (μT - μ) / (1 - μ) := by
      exact div_nonneg (by linarith) (by linarith)
    have hmin_le : min ηInj ((μT - μ) / (1 - μ)) ≤ (μT - μ) / (1 - μ) :=
      min_le_right _ _
    have hmin0 : 0 ≤ min ηInj ((μT - μ) / (1 - μ)) := le_min hη hramp0
    exact mac7_clamped_step_le_target μT (min ηInj ((μT - μ) / (1 - μ))) μ hμle hμ hmin0 hmin_le

/-- ★★★ MAC8（控制律不变量）：闭环轨道 ∀ n, μ_n ≤ μT。
    配合 μT < FC11 天花板（数值层），这是「永不越天花板」的机器保证——
    开环恒定 η 在 n*=162 越界（S6a），闭环在结构上不可能越界。 -/
theorem mac8_control_invariant (μT ηInj μ₀ : ℝ) (hμ0le : μ₀ ≤ μT) (hμ0 : μ₀ < 1)
    (hη : 0 ≤ ηInj) (hT : μT < 1) :
    ∀ n : ℕ, muControl μT ηInj μ₀ n ≤ μT := by
  intro n
  induction n with
  | zero =>
      simp [muControl]
      exact hμ0le
  | succ k ih =>
      change muStep (muControl μT ηInj μ₀ k) (etaControl μT ηInj (muControl μT ηInj μ₀ k)) ≤ μT
      exact mac7_control_step_le_target μT ηInj (muControl μT ηInj μ₀ k) ih
        (lt_of_le_of_lt ih hT) hη hT

/-- ★ MAC9（钳制未激活段与开环一致）：μ < μT 且 η_inj ≤ ramp 时
    η_control = η_inj —— 进窗前的轨迹与开环完全相同 ⟹ 进窗步数与开环一致。 -/
theorem mac9_clamp_inactive (μT ηInj μ : ℝ) (hμlt : μ < μT)
    (hη : ηInj ≤ (μT - μ) / (1 - μ)) :
    etaControl μT ηInj μ = ηInj := by
  unfold etaControl
  rw [if_neg (not_le.mpr hμlt), min_eq_left hη]

/-- ★ MAC10（到目标即冻结）：μT ≤ μ 时闭环一步不变（η_control = 0）。
    进窗后 μ ≡ μT，约束时间 τ_E(μT) 可持续任意久（TD19 关断语义）。 -/
theorem mac10_control_freeze (μT ηInj μ : ℝ) (hμ : μT ≤ μ) :
    muStep μ (etaControl μT ηInj μ) = μ := by
  unfold etaControl
  rw [if_pos hμ]
  simp [muStep]

end ProjectionPhysics.MuAxiomChain

end
