-- ProjectionPhysics — VibrationChargeRadiation：加速电荷 ⟹ 反引力的推导链骨架（探索）
--
-- leo（2026-10-06）：「这个电子加速度成了一个反引力。因为有反引力场，4 种力统一了呀，
--   所以在这件事情上应该是可以推导出来的。」
--
-- 仓库已有结构的接口代数（不新增公设）。把「加速电荷 ⟹ 反引力 ⟹ 光子」拆成四步：
--
--   CR1 ★ 源时变 ⟹ 空间场时变（逆否：静态场 ⟹ 源静态）。
--         MS5 带源波动方程 ∂_t²C = c²∂_x²C + J：若 C 静态则 J 必须与时间无关；
--         故 J 时变（加速电荷 = 时变源）⟹ C 不可能静态。
--   CR2 ★ 空间场时变 ⟹ 核力通道激活：dC ≠ 0 ∧ m ≠ 0 ⟹ m·dC ≠ 0
--         （GQF2b 四通道的核力通道 m·dC，矢量光速变化通道）。
--   CR3  μ 的桥在框架内已存在（MuFieldCoupling TD11–TD18）：
--         η = flattenProgress = 1 − Q_A(v)/Q_A(v₀)，μ' = muStep μ η。
--         TD12：抹平一次 ⟹ η=1 ⟹ μ 一步到 1。
--         故断点不是「dC↦μ 的本构」，而是「谁提供抹平动作 / 抹平功率从哪来」
--         （TD18 原话：缺口从「η 是哪来的」变成「抹平功率是哪来的」）。
--   CR4 ★ μ=1 ⟹ 光子终点：质量归零（AMC1）∧ 中性（CF3）——GQP1 光子的代数终点。
--   CR5 ★ 条件链闭包：抹平一次 ⟹ μ=1 ⟹ 光子（TD12 + CR4 串联）。
--         这是「若有人抹平，则任意锚定物质变光子」的框架内条件改述；
--         断点压缩到「抹平动作的来源」（第二输入缺口，未变）。
--   CR6  负电荷 = 吸收态的语义接口：负电荷（汇，CF）↔ HQ iR 分支（吸收态，
--         开方不可逆沉没放能 HQ9a）。这是「为什么是负电荷」的三个候选锚点之一
--         （另两个：AMC5 正反抵消湮灭、黑洞=流场汇）；接口层，非定理。
--
-- 诚实边界（写死）：
--   · 所有定理都是初等代数（真但平凡）；物理语义重量集中在两处：
--     (a) CR1 在 1+1 维差分骨架（MS3/MS5 同款），3D 连续版未形式化；
--     (b) 「加速电荷 ⟹ 抹平动作」这一步**没有**框架内定理——flatten 是控制
--         操作 P_A（GCA5），需要外部施加者；电荷不会自动触发 flatten。
--   · CR6 是语义对应（解释层），不是推导：CF 的汇与 HQ 的 iR 是两套语言。
--   · 本链证明的是「若抹平发生，则任意物质变光子」的条件陈述，
--     不证明「加速电荷导致抹平」。无新可检验预言。
--
-- 死法：若 (a) 某个守恒律排除「时变源 ⟹ 抹平」这一接法，或
--   (b) CR1 的 3D 连续版失效，或 (c) 找到与 CR5 矛盾的反例，
--   则本链死（断点位置按反例形状移动）。

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ProjectionPhysics.Explorations.MaxwellSpace
import ProjectionPhysics.MassCancellation
import ProjectionPhysics.Explorations.VibrationChargeFlow
import ProjectionPhysics.PlasmaDynamics
import ProjectionPhysics.MuFieldCoupling
import ProjectionPhysics.HiddenQFT

namespace ProjectionPhysics.VibrationChargeRadiation

open ProjectionPhysics

-- ---------------------------------------------------------------------------
-- CR1 ★ 源时变 ⟹ 空间场时变
--   引理（逆否）：静态场 ⟹ 源静态。MS5 带源方程里若 Dt C ≡ 0，
--   则 J 不可能随时间变（否则波动方程被破坏）。
-- ---------------------------------------------------------------------------

/-- 静态空间场 ⟹ 源与时间无关：J 在相邻时间相等。
    证明：C 静态 ⟹ 波动算子两边二阶时间项为零且空间项不依赖 t，
    故 MS5 给出 J(t+1) = J(t)。 -/
theorem static_field_implies_static_source
    (C J : ProjectionPhysics.SpaceField) (c : ℝ)
    (hms : ∀ t x, Dt (Dt C) t x = c ^ 2 * Dx (Dx C) t x + J t x)
    (hstatic : ∀ t x, Dt C t x = 0) :
    ∀ t x, J (t + 1) x = J t x := by
  intro t x
  have hsame : ∀ t' x', C (t' + 1) x' = C t' x' := by
    intro t' x'
    have h := hstatic t' x'
    unfold Dt at h
    linarith
  -- 二阶时间项两边为零
  have hd2_1 : Dt (Dt C) t x = 0 := by
    unfold Dt
    simp [hsame]
  have hd2_2 : Dt (Dt C) (t + 1) x = 0 := by
    unfold Dt
    simp [hsame]
  -- 空间二阶差不依赖 t（C 静态）
  have hdx : Dx (Dx C) (t + 1) x = Dx (Dx C) t x := by
    unfold Dx
    simp [hsame]
  -- MS5 在 t 与 t+1 两处展开
  have h1 := hms t x
  rw [hd2_1] at h1
  have h2' : 0 = c ^ 2 * Dx (Dx C) t x + J (t + 1) x := by
    simpa [hd2_2, hdx] using hms (t + 1) x
  linarith

/-- ★ CR1：源时变（加速电荷 = 时变源）⟹ 空间场不可能静态。
    这是「加速电荷 ⟹ 核力通道」的入口：时变源挤出时变场。 -/
theorem source_time_varying_forces_field_varying
    (C J : ProjectionPhysics.SpaceField) (c : ℝ)
    (hms : ∀ t x, Dt (Dt C) t x = c ^ 2 * Dx (Dx C) t x + J t x)
    (hj : ∃ t x, J (t + 1) x ≠ J t x) :
    ¬ ∀ t x, Dt C t x = 0 := by
  intro hstatic
  have hs := static_field_implies_static_source C J c hms hstatic
  rcases hj with ⟨t, x, hne⟩
  exact hne (hs t x)

-- ---------------------------------------------------------------------------
-- CR2 ★ 空间场时变 ⟹ 核力通道激活（GQF2b 通道标注的 ℝ 标量版）
-- ---------------------------------------------------------------------------

/-- CR2：核力通道非零——边界条件 m ≠ 0、dC ≠ 0 保证 m·dC ≠ 0。 -/
theorem nuclear_channel_active {m dC : ℝ} (hm : m ≠ 0) (hdC : dC ≠ 0) :
    m * dC ≠ 0 :=
  mul_ne_zero hm hdC

-- ---------------------------------------------------------------------------
-- CR3 μ 的桥在框架内（MuFieldCoupling）；不再发明 κ 本构。
--   串接：抹平一次 ⟹ η=1 ⟹ muStep μ 1 = 1（TD12 + plasma muStep_full_gain）。
-- ---------------------------------------------------------------------------

/-- CR3（修）：μ 的框架内桥 = `muStep μ (flattenProgress ...)`。
    TD12（MuFieldCoupling）+ `muStep_full_gain`（PlasmaDynamics）：
    抹平一次 ⟹ 增益 η=1 ⟹ μ 一步到 1。
    这是本模块此前 CR3「κ:dC↦μ 模糊本构」的**修正**——断点不在发明
    新本构，而在「谁施加抹平动作」（GCA 的 flatten 是控制操作，需外部
    施加者；电荷不自动触发）。 -/
theorem mu_one_after_one_flatten
    {ι : Type} [DecidableEq ι] (A : Finset ι) (hA : A.Nonempty)
    (v v₀ : ι → ℝ) (μ : ℝ)
    (h0 : GravityControl.fluctuationEnergy A v₀ ≠ 0) :
    PlasmaDynamics.muStep μ (MuFieldCoupling.flattenProgress A (GravityControl.flatten A v) v₀) = 1 := by
  unfold PlasmaDynamics.muStep MuFieldCoupling.flattenProgress
  have hq : 1 - GravityControl.fluctuationEnergy A (GravityControl.flatten A v) /
      GravityControl.fluctuationEnergy A v₀ = 1 := by
    simpa [MuFieldCoupling.flattenProgress] using
      (MuFieldCoupling.flattenProgress_after_flatten A hA v v₀ h0)
  rw [hq]
  ring

-- ---------------------------------------------------------------------------
-- CR4 ★ μ=1 ⟹ 光子终点（AMC1 + CF3 组合）
-- ---------------------------------------------------------------------------

/-- CR4：μ=1 时任意锚定物质质量归零且呈中性。
    组合 AMC1（amc1_anti_gravity_cancels_any_mass）与 CF3（zero_is_neutral）。 -/
theorem photon_endpoint_of_mu_one (s : ℝ) :
    MassCancellation.anchorMassSq (MassCancellation.effectiveAnchor s 1) = 0 ∧
    ¬ VibrationChargeFlow.PositiveSource 0 ∧ ¬ VibrationChargeFlow.NegativeSink 0 := by
  constructor
  · exact MassCancellation.amc1_anti_gravity_cancels_any_mass s
  · exact VibrationChargeFlow.zero_is_neutral

-- ---------------------------------------------------------------------------
-- CR5 ★ 条件链闭包：抹平一次 ⟹ μ=1 ⟹ 光子
--   CR3 + CR4 串联：若有人对区域 A 抹平一次，则任意锚定物质 s 变成光子。
--   断点压缩到「抹平动作的来源」——框架内条件陈述完整，物理来源仍是第二输入缺口。
-- ---------------------------------------------------------------------------

/-- CR5：抹平一次 ⟹ 光子终点。
    （flatten 一次 ⟹ μ=1 [CR3]；μ=1 ⟹ 质量归零且中性 [CR4]。）
    这是「反引力 ⟹ 光子」在仓库代数里的完整条件链；
    flat 动作的物理来源（谁在抹平）未给出——第二输入缺口未变。 -/
theorem photon_after_one_flatten
    {ι : Type} [DecidableEq ι] (A : Finset ι) (hA : A.Nonempty)
    (v v₀ : ι → ℝ) (μ s : ℝ)
    (h0 : GravityControl.fluctuationEnergy A v₀ ≠ 0) :
    let μ' := PlasmaDynamics.muStep μ (MuFieldCoupling.flattenProgress A (GravityControl.flatten A v) v₀)
    MassCancellation.anchorMassSq (MassCancellation.effectiveAnchor s μ') = 0 ∧
    ¬ VibrationChargeFlow.PositiveSource 0 ∧ ¬ VibrationChargeFlow.NegativeSink 0 := by
  dsimp
  have hμ' : PlasmaDynamics.muStep μ
      (MuFieldCoupling.flattenProgress A (GravityControl.flatten A v) v₀) = 1 :=
    mu_one_after_one_flatten A hA v v₀ μ h0
  rw [hμ']
  exact photon_endpoint_of_mu_one s

-- ---------------------------------------------------------------------------
-- CR6 负电荷 = 吸收态（语义接口，非定理）
--   负电荷（汇，CF）的结构同位：黑洞 = 流场汇（MaxwellFlow）、
--   HQ iR = 开方流的吸收态（开方不可逆沉没放能 HQ9a：φ(R)−φ(iR)=δ+ε>0）。
--   这是「为什么是负电荷」的三个候选锚点之一，接口层留档，不做推导。 -/

/-- CR6 接口数据：负电荷（汇）与开方流吸收态（iR）的语义同位。
    注释性接口：CF 的 NegativeSink（∇·C<0，向内汇聚）↔ HQ 的 FlowTag.iR
    （吸收态，信息沉没）。物理对应是解释层；不作定理断言。 -/
def sinkAsAbsorptionTag : HiddenQFT.FlowTag := HiddenQFT.FlowTag.iR

end ProjectionPhysics.VibrationChargeRadiation