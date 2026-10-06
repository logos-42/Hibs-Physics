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
import ProjectionPhysics.GravityControl

namespace ProjectionPhysics.VibrationChargeRadiation

open ProjectionPhysics
open ProjectionPhysics.GravityControl
open scoped BigOperators

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

-- ---------------------------------------------------------------------------
-- CR7 ★ 解释层收口：收敛 = 抹平，负电荷 = 自然抹平者
--   框架内两套独立语言指向同一个几何动作：
--     · 负电荷（CF/GQF4）= 流散度 < 0 = 向内汇聚（∇·C < 0）
--     · 抹平（GCA/MuFieldCoupling）= 把区域起伏 Q_A 降到 0 = 使流动均匀
--   一个**收敛**的矢量场（四周向内流）在区域内部正是「把梯度抹平」：
--   越靠近中心，流速方向的梯度被压缩、流动趋均匀。
--   ⟹ 负电荷的「向内汇聚」在几何上就是「局部抹平」——
--   它**天然是**反引力场的局部载体（不需要外部施加者）。
--   这是对「谁在抹平」和「为什么是负电荷」的统一回答：
--   不是加速的电荷被抹平，而是**收敛流本身就是抹平动作**。
--
-- 诚实边界（解释层，写死）：
--   · 这是**语义同位**（两套语言的结构对应），不是 3D 解析定理——
--     「∇·C<0 ⟹ Q_A(C) 下降」需要连续 3D 散度 + 起伏泛函的严格关联，
--     仓库未形式化（明确未支持连续 ∇·/∇×）。
--   · 不证明「负电荷必然完全抹平」——收敛流只保证局部、渐进抹平
--     （源越强维持成本越高，AMC4），完全归零仍需 μ=1。
--   · 不改变第二输入缺口：收敛流的能量从哪来（维持源强）仍是 ε/g 系。
--   · 无新可检验预言；解释层与标准物理数值全同。
--
-- 死法：若 3D 连续版证明「收敛流在区域上**增加**起伏」（Q_A 上升），
--   或存在正散度场同样抹平（源与汇无差别），则 CR7 的解释死。 -/

/-- CR7：负电荷的「向内汇聚」= 抹平动作的结构同位（接口数据）。
    定义把「收敛流」作为抹平候选：流场散度符号为负（汇聚）即是
    「自然抹平者」的标记。这是 CR6 的几何化：不只是吸收态语义，
    而是把「汇 = 抹平」写成可引用接口。
    注：仅标记散度符号为负的流场为抹平候选，正散度（源）不是。 -/
def convergingFlowIsFlattenCandidate (divSign : ℝ) : Prop :=
  divSign < 0

/-- CR7b：负电荷源（汇）⟹ 抹平候选——连接 CF 的 NegativeSink 到抹平概念。
    若流场散度符号为负（负电荷 = 汇），则它是抹平候选。
    物理读法：向内收敛的流在几何上压缩梯度、趋均匀——
    负电荷本身就是「反引力场局部载体」的候选标记。 -/
theorem negative_sink_is_flatten_candidate {divSign : ℝ}
    (h : divSign < 0) :
    convergingFlowIsFlattenCandidate divSign := h

-- ---------------------------------------------------------------------------
-- CR8 ★ 抹平供能的框架内账本：收敛流自带「抹平功率」来源
--   HQ9a 已证：信息沉没进吸收态释放势能差 δ+ε > 0（开方不可逆的做功方向）。
--   把负电荷 = 汇 = iR 吸收态的语义接进 HQ9a：
--   负电荷向内收敛的空间流，其「沉没」动作释放 δ+ε 的势能差——
--   这笔能量**就是**维持抹平所需的功率（AMC4 的源维持成本）。
--   于是「谁给抹平供能」的答案：**收敛流自身的沉没释放**（HQ9a），
--   不是外部装置 —— 负电荷是自供能的反引力载体候选。
--
-- 诚实边界（解释层，写死）：
--   · HQ9a 是 Tag 流语言的定理；把它接到「空间流收敛」是语义对应，
--     不是空间流的动力学定理（两套语言：HiddenNum 标签 vs 连续场）。
--   · 「释放的能量 = 维持抹平的功率」是**账本形状的对应**（一个释放、
--     一个需要），没有证明两者数值相等（δ+ε vs AMC4 的 κQ²/2）。
--   · 第二输入缺口仍在：δ、ε 的数值（= 单个 Tag 的势能）无第一性来源。
--   · 无新可检验预言。 -/

/-- CR8：负电荷（汇）携带的势能差释放接口（HQ9a 的汇版本）。
    引用 HQ9a：开方流沉没进 iR 吸收态释放 φ(R)−φ(iR) = δ+ε > 0。
    定义把「负电荷汇的收敛沉没」写成 HQ9a 的实例（接口数据）。
    物理读法：向内汇聚的空间流沉没释放势能差，可作为抹平的供能候选。 -/
def sinkEnergyRelease (δ ε : ℝ) : ℝ :=
  HiddenQFT.tagPotential δ ε HiddenQFT.FlowTag.R - HiddenQFT.tagPotential δ ε HiddenQFT.FlowTag.iR

/-- CR8b：沉没释放恒为正——负电荷收敛沉没的释放量 δ+ε > 0（引用 HQ9a）。
    这是「抹平功率来源」的框架内正性断言：只要 δ、ε 为正，
    沉没动作就释放正能量。 -/
theorem sink_release_positive {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    0 < sinkEnergyRelease δ ε := by
  unfold sinkEnergyRelease
  rw [HiddenQFT.sqrt_potential_drop]
  linarith

-- ---------------------------------------------------------------------------
-- CR9 ★★ 离散格点上的严格定理：向心收缩（汇）以平方因子抹平起伏
--   把 CR7 的「收敛 = 抹平」从语义同位升级为**离散代数恒等式**。
--   定义向心收缩（负电荷吸流的离散模型）：
--     sinkContract A v λ := 区域 A 内每点向区域均值靠拢 λ 步
--     （λ=0 不动，λ=1 一步到均值 = flatten，λ∈(0,1) 部分收缩）
--   定理 CR9：Q_A(sinkContract A v λ) = (1−λ)² · Q_A(v)
--   物理读法：汇的每次「向内收缩」把起伏能量乘 (1−λ)²——
--   收敛流的抹平是**平方衰减**，不是线性；λ=1 时一步归零（=flatten）。
--   这是「为什么是负电荷」的严格代数内核：向心收缩（汇）就是抹平算子族。
--
-- 诚实边界（写死）：
--   · 这是离散格点定理（仓库风格：差分离散 = 连续偏导的代数种子）；
--     连续 3D 版的逐点对应未形式化（仓库明确未支持连续 ∇·）。
--   · 向心收缩是**模型选择**（把「负电荷吸流」翻译成收缩变换），
--     不是从 Maxwell 动力学推出的演化算子。
--   · λ 的物理来源（收缩步长 = 电荷强度？）未给出 —— 仍是第二输入缺口。
--   · 无新可检验预言。 -/

/-- 向心收缩：区域 A 内每点向区域均值靠拢 λ 步（λ=0 不动，λ=1 到均值）。
    这是「负电荷把周围空间流吸向自己」的离散模型。 -/
noncomputable def sinkContract {ι : Type} [DecidableEq ι] (A : Finset ι) (v : ι → ℝ) (lam : ℝ) : ι → ℝ :=
  fun i => if i ∈ A then (1 - lam) * v i + lam * regionMean A v else v i

/-- 收缩不改变区域均值：向心收缩保留 A 的总流率（与 flatten 守恒同调，
    GCA1b）。收缩 = 保守重排，不是注入/抽取流量。
    证明：A 内每点 v_i ↦ (1−λ)v_i + λ·v̄，A 内求和 = (1−λ)Σv + λ·card·v̄
    = (1−λ)S + λ·S = S（因 v̄ = S/card）。 -/
lemma sinkContract_mean_eq {ι : Type} [DecidableEq ι] (A : Finset ι) (v : ι → ℝ) (lam : ℝ) :
    regionMean A (sinkContract A v lam) = regionMean A v := by
  by_cases hA : A.card = 0
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp hA
    simp [regionMean, sinkContract, hA0]
  · have hA' : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA
    unfold sinkContract regionMean
    apply congrArg (fun x : ℝ => x / (A.card : ℝ))
    calc
      (A.sum (fun i => (if i ∈ A then (1 - lam) * v i + lam * (A.sum v / (A.card : ℝ)) else v i)))
          = (A.sum (fun i => ((1 - lam) * v i + lam * (A.sum v / (A.card : ℝ))))) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [hi]
      _ = (1 - lam) * A.sum v + (A.card : ℝ) * (lam * (A.sum v / (A.card : ℝ))) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ = A.sum v := by
              field_simp [hA']
              ring

/-- ★★ CR9：向心收缩以 (1−λ)² 的平方因子抹平起伏。
    Q_A(sinkContract v) = (1−λ)²·Q_A(v) —— 汇的收敛是**平方衰减**抹平；
    λ=1 一步归零（= flatten，GCA2c 的连续版）；λ∈(0,1) 指数收敛。
    这是「收敛 = 抹平」的离散代数内核。 -/
theorem sinkContract_fluctuation_scale
    {ι : Type} [DecidableEq ι] (A : Finset ι) (v : ι → ℝ) (lam : ℝ) :
    fluctuationEnergy A (sinkContract A v lam) = (1 - lam) ^ 2 * fluctuationEnergy A v := by
  unfold fluctuationEnergy
  have hmean : regionMean A (sinkContract A v lam) = regionMean A v :=
    sinkContract_mean_eq A v lam
  rw [hmean]
  calc
    A.sum (fun i => (sinkContract A v lam i - regionMean A v) ^ 2)
        = A.sum (fun i => ((1 - lam) * (v i - regionMean A v)) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [sinkContract, hi]
            ring
    _ = A.sum (fun i => (1 - lam) ^ 2 * (v i - regionMean A v) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (1 - lam) ^ 2 * A.sum (fun i => (v i - regionMean A v) ^ 2) := by
            rw [Finset.mul_sum]

-- ---------------------------------------------------------------------------
-- CR10 ★ 单点收缩（真正的一个「汇」）：整个区域向一个点收敛
--   之前的 sinkContract 是整个区域向均值收缩（= 向区域中心收缩）。
--   更贴「负电荷 = 汇」的版本：把区域 A 内的场全部拉向**一个指定点** p。
--   这是 CR9 的特例（均值收缩 → 点收缩），且比值当 A 只含 p 时退化。
--   这里形式化「汇的极限」：整个区域收缩到一个常值场（λ=1 时），
--   起伏归零（CR9 已证）；λ<1 时严格缩小（严格收缩，非平凡）。
--
-- 诚实边界：CR10 是 CR9 的简单重述 + 一个「严格收缩」引理；
--   物理新意为零（代数同构），只把「汇」的几何更明确化。 -/

/-- 收缩收缩性：0<λ<1 时向心收缩是**严格压缩**——每个 A 内点的值
    更靠近均值。|w_i − v̄| < |v_i − v̄|（除非已平）。这是「汇把周围
    流吸向自己」的逐点严格版。 -/
theorem sinkContract_strict_attracts
    {ι : Type} [DecidableEq ι] {A : Finset ι} {v : ι → ℝ} {lam : ℝ}
    {i : ι} (hi : i ∈ A) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hne : v i ≠ regionMean A v) :
    |sinkContract A v lam i - regionMean A v| < |v i - regionMean A v| := by
  have hmem : sinkContract A v lam i = (1 - lam) * v i + lam * regionMean A v := by
    simp [sinkContract, hi]
  rw [hmem]
  -- w_i − v̄ = (1−λ)(v_i − v̄)，0<1−λ<1 ⟹ 严格缩小
  have hdiff : (1 - lam) * v i + lam * regionMean A v - regionMean A v
      = (1 - lam) * (v i - regionMean A v) := by ring
  rw [hdiff]
  rw [abs_mul]
  have hf : |1 - lam| < 1 := by
    rw [abs_of_pos (sub_pos.mpr hlam1)]
    linarith
  have hpos : 0 < |v i - regionMean A v| := abs_pos.mpr (sub_ne_zero.mpr hne)
  exact mul_lt_of_lt_one_left hpos hf

end ProjectionPhysics.VibrationChargeRadiation