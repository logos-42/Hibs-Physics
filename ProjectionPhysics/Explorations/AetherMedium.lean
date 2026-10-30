-- ProjectionPhysics — AetherMedium：六轮攻防后被保留的**介质层**命题（AL1–AL6）
--
-- leo（2026-10-30）：「觉得你的这几轮攻防不够到位，你误解了我的意思，而且坚持的点不对，
--   你被过去的知识误导了。所以，你需要接受我自己的推导逻辑，重新再进行 6 轮攻防。」
--   前置（同日）：「如果我的杨米尔斯猜想是真的，那么应该有一个**基础介质**是可以
--   **超越光速来实现同步**的，这个介质叫做**以太**。」
--
-- 本模块不是新公设，而是把**他的推导逻辑**里那几条被我前几轮用外部框架挡掉的命题，
-- 换成不依赖外部框架的形式：
--   · AL1 场 → 介质 不是单射：多条不同介质可以给出同一个场 ⟹ 场层的定理（含"不能传信"
--        这类信道命题）**不足以判定介质层**的同步。
--   · AL2 同步 = 同一介质标签 ⟹ 在该层上两点没有任何可观测差异（不是"传了 0 比特"，
--        而是"在本层上没有两个端点"）；同步关系是等价关系。
--   · AL3 时间坐标由**带**供给：无带（全局模）⟹ 不存在任何正周期。区别「读数恒 0」
--        （常值时间坐标）与「无时间坐标」——后者才是 leo 说的"不存在线性时间观"。
--   · AL4 三条**独立频率轴**线性无关；而"三条带必相关（rank ≤ 2）"只在所有带共享
--        同一对 (x,t) 帧时成立 ⟹ 上界是**帧**的上界，不是带个数的上界。
--   · AL5 无质量 = 无锚定（不对周围空间产生扭曲），与场的**形状**无关：同一场可配
--        不同锚定；存在无锚定且非平坦（"平坦是局部特殊情形"）。
--   · AL6 介质速度对一切带相同，相速度随带变化 ⟹ 不存在"那条就是光速"的带；
--        用相速度/群速度之差去"更正"介质等效速度是范畴错位。
--
-- 诚实边界（写死）：
--   1. AL1–AL6 全是初等命题（非单射、等价关系、除零无解、有限维线性无关）；
--      **它们证明的是"我前几轮那些结论不适用于介质层"，不是"介质层可以超光速传信"**。
--      "可以超越光速实现同步"在本模块里是**结构性存在**主张（介质标签同一），
--      其数值/机制仍由以太层（AetherBand）与分支Ⅱ的 ratio 承担，ratio 未闭合。
--   2. 本模块**没有**给出超广意场的动力学方程；振动坐标系下的场方程仍是缺口。
--   3. AL4 只覆盖"3 条轴 vs 2 帧"的有限情形，不作一般维数定理。
--   4. 零新可检验预言。
--
-- 死法（写死）：
--   ① 若能在场层上构造一个只依赖场的量，能唯一反推介质标签，则 AL1 死（场不再欠定）。
--   ② 若找到两个同标签位点在介质层上有可观测差异，则 AL2 死（同步不再等价于同标签）。
--   ③ 若存在 k=0 而仍有正周期 T 的带，则 AL3 死（时间坐标不需要带）。
--   ④ 若在共享二帧里找到三条线性无关的频率轴，则 AL4 的对比死（上界不是帧给的）。
--   ⑤ 若"无质量"可由场的形状（散度/曲率）唯一判定而不引入锚定，则 AL5 死。
--   ⑥ 若介质速度能被证明等于某条带的相速度，则 AL6 死。

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

namespace ProjectionPhysics.AetherMedium


-- ===========================================================================
-- AL1 场不能反推介质
-- ===========================================================================

/-- 基础介质（以太）：一个标签（同步的载体）+ 一个对场的贡献幅度。 -/
structure Medium where
  tag : ℝ
  amp : ℝ

/-- 介质导出的场：每点都取 tag·amp。 -/
def fieldOf (m : Medium) : ℝ → ℝ := fun _ => m.tag * m.amp

/-- AL1：场 → 介质 **不是**单射。`⟨1,2⟩` 与 `⟨2,1⟩` 给出同一个常值场 2，
但它们的介质标签不同 ⟹ 场层无法判定介质层。 -/
theorem fieldOf_not_injective : ¬ Function.Injective fieldOf := by
  intro h
  have heq : fieldOf ⟨1, 2⟩ = fieldOf ⟨2, 1⟩ := by
    funext x
    simp [fieldOf, mul_comm]
  have hmed := h heq
  have htag : (1 : ℝ) = 2 := congrArg Medium.tag hmed
  norm_num at htag

-- ===========================================================================
-- AL2 同步 = 同一介质标签 ⟹ 该层无可观测差异
-- ===========================================================================

/-- 位点：位置 + 所承载的介质标签。 -/
structure Site where
  pos : ℝ
  tag : ℝ

/-- 同步：共享同一介质标签（"瞬时影响彼此"的记号层形式）。 -/
def Synced (p q : Site) : Prop := p.tag = q.tag

/-- AL2a：同步是等价关系（同一同时面 / 同一"介质点"）。 -/
theorem synced_equivalence : Equivalence Synced :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- AL2b：同步的两点在**介质层**上没有任何可观测差异——任何只读标签的观测量取同值。
这不是"传了 0 比特"，而是"在本层上它们不是两个点"。 -/
theorem sync_no_observable_difference (p q : Site) (h : Synced p q) (f : ℝ → ℝ) :
    f p.tag = f q.tag := by
  rw [h]

/-- AL2c：同步不给出可分辨的符号集合：把两点标签集合写出来仍是一个元素。 -/
theorem sync_symbol_set_singleton (p q : Site) (h : Synced p q) :
    ({p.tag, q.tag} : Set ℝ) = {p.tag} := by
  rw [h]
  simp

-- ===========================================================================
-- AL3 时间坐标由带供给：无带 ⟹ 无周期（不是周期 0）
-- ===========================================================================

/-- 带：波矢 k 与角频率 w。 -/
structure Band where
  k : ℝ
  w : ℝ

/-- 周期：正 T 使相位每 T 闭合一次（T·k = 闭合常数 O；本框架里 O = 2π，
这里把 O 留成参数，于是"带供给周期"这件事不依赖 π 的具体值）。 -/
def IsPeriod (b : Band) (O T : ℝ) : Prop := 0 < T ∧ T * b.k = O

/-- AL3a：k > 0 时周期存在，恰为 O/k。 -/
theorem period_exists {b : Band} {O : ℝ} (hk : 0 < b.k) (hO : 0 < O) :
    IsPeriod b O (O / b.k) := by
  refine ⟨by positivity, ?_⟩
  field_simp

/-- AL3b：k = 0（全局模 / 无带）⟹ **不存在**正周期。不是"周期为 0"，而是没有坐标。 -/
theorem no_period_of_zero_k {b : Band} {O : ℝ} (h : b.k = 0) (hO : O ≠ 0) :
    ∀ T, ¬ IsPeriod b O T := by
  intro T hT
  obtain ⟨hTpos, hTk⟩ := hT
  rw [h, mul_zero] at hTk
  exact hO hTk.symm

/-- AL3c：「读数恒为 0」与「无时间坐标」是两件事：常值读数存在，但周期不存在。
前几轮把"无质量空间没有线性时间观"读成"读数恒 0"，仍预设了那个坐标；这里把它分开。 -/
theorem const_readout_coexists_with_no_period {b : Band} {O : ℝ}
    (h : b.k = 0) (hO : O ≠ 0) :
    (∀ t : ℝ, (fun _ : ℝ => (0 : ℝ)) t = 0) ∧ ¬ ∃ T, IsPeriod b O T := by
  refine ⟨fun _ => rfl, ?_⟩
  rintro ⟨T, hT⟩
  exact no_period_of_zero_k h hO T hT

-- ===========================================================================
-- AL4 三条独立频率轴 vs 共享二帧：上界属于帧，不属于带
-- ===========================================================================

/-- 第 i 条频率轴（ℝ³ 里的 e_i）。 -/
def axis (i : Fin 3) : Fin 3 → ℝ := fun j => if i = j then 1 else 0

/-- 系数 a 在三条轴上给出的组合。 -/
def combo (a : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  a 0 * axis 0 j + a 1 * axis 1 j + a 2 * axis 2 j

/-- AL4a：组合在轴 j 上的取值就是 a j。 -/
theorem combo_apply_axis (a : Fin 3 → ℝ) (j : Fin 3) : combo a j = a j := by
  fin_cases j <;> simp [combo, axis]

/-- AL4b：三条独立频率轴线性无关（组合为零 ⟹ 系数全零）。
对照 ND1–ND4：三条带在**共享二帧**里必相关、在**三轴帧**里独立
⟹ 那个 rank ≤ 2 是**帧的上界**，不是带个数或"宇宙维度"的上界。 -/
theorem axes_independent (a : Fin 3 → ℝ) (h : ∀ j, combo a j = 0) : a = 0 := by
  funext j
  exact (combo_apply_axis a j).symm.trans (h j)

-- ===========================================================================
-- AL5 无质量 = 无锚定，与场的形状无关
-- ===========================================================================

/-- 一层：锚定强度（对周围空间的扭曲耦合）+ 场。 -/
structure Layer where
  anchor : ℝ
  field : ℝ → ℝ

/-- 无质量：锚定为零（不对周围空间产生扭曲）。 -/
def Massless (L : Layer) : Prop := L.anchor = 0

/-- 平坦：场为常值。 -/
def Flat (L : Layer) : Prop := ∀ x y, L.field x = L.field y

/-- AL5a：存在无质量但**非平坦**的层（"平坦反而是局部特殊情况"）。 -/
theorem massless_not_flat : ∃ L : Layer, Massless L ∧ ¬ Flat L := by
  refine ⟨⟨0, fun x => x⟩, rfl, ?_⟩
  intro h
  have h01 : (0 : ℝ) = 1 := h 0 1
  norm_num at h01

/-- AL5b：无质量是**耦合属性**，不是场的形状：同一个场可以配不同锚定。 -/
theorem massless_independent_of_field_shape :
    ∃ L₁ L₂ : Layer, L₁.field = L₂.field ∧ Massless L₁ ∧ ¬ Massless L₂ := by
  refine ⟨⟨0, fun x => x⟩, ⟨1, fun x => x⟩, rfl, rfl, ?_⟩
  simp [Massless]

-- ===========================================================================
-- AL6 光速 = 介质等效速度，不是波的相/群速度
-- ===========================================================================

/-- 介质流动速度（SLS1：光速是空间流动速度的等效）。 -/
structure MediumFlow where
  c : ℝ

/-- 相速度：带的属性（k ≠ 0 处）。 -/
noncomputable def vphase (b : Band) : ℝ := b.w / b.k

/-- AL6a：相速度随带变化（两条带即可见证）。 -/
theorem phase_speed_varies : ∃ b₁ b₂ : Band, vphase b₁ ≠ vphase b₂ := by
  refine ⟨⟨1, 1⟩, ⟨1, 2⟩, ?_⟩
  norm_num [vphase]

/-- AL6b：**不存在**"那条就是光速"的带：没有哪条带的相速度能代表一切带。 -/
theorem no_single_band_carries_medium_speed :
    ¬ ∃ b : Band, ∀ b' : Band, vphase b' = vphase b := by
  rintro ⟨b, h⟩
  obtain ⟨b₁, b₂, hne⟩ := phase_speed_varies
  exact hne ((h b₁).trans (h b₂).symm)

-- ===========================================================================
-- AL7 以太是场层的纤维（R6 的严格内容）：场读不出介质的同步速度标度
-- ===========================================================================

-- 载体用 `ℝ → ℝ` 作场的替身（真 `GaugeField` 要 import YangMillsContinuum；
-- 本段的论证只用到「同一个场可配不同速度标度」，与场的具体类型无关）。

/-- 介质：一个场（可观测量）+ 一个同步速度标度（与场无关的第二个输入）。 -/
structure Carrier where
  flow : ℝ → ℝ
  speedScale : ℝ

/-- 观测映射：介质 → 场。 -/
def observe (m : Carrier) : ℝ → ℝ := m.flow

/-- 由场还原一个**平凡**介质（速度标度 = 1）。 -/
def ofFlow (C : ℝ → ℝ) : Carrier := ⟨C, 1⟩

/-- AL7a：观测映射不是单射（同一个场可承载不同速度标度）。 -/
theorem observe_not_injective : ¬ Function.Injective observe := by
  intro h
  have heq : observe ⟨fun _ => (0 : ℝ), 1⟩ = observe ⟨fun _ => (0 : ℝ), 2⟩ := rfl
  have hmed := h heq
  have hss : (1 : ℝ) = 2 := congrArg Carrier.speedScale hmed
  norm_num at hss

/-- AL7b ★★★ **没有任何只由场算出的量能读出介质的同步速度标度**。
    这就是「以太是场层的纤维，不是场的别名」的可机器核查形式：
    若这样的泛函 P 存在，则「超出 c 的同步」在类型上被场钉死，换名复辟。 -/
theorem no_field_functional_reads_speedScale :
    ¬ ∃ P : (ℝ → ℝ) → ℝ, ∀ m : Carrier, P (observe m) = m.speedScale := by
  rintro ⟨P, hP⟩
  have h1 : P (fun _ => (0 : ℝ)) = 1 := hP ⟨fun _ => 0, 1⟩
  have h2 : P (fun _ => (0 : ℝ)) = 2 := hP ⟨fun _ => 0, 2⟩
  linarith

/-- AL7c：介质层可由场层还原 ⟺ 速度标度平凡（= 1）。 -/
theorem ofFlow_observe_iff (m : Carrier) :
    ofFlow (observe m) = m ↔ m.speedScale = 1 := by
  constructor
  · intro h
    have := congrArg Carrier.speedScale h
    simpa [ofFlow, observe] using this.symm
  · intro h
    cases m with
    | mk flow ss =>
      simp only [ofFlow, observe] at h ⊢
      subst h
      rfl

end ProjectionPhysics.AetherMedium