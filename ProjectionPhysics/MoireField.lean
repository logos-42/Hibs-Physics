-- ProjectionPhysics — MoireField：魔角石墨烯场源的场天花板账本（代数骨架）
--
-- leo（2026-09-23）问题：魔角石墨烯（1° 夹角）方案若用来产生磁场、再由磁场
--   引发引力场约束实现可控核聚变，数据如何变化？
--
-- 本轮不做新物理，只做一件事：把仓库已证条目里的**场源**换成一个"有材料
-- 天花板 B ≤ B_c2"的场源（魔角石墨烯 N=2 的 B_c2⊥ ≈ 0.12 T、面内 ≈ 1.6 T），
-- 看去掉的那个自由度把数字压到哪：
--
--   FC1（FrcCompact）      n_max = βB²/(4μ₀kT)        —— 场决定密度
--   PF3（PlasmaFusion）    B² ≥ 2μ₀nkT                —— 密度决定最小场
--   二轮修正链            τ_E = τ₀/√(1−μ)，τ₀ = a²/D₀ —— μ 决定约束时间
--   劳森                 n·τ ≥ A（A = 2e20 @15keV）
--   FC11b（FrcCompact）    μ < 1 − m_e/m_i ⟺ 1−μ > m_e/m_i —— μ 的硬天花板
--
-- 核心定理（mathlib，代数种子）：
--   MFC1. 场天花板 ⟹ 密度天花板（FC1 对 B 单调）
--   MFC2. 密度下降 ⟹ 所需 (1−μ) 上限下降（τ_req ↑ ⟹ X_req ↓）
--   MFC3. X_req = (τ₀/A)²·n²（四次方标度的来源：n ∝ B² ⟹ X ∝ B⁴）
--   MFC4★ 死证：X_req ≤ m_e/m_i ⟹ **不存在**可行 μ（不是"更难"，是无解）
--   MFC5★ 组合：低场 → 无解（本轮生死门）
--   MFC6. 装置越小要求的场越高（阈值 ∝ 1/a² ⟹ B_death ∝ 1/a）——小装置更依赖场
--   MFC7. 功率比 = 场比⁴（P ∝ n² ∝ B⁴）——装置尺寸/功率的数据变化律
--
-- 诚实边界：全是代数单调性 + 一次否定存在性证明（真但平凡）；μ 的主动产生
--   机制 = 第二输入缺口（未变）；材料 B_c2/n_s 是外部实验上层限（数值层输入）；
--   载流（安匝）与制冷（mW vs kW）两门是数值层量级账，未在此形式化；
--   无新物理预言（4 层判定：数学恒等 + 工程映射）。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import ProjectionPhysics.FrcCompact

noncomputable section
namespace MoireField

open FrcCompact

/-! ### ① 场天花板 ⟹ 密度天花板 -/

/-- MFC1：FRC β≈1 平衡密度对场强单调——**场源天花板就是密度天花板**。
    这是"材料 B_c2 上限"进入整套聚变数字链的唯一入口：FC1 一旦被截，
    后面 n、P、τ_Lawson、(1−μ) 全部随之被截。 -/
theorem density_mono_field (β μ₀ k T B₁ B₂ : ℝ) (hβ : 0 < β) (hμ : 0 < μ₀)
    (hk : 0 < k) (hT : 0 < T) (hB₁ : 0 ≤ B₁) (hB : B₁ ≤ B₂) :
    frcDensity β B₁ μ₀ k T ≤ frcDensity β B₂ μ₀ k T := by
  unfold frcDensity
  have hsq : B₁ * B₁ ≤ B₂ * B₂ := mul_self_le_mul_self hB₁ hB
  have hnum : β * (B₁ * B₁) ≤ β * (B₂ * B₂) :=
    mul_le_mul_of_nonneg_left hsq (le_of_lt hβ)
  have hden : 0 < 4 * μ₀ * k * T := by positivity
  rw [div_le_div_iff₀ hden hden]
  nlinarith [hnum]

/-- MFC1b：密度上限的具体形式——n_max(B) = βB²/(4μ₀kT) 与 B² 同阶（四次方律的一半）。 -/
theorem density_sq_form (β μ₀ k T B : ℝ) :
    frcDensity β B μ₀ k T = β / (4 * μ₀ * k * T) * B ^ 2 := by
  unfold frcDensity
  field_simp

/-! ### ② 所需 (1−μ) 与密度的关系 -/

/-- 输入：所需 (1−μ) 的上限。劳森要求 τ_E ≥ n·τ 常数/密度，而
    τ_E = τ₀/√(1−μ) ⟹ √(1−μ) ≤ τ₀/τ_L ⟹ 1−μ ≤ (τ₀/τ_L)² = (τ₀·n/A)²。
    记为 X_req（X 越小 = 要求 μ 越靠近 1 = 越难）。 -/
def xReq (τ₀ A n : ℝ) : ℝ := (τ₀ * n / A) ^ 2

/-- 输入：装置尺度给出的弛豫时间基准 τ₀ = a²/D₀（a = 装置尺寸，D₀ = 扩散系数）。 -/
def tau0 (a D₀ : ℝ) : ℝ := a ^ 2 / D₀

/-- MFC3：X_req = (τ₀/A)²·n² —— 四次方标度的代数内核：
    n ∝ B²（MFC1b）⟹ X_req ∝ n² ∝ B⁴。 -/
theorem xReq_sq_form (τ₀ A n : ℝ) (hA : A ≠ 0) :
    xReq τ₀ A n = (τ₀ / A) ^ 2 * n ^ 2 := by
  unfold xReq
  field_simp

/-- MFC2：密度下降 ⟹ 所需 (1−μ) 上限下降（μ 要求变严）——**反直觉方向**：
    场越弱，密度越低，劳森要求的约束时间越长，反而要求 μ 更接近 1。 -/
theorem xReq_mono_density (c n₁ n₂ : ℝ) (hc : 0 < c) (hn₁ : 0 ≤ n₁) (hn : n₁ ≤ n₂) :
    (c * n₁) ^ 2 ≤ (c * n₂) ^ 2 := by
  have hdiff : 0 ≤ c * n₂ - c * n₁ := by nlinarith
  have hsum : 0 ≤ c * n₁ + c * n₂ := by nlinarith
  have hprod : 0 ≤ (c * n₂ - c * n₁) * (c * n₁ + c * n₂) := mul_nonneg hdiff hsum
  nlinarith [hprod]

/-- MFC2b：随密度单调（包装成 xReq 形式，供 MFC5 组合）。 -/
theorem xReq_mono (τ₀ A n₁ n₂ : ℝ) (hτ₀ : 0 ≤ τ₀) (hA : 0 < A) (hn₁ : 0 ≤ n₁)
    (hn : n₁ ≤ n₂) : xReq τ₀ A n₁ ≤ xReq τ₀ A n₂ := by
  unfold xReq
  have hnum : τ₀ * n₁ ≤ τ₀ * n₂ := mul_le_mul_of_nonneg_left hn hτ₀
  have hle : τ₀ * n₁ / A ≤ τ₀ * n₂ / A := by
    rw [div_le_div_iff₀ hA hA]
    nlinarith [hnum]
  have h1 : 0 ≤ τ₀ * n₁ / A := div_nonneg (mul_nonneg hτ₀ hn₁) (le_of_lt hA)
  have h2 : 0 ≤ τ₀ * n₂ / A :=
    div_nonneg (mul_nonneg hτ₀ (le_trans hn₁ hn)) (le_of_lt hA)
  have hprod : 0 ≤ (τ₀ * n₂ / A - τ₀ * n₁ / A) * (τ₀ * n₂ / A + τ₀ * n₁ / A) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_nonneg h2 h1)
  nlinarith [hprod]

/-! ### ③ FC11 窗口与死证 -/

/-- 输入：可接受的 μ。FC11b 已证 RMF 窗口 ⟺ μ < 1 − m_e/m_i，即
    0 < 1−μ ∧ m_e/m_i < 1−μ ∧ 1−μ < 1（μ ∈ (0,1)）。 -/
def muWindowOpen (μ m_e m_i : ℝ) : Prop :=
  0 < 1 - μ ∧ m_e / m_i < 1 - μ ∧ 1 - μ < 1

/-- **MFC4★ 死证**：若所需的 (1−μ) 上限已经**小于** FC11 地板 m_e/m_i，
    则不存在任何可行 μ——需求与窗口不相交。
    注意这不是"μ 更难做到"，而是**可行集为空**：场天花板把问题从
    工程难度问题变成不可满足的代数条件。 -/
theorem no_admissible_mu_of_low_requirement (X m_e m_i : ℝ) (hdead : X ≤ m_e / m_i) :
    ¬ ∃ μ : ℝ, muWindowOpen μ m_e m_i ∧ 1 - μ ≤ X := by
  rintro ⟨μ, ⟨_, hfloor, _⟩, hle⟩
  linarith

/-- **MFC5★ 组合定理**：场源天花板使密度落到 X_req ≤ m_e/m_i 的区间 ⟹ 无解。
    链条：B ≤ B_cap --MFC1--> n ≤ n(B_cap) --MFC2--> X_req ≤ X_req(B_cap)
    --假设--> ≤ m_e/m_i --MFC4--> ∄μ。 -/
theorem field_ceiling_no_solution (τ₀ A n me mi : ℝ) (hdead : xReq τ₀ A n ≤ me / mi) :
    ¬ ∃ μ : ℝ, muWindowOpen μ me mi ∧ 1 - μ ≤ xReq τ₀ A n :=
  no_admissible_mu_of_low_requirement _ _ _ hdead

/-- MFC5b：设计密度分支的可行性判据——存在可行 μ ⟺ X_req > m_e/m_i
    （窗口下界严格低于需求上限）。 -/
theorem feasible_iff_above_floor (X me mi : ℝ) (hfloor : 0 < me / mi)
    (hX : me / mi < X) (hX1 : X < 1) :
    ∃ μ : ℝ, muWindowOpen μ me mi ∧ 1 - μ ≤ X := by
  refine ⟨1 - X, ⟨by linarith, by linarith, by linarith⟩, by linarith⟩

/-! ### ④ 装置尺度与场阈值的反比 -/

/-- MFC6a：τ₀ ∝ a² 单调——装置越大，基准约束时间越长。 -/
theorem tau0_mono (D₀ a₁ a₂ : ℝ) (hD : 0 < D₀) (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) :
    tau0 a₁ D₀ ≤ tau0 a₂ D₀ := by
  unfold tau0
  have hsq : a₁ * a₁ ≤ a₂ * a₂ := mul_self_le_mul_self (le_of_lt ha₁) ha
  have hden : 0 < D₀ := hD
  rw [div_le_div_iff₀ hden hden]
  nlinarith [hsq]

/-- **MFC6★**：阈值密度 ∝ 1/τ₀ ∝ 1/a²——**装置越小，要求的场天花板越高**。
    数值：B_death(0.2m) ≈ 1.0 T、B_death(0.1m) ≈ 2.0 T、B_death(0.05m) ≈ 4.0 T。
    含义：紧凑化路线（leo 关注的 10cm 级）把场门槛抬到魔角石墨烯面内 B_c
    （1.6 T）之上——材质的场天花板与装置的尺寸要求方向冲突。 -/
theorem threshold_inverse_size (A D₀ a₁ a₂ s : ℝ) (hA : 0 < A) (hD : 0 < D₀)
    (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) (hs : 0 ≤ s) :
    (A / tau0 a₂ D₀) * s ≤ (A / tau0 a₁ D₀) * s := by
  have ht : tau0 a₁ D₀ ≤ tau0 a₂ D₀ := tau0_mono D₀ a₁ a₂ hD ha₁ ha
  have ht1 : 0 < tau0 a₁ D₀ := by
    unfold tau0
    positivity
  have hdiv : A / tau0 a₂ D₀ ≤ A / tau0 a₁ D₀ :=
    div_le_div_of_nonneg_left (le_of_lt hA) ht1 ht
  exact mul_le_mul_of_nonneg_right hdiv hs

/-! ### ⑤ 功率/体积的数据变化律 -/

/-- MFC7：功率比 = 场比⁴——P ∝ n²⟨σv⟩ 与 n ∝ B²（MFC1b）合成：
    场天花板降到 1/k ⟹ 功率密度降到 1/k⁴ ⟹ 同功率体积涨 k⁴ 倍。 -/
theorem power_ratio_is_field_ratio_pow4 (c B₁ B₂ : ℝ) (hc : c ≠ 0) (hB₁ : B₁ ≠ 0) :
    (c * B₂ ^ 2) ^ 2 / (c * B₁ ^ 2) ^ 2 = (B₂ / B₁) ^ 4 := by
  field_simp

/-- MFC7b：体积标度的同一件事——同功率体积 ∝ B⁻⁴（此处给出比值形式）。 -/
theorem volume_ratio_is_inverse_pow4 (c B₁ B₂ : ℝ) (hc : c ≠ 0) (hB₁ : B₁ ≠ 0) :
    (c * B₁ ^ 2) ^ 2 / (c * B₂ ^ 2) ^ 2 = (B₁ / B₂) ^ 4 := by
  field_simp

/-- 模块范围声明（供 verify_all / wiki 引用）。 -/
def MOIRE_FIELD_SCOPE : String :=
  "魔角石墨烯场源账本代数骨架: MFC1 场天花板⟹密度天花板(FC1 对 B 单调) " ++
  "+ MFC2 密度↓⟹所需(1−μ)上限↓(劳森 τ 变长, μ 要求变严) " ++
  "+ MFC3 X_req=(τ₀/A)²n² (n∝B²⟹X∝B⁴) " ++
  "+ MFC4★ 死证 X_req≤m_e/m_i⟹∄可行 μ(FC11b 窗口空) " ++
  "+ MFC5★ 组合 低场⟹无解 + MFC5b 可行⟺X_req>m_e/m_i " ++
  "+ MFC6★ 阈值 ∝1/a² (B_death∝1/a: 小装置要求更高场) " ++
  "+ MFC7 功率比=场比⁴(P∝B⁴) / 体积比=场比⁻⁴; 数值层输入: 材料 B_c2(0.12/1.6/10 T), " ++
  "n_s(REBCO 片超流密度 vs 二维), 制冷容量; 开放缺口: μ 主动产生=第二输入缺口(未变), " ++
  "载流/制冷两门未形式化; 无新物理预言"

end MoireField
