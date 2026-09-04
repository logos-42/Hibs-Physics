-- ProjectionPhysics — FrcCompact：FRC（场反位形）迭代版紧凑装置的代数骨架
--
-- leo（2026-09-02）问题：这套理论能不能缩到半径 10cm 以内？
--   允许把本理论当作 **FRC 的迭代版本**，用已有 FRC 技术（尤其"变化的电磁场"
--   = 旋转磁场 RMF 驱动电流）作为现实锚点，重新做数据验证。
--
-- 与既有主线的精确接轨：
--   · PlasmaFusion PF1–PF3：磁压平衡 / β ≤ 1 / 场强反推（本模块走 β≈1 的 FRC 分支）
--   · PlasmaFusion PF7：hoop 应力 ⟹ 半径上限（本模块反解成 **场强上限**）
--   · PlasmaDynamics TM：m_eff = s(1−μ) ⟹ D ∝ √m_eff ⟹ τ_E ∝ 1/√(1−μ)
--   · PlasmaFusion PF9：时变场调制 ⟹ 控制力（本模块对应 RMF 驱动窗口）
--
-- ★ 本轮的核心新结果（上一轮 μ≥0.9997 的"输运解锁"结论缺了稳定性这一侧）：
--   在 FRC（β≈1）平衡下，**S*（s 参数/动力学参数）与 τ_E 对质量标度的响应完全相同**：
--       S*(μ)/S*(0) = τ_E(μ)/τ_E(0) = 1/√(1−μ)
--   二者比值与 B、m_eff 都无关（FC5 锁定定理）。即：
--   **不可能只改善约束时间而不等比例抬高 s 参数**——μ 把输运问题换成了
--   （更大、更不被理解的）动力学稳定性问题。
--   同时 τ_A ∝ √m_eff（FC6）：μ↑ ⟹ Alfvén 时间变短 ⟹ 不稳定性长得更快。
--
-- 核心定理（mathlib，代数种子）：
--   FC1.  FRC β 压强平衡：4μ₀kT·n = βB²；n·T 与 T 无关，只由 β、B 决定
--   FC2★. S*²·ρ_i² = β·r_s²/2（s 参数与回旋半径严格锁定）
--   FC3★. S*²·m = C²（质量越小 s 参数越大）
--   FC4★. τ_E²·m = C²（质量越小约束越久，repo TM 链）
--   FC5★★. 锁定定理：S*/τ_E 与 m、B 都无关（μ 的两面性）
--   FC6★. τ_A² 在 β=1 下与 B 无关、∝ m（μ↑ ⟹ 不稳定性加速）
--   FC7★. N_A² = τ_E²/τ_A² ∝ B²/m²，m↓ ⟹ 可增长代数发散
--   FC8★. 机械门：σ_hoop ≤ σ_y ⟹ B² ≤ 2μ₀σ_y t/R_c（PF7 反解）
--   FC9★. RMF 窗口：ω_ci ∝ 1/m_eff，μ↑ ⟹ 驱动频率必须更高
--   FC10★. Θ ≡ B²/m_eff 是唯一不变量；固定 S* 预算 ⟹ 增益 ∝ m_eff
--
-- 诚实边界：代数骨架（标度/锁定/不等式），不是 Grad-Shafranov 平衡或
--   Hall-MHD 稳定性分析；Bohm 系数 f_B、S* 稳定边界是数值层输入（经验值）；
--   μ 的主动产生机制 = 第二输入缺口（未变）；μ 对核反应率 ⟨σv⟩ 的影响
--   （v_th ∝ 1/√m_eff ⟹ 反应率可能变）**未建模**，是新增的开放缺口；
--   无新物理预言（4 层判定：数学恒等 + FRC 工程映射）。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import ProjectionPhysics.PlasmaFusion

noncomputable section
namespace FrcCompact

/-! ### ① FRC β≈1 平衡：n·T 只由 B 决定 -/

/-- FC1 输入：FRC 压强平衡下的密度。FRC 是 **高 β（≈1）** 位形，
    压强平衡写成 2 n k T = β B²/(2μ₀)，解出 n = βB²/(4μ₀kT)。
    对比托卡马克 β≈2%：同一 B 下 FRC 的 nT 高 1/β_tok 倍（≈50×）。
    这就是"FRC 是紧凑装置的天然载体"的定量来源。 -/
def frcDensity (β B μ₀ k T : ℝ) : ℝ := β * B * B / (4 * μ₀ * k * T)

/-- FC1：FRC 密度定义的自洽式——4μ₀kT·n = βB²（压强平衡的代数形式）。 -/
theorem frc_density_balance (β B μ₀ k T : ℝ) (hμ : μ₀ ≠ 0) (hk : k ≠ 0) (hT : T ≠ 0) :
    4 * μ₀ * k * T * frcDensity β B μ₀ k T = β * B * B := by
  unfold frcDensity
  field_simp [hμ, hk, hT]

/-- FC1b 输入：FRC 的 n·T 乘积（只由 β 与 B 决定）。 -/
def ntProduct (β B μ₀ k : ℝ) : ℝ := β * B * B / (4 * μ₀ * k)

/-- FC1b★：n·T 与温度无关——FRC 的密度完全由磁场"定价"，
    温度降一档密度就涨一档。这是 FRC 与托卡马克最本质的工程差别。 -/
theorem nt_independent_of_T (β B μ₀ k T : ℝ) (hμ : μ₀ ≠ 0) (hk : k ≠ 0) (hT : T ≠ 0) :
    frcDensity β B μ₀ k T * T = ntProduct β B μ₀ k := by
  unfold frcDensity ntProduct
  field_simp [hμ, hk, hT]

/-- FC1c：n·T 随场强平方增长（β=1 路线的全部收益都在 B² 上）。 -/
theorem nt_mono_field (β μ₀ k : ℝ) (hβ : 0 < β) (hμ : 0 < μ₀) (hk : 0 < k)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (h : B₁ < B₂) :
    ntProduct β B₁ μ₀ k < ntProduct β B₂ μ₀ k := by
  unfold ntProduct
  have hsq : B₁ * B₁ < B₂ * B₂ := by nlinarith
  have hC : 0 < β / (4 * μ₀ * k) := by positivity
  have h₁ : β * B₁ * B₁ / (4 * μ₀ * k) = (β / (4 * μ₀ * k)) * (B₁ * B₁) := by ring
  have h₂ : β * B₂ * B₂ / (4 * μ₀ * k) = (β / (4 * μ₀ * k)) * (B₂ * B₂) := by ring
  rw [h₁, h₂]
  exact mul_lt_mul_of_pos_left hsq hC

/-! ### ② S*（s 参数）与回旋半径的锁定 -/

/-- FC2 输入：s 参数（动力学参数）的平方——S* ≡ r_s/d_i，
    d_i = c/ω_pi = √(m_i/(μ₀ n e²))，故 S*² = r_s² μ₀ n e²/m_i。 -/
def sParamSq (r_s μ₀ n e m_i : ℝ) : ℝ := r_s * r_s * μ₀ * n * e * e / m_i

/-- FC2 输入：离子回旋半径平方——ρ_i = √(2 m_i kT)/(eB)。 -/
def gyroSq (m_i kT e B : ℝ) : ℝ := 2 * m_i * kT / (e * e * B * B)

/-- FC2★★：FRC 压强平衡下 **S*²·ρ_i² = β·r_s²/2**，即
        S* = √β · r_s / (√2 ρ_i)
    s 参数与回旋半径严格锁定：**任何把 ρ_i 缩小的手段都会等比例抬高 S***。
    这是本轮最关键的恒等式——它把"质量取消改善输运"和"s 参数恶化"
    焊成了同一件事的两面（见 FC5）。 -/
theorem sstar_gyro_lock (β B μ₀ k T e m_i r_s : ℝ)
    (hμ : μ₀ ≠ 0) (hk : k ≠ 0) (hT : T ≠ 0) (hm : m_i ≠ 0)
    (he : e ≠ 0) (hB : B ≠ 0) :
    sParamSq r_s μ₀ (frcDensity β B μ₀ k T) e m_i * gyroSq m_i (k * T) e B =
      β * r_s * r_s / 2 := by
  unfold sParamSq gyroSq frcDensity
  field_simp [hμ, hk, hT, hm, he, hB]
  ring

/-! ### ③ 质量标度：S* 与 τ_E 同向、τ_A 反向 -/

/-- FC3 输入：∝ 1/√m 的量（S* 与 τ_E 都属此类）。 -/
def invSqrtMass (C m : ℝ) : ℝ := C / Real.sqrt m

/-- FC3★：S*²·m = C² —— 质量越小，s 参数越大（因为 d_i ∝ √m）。 -/
theorem sstar_sq_mul_mass (C m : ℝ) (hm : 0 < m) : (C / Real.sqrt m) ^ 2 * m = C ^ 2 := by
  have hs : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt (le_of_lt hm)
  have hsn : Real.sqrt m ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  field_simp [hsn]
  rw [hs]

/-- FC4★：τ_E²·m = C² —— 质量越小约束越久。
    来源（repo TM 链）：m_eff = s(1−μ) ⟹ ρ_i ∝ √m_eff ⟹ ν ∝ 1/√m_eff
    ⟹ D ∝ ρ²ν ∝ √m_eff ⟹ τ_E = r_s²/(4D) ∝ 1/√m_eff。 -/
theorem tau_sq_mul_mass (C m : ℝ) (hm : 0 < m) : (C / Real.sqrt m) ^ 2 * m = C ^ 2 := by
  exact sstar_sq_mul_mass C m hm

/-- FC5★★★：**锁定定理**——S* 与 τ_E 对质量标度的响应完全相同，
    比值 S*/τ_E 与 m、B 都无关。
    物理后果（本轮最重要的结论）：
    **不可能只改善约束时间而不等比例抬高 s 参数。**
    上一轮"μ≥0.9997 ⟹ τ_E×58 ⟹ 劳森闭合"只算了输运一侧；
    FRC 的动力学稳定性（S*/E ≲ 3–4 的经验边界）会在同一因子上恶化。 -/
theorem sstar_tau_locked (A C m₁ m₂ : ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hA : A ≠ 0) (hC : C ≠ 0) :
    (A / Real.sqrt m₁) / (C / Real.sqrt m₁) = (A / Real.sqrt m₂) / (C / Real.sqrt m₂) := by
  have hs₁ : Real.sqrt m₁ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm₁)
  have hs₂ : Real.sqrt m₂ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm₂)
  field_simp [hs₁, hs₂, hA, hC]

/-- FC5b★：μ 标度显式形式——S*(μ)/S*(0) = 1/√(1−μ)（m_eff = m(1−μ)）。 -/
theorem mu_scaling_sstar (C m μ : ℝ) (hm : 0 < m) (hμ : 0 < 1 - μ) (hC : C ≠ 0) :
    (C / Real.sqrt (m * (1 - μ))) / (C / Real.sqrt m) = 1 / Real.sqrt (1 - μ) := by
  rw [Real.sqrt_mul (le_of_lt hm)]
  have hsm : Real.sqrt m ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  have hsu : Real.sqrt (1 - μ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hμ)
  field_simp [hsm, hsu, hC]

/-- FC5c★：τ_E(μ)/τ_E(0) = 1/√(1−μ) —— 与 FC5b **同一因子**，
    两者的比值恒为 1（由 FC5 保证）。这一对并列陈述就是"μ 的两面性"。 -/
theorem mu_scaling_tau (C m μ : ℝ) (hm : 0 < m) (hμ : 0 < 1 - μ) (hC : C ≠ 0) :
    (C / Real.sqrt (m * (1 - μ))) / (C / Real.sqrt m) = 1 / Real.sqrt (1 - μ) := by
  exact mu_scaling_sstar C m μ hm hμ hC

/-! ### ④ Alfvén 时间：μ 让不稳定性长得更快 -/

/-- FC6 输入：Alfvén 时间平方（原始形式）τ_A = r_s√(μ₀ n m)/B。 -/
def alfvenSqRaw (μ₀ n m r_s B : ℝ) : ℝ := μ₀ * n * m * r_s * r_s / (B * B)

/-- FC6 输入：代入 FRC β 平衡后的 Alfvén 时间平方——**与 B 无关**。 -/
def alfvenSq (β m r_s kT : ℝ) : ℝ := β * m * r_s * r_s / (4 * kT)

/-- FC6★：β 平衡下 τ_A² = β·m·r_s²/(4kT)——**与磁场无关，只 ∝ m**。
    物理后果：μ↑ ⟹ m_eff↓ ⟹ τ_A↓ ⟹ 倾斜模/n=1 模在更短时间内长起来。
    想靠提高 B 来"压住"不稳定性在 FRC 里是无效的（B 被 β=1 抵消了）。 -/
theorem alfven_sq_independent_of_B (β B μ₀ k T m r_s : ℝ)
    (hμ : μ₀ ≠ 0) (hk : k ≠ 0) (hT : T ≠ 0) (hB : B ≠ 0) :
    alfvenSqRaw μ₀ (frcDensity β B μ₀ k T) m r_s B = alfvenSq β m r_s (k * T) := by
  unfold alfvenSqRaw alfvenSq frcDensity
  field_simp [hμ, hk, hT, hB]

/-- FC7 输入：一个约束时间内可供不稳定性增长的（Alfvén）代数平方。
    N_A = τ_E/τ_A，τ_E ∝ B/√m、τ_A ∝ √m ⟹ N_A² ∝ B²/m²。 -/
def foldingsSq (B m : ℝ) : ℝ := B * B / (m * m)

/-- FC7★：N_A² 随质量减小而增大——μ→1（m_eff→0）⟹ 可增长代数发散。
    这是"μ 在稳定性这一侧是纯负作用"的严格表述。 -/
theorem foldings_sq_antitone_mass (B m₁ m₂ : ℝ) (hB : B ≠ 0)
    (hm₁ : 0 < m₁) (h : m₁ < m₂) :
    foldingsSq B m₂ < foldingsSq B m₁ := by
  unfold foldingsSq
  have hB2 : 0 < B * B := by simpa [sq] using sq_pos_of_ne_zero hB
  have hsq : m₁ * m₁ < m₂ * m₂ := by nlinarith
  have hinv : 1 / (m₂ * m₂) < 1 / (m₁ * m₁) := one_div_lt_one_div_of_lt (by positivity : 0 < m₁ * m₁) hsq
  calc
    B * B / (m₂ * m₂) = (B * B) * (1 / (m₂ * m₂)) := by ring
    _ < (B * B) * (1 / (m₁ * m₁)) := mul_lt_mul_of_pos_left hinv hB2
    _ = B * B / (m₁ * m₁) := by ring

/-! ### ⑤ 机械门：PF7 反解成场强上限 -/

/-- FC8★：FRC 线圈的**场强上限**——由 PF7 的 hoop 应力判据反解。
    薄壁环 σ = B²R_c/(2μ₀t) ≤ σ_y ⟹ B² ≤ 2μ₀σ_y·t/R_c。
    这是 10cm 级装置的硬天花板：不是材料不够强，是 B 上不去。 -/
theorem frc_field_cap (B μ₀ σ_y t R_c : ℝ) (hμ : 0 < μ₀) (ht : 0 < t)
    (hR : 0 < R_c) (hB : B ≠ 0) :
    PlasmaFusion.hoopStress B μ₀ R_c t ≤ σ_y → B * B ≤ 2 * μ₀ * σ_y * t / R_c := by
  intro h
  have hr := (PlasmaFusion.radius_upper_bound_by_yield B μ₀ t σ_y R_c hμ ht hB).mp h
  have hB2 : 0 < B * B := by simpa [sq] using sq_pos_of_ne_zero hB
  have h1 : R_c * (B * B) ≤ 2 * μ₀ * σ_y * t := (le_div_iff₀ hB2).mp hr
  exact (le_div_iff₀ hR).mpr (by simpa [mul_comm] using h1)

/-- FC8b：场强上限随线圈半径增大而下降——小环允许更高的 B
    （这正是"紧凑 FRC"能用的工程杠杆，也是 Helion/TAE 走高场小环的原因）。 -/
theorem field_cap_antitone_radius (μ₀ σ_y t : ℝ) (hμ : 0 < μ₀) (hσ : 0 < σ_y) (ht : 0 < t)
    (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) (h : R₁ < R₂) :
    2 * μ₀ * σ_y * t / R₂ < 2 * μ₀ * σ_y * t / R₁ := by
  have hC : 0 < 2 * μ₀ * σ_y * t := by positivity
  have hinv : 1 / R₂ < 1 / R₁ := one_div_lt_one_div_of_lt hR₁ h
  calc
    2 * μ₀ * σ_y * t / R₂ = (2 * μ₀ * σ_y * t) * (1 / R₂) := by ring
    _ < (2 * μ₀ * σ_y * t) * (1 / R₁) := mul_lt_mul_of_pos_left hinv hC
    _ = 2 * μ₀ * σ_y * t / R₁ := by ring

/-! ### ⑥ RMF（旋转磁场）驱动窗口：时变电磁场这一支 -/

/-- FC9 输入：离子回旋频率 ω_ci = eB/m_i（RMF 窗口的下界）。 -/
def ionCyclotron (e B m_i : ℝ) : ℝ := e * B / m_i

/-- FC9 输入：电子回旋频率 ω_ce = eB/m_e（RMF 窗口的上界）。 -/
def elecCyclotron (e B m_e : ℝ) : ℝ := e * B / m_e

/-- FC9★：RMF 驱动窗口下界随有效质量下降而**上移**——
    ω_ci ∝ 1/m_eff，μ↑ ⟹ RMF 必须工作在更高频率。
    质量取消不是免费午餐：它把"变化的电磁场"的驱动频段一起推高了。 -/
theorem rmf_window_mass_scaling (e B m₁ m₂ : ℝ) (he : 0 < e) (hB : 0 < B)
    (hm₁ : 0 < m₁) (h : m₁ < m₂) :
    ionCyclotron e B m₂ < ionCyclotron e B m₁ := by
  unfold ionCyclotron
  have hC : 0 < e * B := by positivity
  have hinv : 1 / m₂ < 1 / m₁ := one_div_lt_one_div_of_lt hm₁ h
  calc
    e * B / m₂ = (e * B) * (1 / m₂) := by ring
    _ < (e * B) * (1 / m₁) := mul_lt_mul_of_pos_left hinv hC
    _ = e * B / m₁ := by ring

/-- FC9b：RMF 窗口宽度 ∝ m_e/m_i 之比——窗口本身由质量比给定，
    与 B 无关（频率随 B 整体平移）。 -/
theorem rmf_window_ratio (e B m_e m_i : ℝ) (he : e ≠ 0) (hB : B ≠ 0)
    (hme : m_e ≠ 0) (hmi : m_i ≠ 0) :
    elecCyclotron e B m_e / ionCyclotron e B m_i = m_i / m_e := by
  unfold elecCyclotron ionCyclotron
  field_simp [he, hB, hme, hmi]

/-- FC11★★：RMF 窗口**存在**的充要条件——ω_ci < ω_ce ⟺ m_e < m_eff。

    RMF（旋转磁场）驱动电流的物理要求：场变得比离子回旋快（离子来不及跟随）
    却比电子回旋慢（电子被磁化跟着转 ⟹ 驱动出方位角电流）。
    代入 m_eff = m_i(1−μ) 得到一条**硬天花板**：
        μ < 1 − m_e/m_i
    D-T 数值（m_i = 2.5u）：μ < 1 − 2.194e−4 = **0.99978**。

    含义：质量取消不能把有效质量压到电子质量以下，否则"变化的电磁场"
    这一支（用户要求结合的 FRC 技术）**整体失效**——不是效率下降，
    是驱动窗口消失。这是本轮新增的第四道门。 -/
theorem rmf_window_exists_iff (e B m_e m_eff : ℝ) (he : 0 < e) (hB : 0 < B)
    (hme : 0 < m_e) (hm : 0 < m_eff) :
    ionCyclotron e B m_eff < elecCyclotron e B m_e ↔ m_e < m_eff := by
  unfold ionCyclotron elecCyclotron
  have hC : 0 < e * B := by positivity
  constructor
  · intro h
    have h1 : (e * B) * m_e < (e * B) * m_eff := (div_lt_div_iff₀ hm hme).mp h
    nlinarith
  · intro h
    have h1 : (e * B) * m_e < (e * B) * m_eff := by nlinarith
    exact (div_lt_div_iff₀ hm hme).mpr h1

/-- FC11b：窗口关闭定理——μ ≥ 1 − m_e/m_i ⟹ RMF 窗口不存在
    （ω_ci ≥ ω_ce，离子比电子转得还快）。 -/
theorem rmf_window_closed_at_large_mu (e B m_e m_i μ : ℝ) (he : 0 < e) (hB : 0 < B)
    (hme : 0 < m_e) (hmi : 0 < m_i) (hμle : 1 - m_e / m_i ≤ μ) (hμ1 : μ < 1) :
    ¬ ionCyclotron e B (m_i * (1 - μ)) < elecCyclotron e B m_e := by
  intro h
  have hpos1 : 0 < 1 - μ := by linarith
  have hm_eff_pos : 0 < m_i * (1 - μ) := by positivity
  have hlt : m_e < m_i * (1 - μ) :=
    (rmf_window_exists_iff e B m_e (m_i * (1 - μ)) he hB hme hm_eff_pos).mp h
  have hle : m_i * (1 - μ) ≤ m_e := by
    have hstep : m_i * (1 - μ) ≤ m_i * (m_e / m_i) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hmi)
    rwa [mul_div_cancel₀ m_e (ne_of_gt hmi)] at hstep
  linarith

/-! ### ⑦ 唯一不变量 Θ ≡ B²/m_eff -/

/-- FC10 输入：Θ ≡ B²/m_eff —— 本模块的**唯一无量纲组合**（差一个常数）。 -/
def theta (B m : ℝ) : ℝ := B * B / m

/-- FC10 输入：S*² 写成 Θ 的形式（r_s²e²Θ/(4kT) 差常数）。 -/
def sStarSqTheta (r_s e kT Θ : ℝ) : ℝ := r_s * r_s * e * e * Θ / (4 * kT)

/-- FC10 输入：τ_E² 写成 Θ 的形式（∝ Θ）。 -/
def tauESqTheta (c Θ : ℝ) : ℝ := c * Θ

/-- FC10★★：**增益–稳定性权衡**——S*²/τ_E² 与 Θ（也就是与 B 和 m_eff）都无关。
    推论（数值层展开）：固定 S* 预算（动力学稳定性边界）时
        B²/m_eff = const ⟹ B ∝ √m_eff
        gain ∝ B³/√m_eff ∝ (√m_eff)³/√m_eff = m_eff
    即 **μ→1 时可得增益反而 ∝ m_eff → 0**：为了把 S* 压回预算内必须同步降 B，
    而降 B 的损失（∝B³）快过输运收益（∝1/√m）。 -/
theorem sstar_over_tau_theta_invariant (r_s e kT c Θ₁ Θ₂ : ℝ)
    (hkT : kT ≠ 0) (hc : c ≠ 0) (hΘ₁ : Θ₁ ≠ 0) (hΘ₂ : Θ₂ ≠ 0) :
    sStarSqTheta r_s e kT Θ₁ / tauESqTheta c Θ₁ =
      sStarSqTheta r_s e kT Θ₂ / tauESqTheta c Θ₂ := by
  unfold sStarSqTheta tauESqTheta
  field_simp [hΘ₁, hΘ₂, hkT, hc]

/-- FC10b：不变量 Θ 本身随质量下降而上升（μ↑ ⟹ Θ↑ ⟹ S*↑ 与 τ_E↑ 同时发生）。 -/
theorem theta_antitone_mass (B m₁ m₂ : ℝ) (hB : B ≠ 0) (hm₁ : 0 < m₁) (h : m₁ < m₂) :
    theta B m₂ < theta B m₁ := by
  unfold theta
  have hB2 : 0 < B * B := by simpa [sq] using sq_pos_of_ne_zero hB
  have hsq : m₁ * m₁ < m₂ * m₂ := by nlinarith
  have hinv : 1 / m₂ < 1 / m₁ := one_div_lt_one_div_of_lt (by positivity : 0 < m₁) (by linarith)
  calc
    B * B / m₂ = (B * B) * (1 / m₂) := by ring
    _ < (B * B) * (1 / m₁) := mul_lt_mul_of_pos_left hinv hB2
    _ = B * B / m₁ := by ring

/-! ### ⑧ 人工场选频判据：RMF 驱动频率定量化（FC12） -/

/-- FC12 输入：人工场 RMF 驱动角频率 = k × 离子回旋角频率 ω_ci（选频倍数 k∈[2,5]）。
    这是"人工场调制频率的最优区间"：略高于离子回旋——离子刚磁化、能驱动方位角电流
    （好用），远低于电子回旋（不纯加热），且低于装置光速响应上限（信号传得过装置）。
    数值层（D-T，B=9T）：ω_ci=(eB/m_i)/2π≈55MHz，最优≈138-276MHz（VHF）。 -/
def rmfAngFreq (k e B m : ℝ) : ℝ := k * ionCyclotron e B m

/-- FC12 输入：装置光速响应上限 ω_max = c/L（空间场波动跨越装置长度的频率）。
    调制频率超过 ω_max，则空间场信号传不过装置（MS3：空间场波动速度=c）。 -/
def lightLimit (c L : ℝ) : ℝ := c / L

/-- FC12★：人工场选频带非退化——2×ω_ci < 5×ω_ci（最优倍数区间存在）。
    即总能取 k∈[2,5] 使驱动频率落在"好用"区间内（FC9 RMF 窗口下界之上）。 -/
theorem rmf_selection_band_nonempty (e B m : ℝ) (he : 0 < e) (hB : 0 < B) (hm : 0 < m) :
    rmfAngFreq 2 e B m < rmfAngFreq 5 e B m := by
  unfold rmfAngFreq
  have hci : 0 < ionCyclotron e B m := by
    unfold ionCyclotron
    positivity
  nlinarith

/-- FC12c：选频倍数在开区间 [2,5] 内的任意 k 都落在 RMF 窗口下界之上 ——
    人工场选频不越出 FC9 的物理窗口（ω=k·ω_ci ≥ ω_ci）。 -/
theorem rmf_selection_above_ci (k e B m : ℝ) (hk : 1 ≤ k) (he : 0 < e) (hB : 0 < B)
    (hm : 0 < m) :
    ionCyclotron e B m ≤ rmfAngFreq k e B m := by
  unfold rmfAngFreq
  have hci : 0 < ionCyclotron e B m := by
    unfold ionCyclotron
    positivity
  nlinarith

def FRC_COMPACT_SCOPE : String :=
  "FRC迭代版紧凑装置代数骨架: FRC β≈1平衡(FC1 n=βB²/4μ₀kT, nT只由B定/FC1c ∝B²) + s参数锁定(FC2★ S*²ρ_i²=βr_s²/2 / FC3 S*²m=C² / FC4 τ_E²m=C²) + FC5★★锁定定理(S*/τ_E与m,B无关 ⇒ 不可能只改τ_E不改S*) + FC6★ τ_A²=βmr_s²/4kT与B无关(μ↑⟹不稳定加速) + FC7★ N_A²∝B²/m²发散 + FC8★ 机械门B²≤2μ₀σ_yt/R_c(PF7反解) + FC9★ RMF窗口ω_ci∝1/m_eff + FC10★★ 唯一不变量Θ=B²/m_eff, 固定S*预算⟹增益∝m_eff→0 + FC11★★ RMF窗口存在⟺m_e<m_eff ⟹ 硬天花板μ<1−m_e/m_i=0.99978(D-T) + FC12★★ 人工场选频(RMF驱动频率ω=k·ω_ci, k∈[2,5]最优, 选频带非退化, 上界c/L装置光速响应); 数值层输入: Bohm系数f_B, S*稳定边界, 材料σ_y, ⟨σv⟩用Bosch-Hale; 开放缺口: μ对⟨σv⟩的影响未建模, μ主动产生机制=第二输入缺口(未变); 无新物理预言"

end FrcCompact
end
