-- ProjectionPhysics — AetherBand：「以太」层级 —— 集体频率带、瞬时相关、以及两种「超光速」
--
-- leo（2026-10-29）原话（本节即为该假设的形式化尝试）：
--   「宇宙的本身是振动频率和维度的超广阔的集体，在局域频率较低且不一致的时候，
--    会有波动现象，比如光速和空间涟漪，超广意场是范围更大的，所以可以瞬时影响彼此，
--    远比光速要快，因为光速是空间流动速度的等效，实际上，超广意场观下，有更快的方式。」
--
-- 本模块把它拆成四个可判定的层（不做新物理宣言，只把「瞬时」与「更快」写成命题）：
--
--   ① 频率带 ⟹ 波速（AB1–AB3）：相位速度 v_ph = ω/k；**波矢越小（波长越长 ⟹ 越「广」）
--      相位速度越大**，且**无界**（k → 0⁺ 给任意大的 v_ph）。这正是「范围更大 ⟹ 影响
--      更远/更快」的代数内核：不是信号跑得快，是**一个相位横跨更长的距离**。
--      ⇒ 局域频率「低且不一致」⟹ k 有限且逐点不同 ⟹ 有相位梯度 ⟹ 有波（AB4/AB5 的对照：
--        相位场沿空间变化 = 波；常相位场 = 无波）。
--
--   ② 同步是等价关系（AB4–AB5）：相位相同 `Synced θ` 自反/对称/传递 ⟹ 「瞬时彼此影响」
--      的精确形式是**共用一个相位**，而「全同步」⟺ 相位场为常数 ⟺ k = 0 模（AB5）。
--      ⚠ 这条同时是本模块的诚实核：k = 0 的集体模**没有相位差可传**，见 ④。
--
--   ③ 零带宽 ⟹ 零信道（AB6–AB9）：一个量若是「同一时刻处处相同、且不随时间变化」，
--      它就**不携带可分辨的符号**（AB7/AB8）；Shannon 型容量 C = d·B·log₂(1+SNR) 在
--      B = 0 处为 0（AB9），且容量**对维度线性、对单模速度无影响**（AB10）——
--      ⟹ 「更多维度」给的是**容量**不是**速度**。
--
--   ④ 两种「超光速」，必须分开（AB11–AB15）：
--      Ⅰ 拖曳型（仓库已有）：GQC3 —— 静止系等效速度 = 1 + v，流动系局部 ≤ 1。
--      Ⅱ 层级型（本轮新提出）：超广意场若是**独立的一层**，它有自己的光锥
--         c₂ = ratio·c（ratio = 两级格距之比）。AB13/AB14 写死它的判据与死法：
--         ratio ≠ 1 ⟹ 两锥不重合（真新速度）；**ratio = 1（同一格点导出）⟹ 两锥重合
--         ⟹ 没有新速度** —— 这是本假设唯一的生死线。
--      AB15 是必须一起登记的**不可区分性**：单点测到一个 1.5 倍的「快」，拖曳型与
--      层级型在数值上完全一样 ⟹ 单点测速无法分辨两机制。
--
-- 诚实边界（写死，防后续 session 过度声称）：
--   · AB1–AB15 全是初等实分析/代数（真但平凡）——本模块**不**证明宇宙是振动的，
--     也不证明存在快于 c 的影响；它只把「瞬时」与「更快」写成两条互相排斥的分支，
--     并给出每条分支的判据。分支 I 无新物理；分支 II 需要一条**新公设 + 一个新的
--     无量纲比 ratio**（与 M₀/λ 同款的输入缺口，未闭合）。
--   · 「瞬时影响」在本模块里被严格化成「共相位」——**不含传信**。若把同步写成传比特，
--     即撞 paper3 的死法 (c)（与已确立物理事实矛盾）；AB7/AB8 正是这一条的形式化。
--   · 与 SLS1（c = 空间本身的等效速度）不冲突：本模块的 v_ph 是**相位**速度，
--     c 是**介质**的等效速度；两者重合只在 ω = c·k 的线性色散上（AB17）。
--
-- 死法（写死）：
--   ① 若某集体模能在 k = 0（无限波长）处携带随时间变化的可分辨符号，则 AB7/AB8 死，
--      「瞬时 ⟹ 不可传信」这一整条被推翻（即：发现真正的手段）。
--   ② 若两级格距比 ratio 能被框架已有结构（P1–P4）导出而不引入新输入，则 AB13/AB14
--      的分支 II 不再是「新公设」，缺口关闭；反之 ratio 永远是输入。
--   ③ 若观测到一个「快的因子」既非拖曳（GQC3 的 1+v）也非层级（ratio），两分支皆死。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProjectionPhysics.AetherBand

-- ---------------------------------------------------------------------------
-- ① 频率带 ⟹ 波速
-- ---------------------------------------------------------------------------

/-- 相位速度：v_ph = ω / k（单位：c = 1；k 为波矢模，ω 为角频率）。
    「广」= k 小（波长大）；「局域频率低且不一致」= k 逐点有限且不同。 -/
noncomputable def phaseSpeed (ω k : ℝ) : ℝ := ω / k

/-- AB1 ★ 波长越长 ⟹ 相位速度越大（同一频率带内）。
    这是「范围更大 ⟹ 影响更快」的**代数内核**：不是信号加速，
    而是同一个相位份额横跨了更长距离。 -/
theorem phaseSpeed_antitone_in_k {ω k₁ k₂ : ℝ}
    (hω : 0 < ω) (hk₁ : 0 < k₁) (h : k₁ < k₂) :
    phaseSpeed ω k₂ < phaseSpeed ω k₁ := by
  have hk₂ : 0 < k₂ := lt_trans hk₁ h
  have hinv : 1 / k₂ < 1 / k₁ := one_div_lt_one_div_of_lt hk₁ h
  calc phaseSpeed ω k₂ = ω * (1 / k₂) := by simp [phaseSpeed, div_eq_mul_inv]
    _ < ω * (1 / k₁) := mul_lt_mul_of_pos_left hinv hω
    _ = phaseSpeed ω k₁ := by simp [phaseSpeed, div_eq_mul_inv]

/-- AB2 ★★ 无界性：对任意目标速度 M，都存在一个足够「广」（k 足够小）的模，
    其相位速度超过 M。⟹ **k → 0⁺ 时相位速度无上界**，
    即「超广意场可以瞬时影响彼此」的精确代数形式。 -/
theorem unbounded_phaseSpeed (ω : ℝ) (hω : 0 < ω) (M : ℝ) :
    ∃ k : ℝ, 0 < k ∧ M < phaseSpeed ω k := by
  rcases le_or_gt (M + 1) 0 with hM | hM
  · refine ⟨1, one_pos, ?_⟩
    have : phaseSpeed ω 1 = ω := by simp [phaseSpeed]
    rw [this]; linarith
  · refine ⟨ω / (M + 1), div_pos hω hM, ?_⟩
    have hval : phaseSpeed ω (ω / (M + 1)) = M + 1 := by
      simp only [phaseSpeed, div_div_eq_mul_div]
      field_simp
    rw [hval]; linarith

/-- 两点之间的相位滞后：phaseLag k d = k · d（同一时刻、距离 d、波矢 k）。 -/
def phaseLag (k d : ℝ) : ℝ := k * d

/-- AB3 ★★ 相位滞后可任意小：固定距离 d > 0，任给 ε > 0，都存在一个模
    使两点相位差 < ε。⟹ **「瞬时彼此影响」= 任意远的两点相位差趋于零**。
    （注意：这是**共相位**，不是信号的传递——见 ③。） -/
theorem phaseLag_arbitrarily_small {d : ℝ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℝ, 0 < k ∧ phaseLag k d < ε := by
  refine ⟨ε / (2 * d), div_pos hε (by linarith), ?_⟩
  have hval : phaseLag (ε / (2 * d)) d = ε / 2 := by
    simp only [phaseLag]
    field_simp
  rw [hval]; linarith

-- ---------------------------------------------------------------------------
-- ② 同步 = 共相位（等价关系）
-- ---------------------------------------------------------------------------

/-- 「同步」：同一时刻相位相同。这是在流动系/集体模下的精确形式。 -/
def Synced {X : Type*} (θ : X → ℝ) (x y : X) : Prop := θ x = θ y

/-- AB4 ★ 同步是等价关系（自反 / 对称 / 传递）。
    ⟹ 以太的「同时面」在相位语言下是良定义的划分，而不是逐对的巧合。 -/
theorem synced_equivalence {X : Type*} (θ : X → ℝ) : Equivalence (Synced θ) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- AB5 ★★ k = 0 集体模 ⟹ 处处同步：常数相位场使**任意两点**共相位，
    无需任何传播。这是「超广意场瞬时影响」的**正面**（也是唯一站得住的读法）。 -/
theorem global_mode_all_synced {X : Type*} (θ : X → ℝ) (c : ℝ) (h : ∀ x, θ x = c) :
    ∀ x y, Synced θ x y := by
  intro x y
  simp only [Synced, h x, h y]

/-- 相位场（线性波矢）：phaseAt k x = k · x。 -/
def phaseAt (k x : ℝ) : ℝ := k * x

/-- AB6 ★ 局域频率「不一致」⟹ 有波：k > 0 且 d > 0 时两点相位不同
    （相位场沿空间变化 = 波）。与 AB5 构成对照：
    **共相位（无波，瞬时同步） vs 有梯度（有波，需传播）**。 -/
theorem distinct_phase_of_gradient {k d : ℝ} (hk : 0 < k) (hd : 0 < d) :
    phaseAt k d ≠ phaseAt k 0 := by
  simp only [phaseAt, mul_zero]
  exact mul_ne_zero hk.ne' hd.ne'

-- ---------------------------------------------------------------------------
-- ③ 零带宽 ⟹ 零信道（瞬时相关不是传信）
-- ---------------------------------------------------------------------------

/-- 带零：一个时间序列在所有时刻与 n = 0 时刻相同（频带为零）。 -/
def BandZero {α : Type*} (s : ℤ → α) : Prop := ∀ n, s n = s 0

/-- AB7 ★★ 零带宽 ⟺ 序列为常数 ⟹ **无可分辨的符号**。
    （若所有时刻相同，则任意两个时刻无法区分 ⟹ 传不了任何比特。） -/
theorem bandZero_iff_const {α : Type*} (s : ℤ → α) :
    BandZero s ↔ ∀ m n, s m = s n := by
  constructor
  · intro h m n
    rw [h m, h n]
  · intro h n
    exact h n 0

/-- AB8 ★★ 可传信 ⟹ 带宽非零：若存在两个时刻可区分，则序列不是常数，
    即频带不可能为零。⟹ **「更快」若要求传比特，就必须有带宽；
    带宽为零的瞬时模恰好传不了比特**。 -/
theorem message_needs_bandwidth {α : Type*} (s : ℤ → α)
    (h : ∃ m n, s m ≠ s n) : ¬ BandZero s := by
  intro hz
  obtain ⟨m, n, hmn⟩ := h
  exact hmn ((bandZero_iff_const s).mp hz m n)

/-- Shannon 型容量（每单位时间，单位模）：C = d · B · log₂(1 + SNR)。 -/
noncomputable def capacity (dim B snr : ℝ) : ℝ :=
  dim * B * (Real.log (1 + snr) / Real.log 2)

/-- AB9 ★★ 带宽为零 ⟹ 容量为零：**瞬时通道的信道容量恰为 0**。 -/
theorem capacity_zero_band (dim snr : ℝ) : capacity dim 0 snr = 0 := by
  simp [capacity]

/-- AB10 ★★ 维度只增容量，不改单模速度：容量对维度**线性可加**。 -/
theorem capacity_add_dim (d₁ d₂ B snr : ℝ) :
    capacity (d₁ + d₂) B snr = capacity d₁ B snr + capacity d₂ B snr := by
  simp only [capacity]
  ring

/-- AB10b 容量随带宽严格增（SNR > 1、维度 > 0 时）。 -/
theorem capacity_mono_band {dim B₁ B₂ snr : ℝ}
    (hdim : 0 < dim) (hsnr : 1 < snr) (h : B₁ < B₂) :
    capacity dim B₁ snr < capacity dim B₂ snr := by
  have hlog : 0 < Real.log (1 + snr) / Real.log 2 :=
    div_pos (Real.log_pos (by linarith)) (Real.log_pos (by norm_num))
  have h1 : dim * B₁ < dim * B₂ := mul_lt_mul_of_pos_left h hdim
  calc capacity dim B₁ snr = (dim * B₁) * (Real.log (1 + snr) / Real.log 2) := by
        simp only [capacity]
    _ < (dim * B₂) * (Real.log (1 + snr) / Real.log 2) :=
        mul_lt_mul_of_pos_right h1 hlog
    _ = capacity dim B₂ snr := by simp only [capacity]

-- ---------------------------------------------------------------------------
-- ④ 两种「超光速」：拖曳型（已有） vs 层级型（新提出）
-- ---------------------------------------------------------------------------

/-- Ⅰ 拖曳型：GQC3 的静止系等效速度 = 1 + v（c = 1 单位）。 -/
def dragSpeed (v : ℝ) : ℝ := 1 + v

/-- AB11 ★ 拖曳确实可超光速（v > 0 ⟹ 等效速度 > 1），而流动系局部仍 ≤ 1
    （后者是仓库已有的 GQC3a/b，本模块不重证）。 -/
theorem dragSpeed_gt_one {v : ℝ} (hv : 0 < v) : 1 < dragSpeed v := by
  simp only [dragSpeed]; linarith

/-- Ⅱ 层级型：独立层的光锥 c₂ = ratio · c（ratio = 两级格距之比 a/a₂）。 -/
def coarseSpeed (ratio c : ℝ) : ℝ := ratio * c

/-- AB12 同一格点（ratio = 1）⟹ 两锥重合 ⟹ **没有新速度**。 -/
theorem same_lattice_no_new_speed (c : ℝ) : coarseSpeed 1 c = c := by
  simp [coarseSpeed]

/-- AB13 ★★ 层级型超光速的判据：ratio > 1 且 c > 0 ⟹ c₂ > c。 -/
theorem coarseSpeed_gt {ratio c : ℝ} (hr : 1 < ratio) (hc : 0 < c) :
    c < coarseSpeed ratio c := by
  have h : 1 * c < ratio * c := mul_lt_mul_of_pos_right hr hc
  simpa [coarseSpeed] using h

/-- AB14 ★★★ 生死线：ratio ≠ 1 且 c > 0 ⟹ 两锥**不重合**（真新速度）；
    与之对偶，ratio = 1 ⟹ 重合（AB12）。
    ⟹ 「超广意场」若是独立层，必须给出一个 ≠ 1 的 ratio；这个 ratio 是
    **框架外的新无量纲输入**（与 M₀、λ 同款），不能由 P1–P4 免费得到。 -/
theorem two_cones_distinct {ratio c : ℝ} (hr : ratio ≠ 1) (hc : 0 < c) :
    coarseSpeed ratio c ≠ c := by
  intro h
  have hmul : ratio * c = 1 * c := by
    simpa [coarseSpeed] using h
  exact hr (mul_right_cancel₀ hc.ne' hmul)

/-- AB15 ★★ 不可区分性（**死法**）：单点测到「1.5 倍」时，拖曳型（v = 0.5）与
    层级型（ratio = 1.5, c = 1）给出**完全相同的数值** ⟹ 单点测速无法分辨两机制，
    必须靠第二类测量（例如拖曳型的各向异性 vs 层级型的普适性）。 -/
theorem drag_vs_coarse_indistinguishable :
    dragSpeed (1 / 2) = coarseSpeed (3 / 2) 1 := by
  simp only [dragSpeed, coarseSpeed]; norm_num

-- ---------------------------------------------------------------------------
-- ⑤ 与仓库既有线性色散的接口（v_ph = c 只在 ω = c·k 上成立）
-- ---------------------------------------------------------------------------

/-- AB16 线性色散 ω = c·k 时相位速度 = c：**c 属于色散关系，不属于相位场本身**。
    这正是「光速是空间流动速度的等效」的代数读法：c 是 ω/k 的比值，
    换一个色散关系（另一层）就换一个光锥。 -/
theorem phaseSpeed_of_linear_dispersion {c k : ℝ} (hk : k ≠ 0) :
    phaseSpeed (c * k) k = c := by
  simp only [phaseSpeed]
  field_simp

/-- AB18 ★★★ 范围 × 更新率 的上界：「相距 L 的两点相位差 < ε」（k·L < ε）与线性色散
    ω = c·k 合起来给出 ω < c·ε/L。⟹ **瞬时覆盖得越远（L 越大），它能承载的变化率越小**，
    且两者之积被介质光速封顶：``(同步范围 L) × (角频率 ω) < c·ε``。
    这就是「更快的方式」的**价格表**：范围与变化率不能同时任意大。 -/
theorem reach_rate_bound {c k L ε : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hph : k * L < ε) : c * k < c * ε / L := by
  have hk : k < ε / L := by
    rw [lt_div_iff₀ hL]
    linarith
  calc c * k < c * (ε / L) := mul_lt_mul_of_pos_left hk hc
    _ = c * ε / L := by ring

/-- AB17 ★ 无限波长模是静态的：k = 0 ⟹ ω = c·k = 0。
    ⟹ 集体模的「瞬时」与「静止」是同一件事的两面：
    **横跨全空间的相位不能承载任何变化**（与 AB7/AB8 合起来即为「瞬时 ⟹ 不可传信」）。 -/
theorem global_mode_is_static (c : ℝ) : c * 0 = 0 := by
  ring

end ProjectionPhysics.AetherBand
