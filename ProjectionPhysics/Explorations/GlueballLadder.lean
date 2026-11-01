-- ProjectionPhysics — GlueballLadder：胶球质量阶梯的 Lean 端（LAD1–LAD8）
--
-- leo（2026-11-01）：「用 lean 来证明」——把 `scripts/verify_glueball_ladder_prediction.py`
-- 里「M₀ 定死 + 阶梯规则定死」的算术内核从断言升格为定理。
--
-- 规则（与脚本逐条对应，**不含整数选择自由**）：
--   N = Σᵢ nᵢ²  或  Σᵢ nᵢ² + 1
--   nᵢ ∈ ℤ\{0}（三个方向都要在），+1 只在 max|nᵢ| ≥ 2（变体 II：要有环被扭过两圈以上）
--   质量：m² = N·M₀²（MassGap.strandMassSq），即 m = √N·M₀
--
-- 本模块证明的（全部零 sorry）：
--   LAD1 见证：3 / 6 / 7 / 9 / 15 可达（7 只能靠 +1，见 LAD2）
--   LAD2 ★ Legendre 核：7 不是三个（非零）平方和 ⟹ 7 必须靠集体项 +1
--   LAD3 ★★ 禁区：4 / 5 / 8 / 16 不可达（**无条件**，与枚举界 R 无关）
--   LAD4 ★★★ 禁区窗口定理：M₀ > 0 ⟹ 阶梯态的质量平方**不可能**落在
--        (15M₀², 17M₀²) 内（N=16 禁区），同理 (3,5)(4,6)(7,9)M₀²
--        —— 这是判死条件 D1 的形式化版本（等价于「质量不落在 √15·M₀–√17·M₀ 内」）
--   LAD5 ★★ 饱和定理（无标度）：N ≥ 25 ⟹ √(N+1) < (102/100)·√N
--        ⟹ ≥4 GeV 处相邻阶相对间距 < 2%（落阶判据失去分辨率，只剩禁区可判）
--   LAD6 阶梯质量对 N 严格单调
--   LAD7 MassGap 对接：m = √N·M₀ ⟹ m² = N·M₀²
--
-- 诚实边界（写死）：
--   · N=32 / N=40 两个禁区的不可达性**未在本模块证明**（需 |nᵢ| ≤ 6 的有界枚举，
--     Lean 端 interval_cases 代价过高）；该两条目前只在
--     `scripts/verify_glueball_ladder_prediction.py` 的 R=6 枚举里成立。
--     本模块把窗口定理写成**与 N 无关的形式**（`window_empty_sq`）：
--     谁给出 `¬ IsLadderN 32` 的证明，N=32 禁区立即免费成立。
--   · M₀ 仍是输入（SC6：框架零标度内容）；本模块只证「给定 M₀ 与规则后的结构」。
--   · 不产生 J^PC、不产生宽度/衰变/产生率（一个都没碰）。
--   · 不声称与格点数据一致（残差账本在脚本端；定理只谈规则的可达集）。

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import ProjectionPhysics.Explorations.MassGap

noncomputable section
namespace ProjectionPhysics.GlueballLadder

open ProjectionPhysics
open ProjectionPhysics.MassGap

/-! ### 规则 -/

/-- 三个方向的绕数平方和 Σᵢ nᵢ²。 -/
def baseN (a b c : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2

/-- 变体 II 的集体项许可：只有被扭过两圈以上（max|nᵢ| ≥ 2）才允许整体连接。 -/
def collectiveAllowed (a b c : ℤ) : Prop := 2 ≤ max (max |a| |b|) |c|

/-- 可达条数 N（变体 II）。三个方向都要在（nᵢ ≠ 0）。 -/
def IsLadderN (N : ℕ) : Prop :=
  ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    ((N : ℤ) = baseN a b c ∨ ((N : ℤ) = baseN a b c + 1 ∧ collectiveAllowed a b c))

/-- 阶梯质量：m = √N·M₀。 -/
def ladderMass (N : ℕ) (M₀ : ℝ) : ℝ := Real.sqrt (N : ℝ) * M₀

/-! ### 工具引理 -/

/-- 非零整数的平方 ≥ 1。 -/
lemma one_le_sq_of_ne_zero {a : ℤ} (h : a ≠ 0) : 1 ≤ a ^ 2 := by
  have h0 : 0 ≤ a ^ 2 := sq_nonneg a
  have h1 : a ^ 2 ≠ 0 := pow_ne_zero 2 h
  omega

/-- 平方 ≤ n 给出 -n ≤ a ≤ n（ℤ）。 -/
lemma abs_le_of_sq_le {a : ℤ} {n : ℕ} (h : a ^ 2 ≤ (n : ℤ)) :
    -((n : ℤ)) ≤ a ∧ a ≤ (n : ℤ) := by
  constructor
  · by_contra hc
    push Not at hc
    have h1 : (0 : ℤ) ≤ -a - ((n : ℤ) + 1) := by omega
    have h2 : (0 : ℤ) ≤ -a + ((n : ℤ) + 1) := by omega
    have hm : (0 : ℤ) ≤ (-a - ((n : ℤ) + 1)) * (-a + ((n : ℤ) + 1)) := mul_nonneg h1 h2
    nlinarith [hm, h, sq_nonneg (n : ℤ)]
  · by_contra hc
    push Not at hc
    have h1 : (0 : ℤ) ≤ a - ((n : ℤ) + 1) := by omega
    have h2 : (0 : ℤ) ≤ a + ((n : ℤ) + 1) := by omega
    have hm : (0 : ℤ) ≤ (a - ((n : ℤ) + 1)) * (a + ((n : ℤ) + 1)) := mul_nonneg h1 h2
    nlinarith [hm, h, sq_nonneg (n : ℤ)]

/-- 非零且平方 ≤ 16 的整数，其平方只能取 1 / 4 / 9 / 16（把无穷搜索压成 4 值枚举）。 -/
lemma sq_cases_16 {a : ℤ} (ha : a ≠ 0) (h : a ^ 2 ≤ (16 : ℤ)) :
    a ^ 2 = 1 ∨ a ^ 2 = 4 ∨ a ^ 2 = 9 ∨ a ^ 2 = 16 := by
  obtain ⟨lo, hi⟩ := abs_le_of_sq_le h
  have h1 : (1 : ℤ) ≤ a ^ 2 := one_le_sq_of_ne_zero ha
  interval_cases a <;> omega

/-! ### LAD1 可达见证 -/

/-- LAD1a：3 可达（(1,1,1) 的平方和，无集体项）。 -/
theorem ladder_three : IsLadderN 3 := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, Or.inl ?_⟩
  norm_num [baseN]

/-- LAD1b：6 可达（(1,1,2)，无集体项）。 -/
theorem ladder_six : IsLadderN 6 := by
  refine ⟨1, 1, 2, by norm_num, by norm_num, by norm_num, Or.inl ?_⟩
  norm_num [baseN]

/-- LAD1c：★ 7 可达，但**必须靠集体项**（(1,1,2) 的 6 再加 1；max|nᵢ| = 2 满足变体 II）。 -/
theorem ladder_seven : IsLadderN 7 := by
  refine ⟨1, 1, 2, by norm_num, by norm_num, by norm_num, Or.inr ⟨?_, ?_⟩⟩
  · norm_num [baseN]
  · norm_num [collectiveAllowed]

/-- LAD1d：9 可达（(1,2,2)，无集体项）。 -/
theorem ladder_nine : IsLadderN 9 := by
  refine ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, Or.inl ?_⟩
  norm_num [baseN]

/-- LAD1e：15 可达（(1,2,3) 的 14 再加 1；max = 3 ≥ 2）。 -/
theorem ladder_fifteen : IsLadderN 15 := by
  refine ⟨1, 2, 3, by norm_num, by norm_num, by norm_num, Or.inr ⟨?_, ?_⟩⟩
  · norm_num [baseN]
  · norm_num [collectiveAllowed]

/-! ### LAD2 Legendre 核 -/

/-- LAD2 ★ 7 不是三个（非零）平方和 —— 这是 7 必须靠 +1 的全部内容。 -/
theorem not_base_seven : ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ baseN a b c = 7 := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  unfold baseN at h
  have ha1 : 1 ≤ a ^ 2 := one_le_sq_of_ne_zero ha
  have hb1 : 1 ≤ b ^ 2 := one_le_sq_of_ne_zero hb
  have hc1 : 1 ≤ c ^ 2 := one_le_sq_of_ne_zero hc
  have ha2 : a ^ 2 ≤ (16 : ℤ) := by omega
  have hb2 : b ^ 2 ≤ (16 : ℤ) := by omega
  have hc2 : c ^ 2 ≤ (16 : ℤ) := by omega
  rcases sq_cases_16 ha ha2 with h1 | h1 | h1 | h1 <;>
    rcases sq_cases_16 hb hb2 with h2 | h2 | h2 | h2 <;>
      rcases sq_cases_16 hc hc2 with h3 | h3 | h3 | h3 <;> omega

/-! ### LAD3 禁区：4 / 5 / 8 / 16 不可达（无条件） -/

lemma not_base_four : ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ baseN a b c = 4 := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  unfold baseN at h
  have ha1 : 1 ≤ a ^ 2 := one_le_sq_of_ne_zero ha
  have hb1 : 1 ≤ b ^ 2 := one_le_sq_of_ne_zero hb
  have hc1 : 1 ≤ c ^ 2 := one_le_sq_of_ne_zero hc
  have ha2 : a ^ 2 ≤ (16 : ℤ) := by omega
  have hb2 : b ^ 2 ≤ (16 : ℤ) := by omega
  have hc2 : c ^ 2 ≤ (16 : ℤ) := by omega
  rcases sq_cases_16 ha ha2 with h1 | h1 | h1 | h1 <;>
    rcases sq_cases_16 hb hb2 with h2 | h2 | h2 | h2 <;>
      rcases sq_cases_16 hc hc2 with h3 | h3 | h3 | h3 <;> omega

lemma not_base_five : ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ baseN a b c = 5 := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  unfold baseN at h
  have ha1 : 1 ≤ a ^ 2 := one_le_sq_of_ne_zero ha
  have hb1 : 1 ≤ b ^ 2 := one_le_sq_of_ne_zero hb
  have hc1 : 1 ≤ c ^ 2 := one_le_sq_of_ne_zero hc
  have ha2 : a ^ 2 ≤ (16 : ℤ) := by omega
  have hb2 : b ^ 2 ≤ (16 : ℤ) := by omega
  have hc2 : c ^ 2 ≤ (16 : ℤ) := by omega
  rcases sq_cases_16 ha ha2 with h1 | h1 | h1 | h1 <;>
    rcases sq_cases_16 hb hb2 with h2 | h2 | h2 | h2 <;>
      rcases sq_cases_16 hc hc2 with h3 | h3 | h3 | h3 <;> omega

lemma not_base_eight : ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ baseN a b c = 8 := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  unfold baseN at h
  have ha1 : 1 ≤ a ^ 2 := one_le_sq_of_ne_zero ha
  have hb1 : 1 ≤ b ^ 2 := one_le_sq_of_ne_zero hb
  have hc1 : 1 ≤ c ^ 2 := one_le_sq_of_ne_zero hc
  have ha2 : a ^ 2 ≤ (16 : ℤ) := by omega
  have hb2 : b ^ 2 ≤ (16 : ℤ) := by omega
  have hc2 : c ^ 2 ≤ (16 : ℤ) := by omega
  rcases sq_cases_16 ha ha2 with h1 | h1 | h1 | h1 <;>
    rcases sq_cases_16 hb hb2 with h2 | h2 | h2 | h2 <;>
      rcases sq_cases_16 hc hc2 with h3 | h3 | h3 | h3 <;> omega

lemma not_base_fifteen : ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ baseN a b c = 15 := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  unfold baseN at h
  have ha1 : 1 ≤ a ^ 2 := one_le_sq_of_ne_zero ha
  have hb1 : 1 ≤ b ^ 2 := one_le_sq_of_ne_zero hb
  have hc1 : 1 ≤ c ^ 2 := one_le_sq_of_ne_zero hc
  have ha2 : a ^ 2 ≤ (16 : ℤ) := by omega
  have hb2 : b ^ 2 ≤ (16 : ℤ) := by omega
  have hc2 : c ^ 2 ≤ (16 : ℤ) := by omega
  rcases sq_cases_16 ha ha2 with h1 | h1 | h1 | h1 <;>
    rcases sq_cases_16 hb hb2 with h2 | h2 | h2 | h2 <;>
      rcases sq_cases_16 hc hc2 with h3 | h3 | h3 | h3 <;> omega

lemma not_base_sixteen : ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ baseN a b c = 16 := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  unfold baseN at h
  have ha1 : 1 ≤ a ^ 2 := one_le_sq_of_ne_zero ha
  have hb1 : 1 ≤ b ^ 2 := one_le_sq_of_ne_zero hb
  have hc1 : 1 ≤ c ^ 2 := one_le_sq_of_ne_zero hc
  have ha2 : a ^ 2 ≤ (16 : ℤ) := by omega
  have hb2 : b ^ 2 ≤ (16 : ℤ) := by omega
  have hc2 : c ^ 2 ≤ (16 : ℤ) := by omega
  rcases sq_cases_16 ha ha2 with h1 | h1 | h1 | h1 <;>
    rcases sq_cases_16 hb hb2 with h2 | h2 | h2 | h2 <;>
      rcases sq_cases_16 hc hc2 with h3 | h3 | h3 | h3 <;> omega

/-- LAD3a：4 不可达。两条腿都断：(1,1,1)+1 = 4 但 max|nᵢ| = 1 < 2（变体 II 不许），
    而 4 本身不是三个非零平方和。 -/
theorem four_not_ladder : ¬ IsLadderN 4 := by
  rintro ⟨a, b, c, ha, hb, hc, hbase | ⟨hbase, hcol⟩⟩
  · exact not_base_four ⟨a, b, c, ha, hb, hc, hbase.symm⟩
  · -- 4 = Σnᵢ² + 1 ⟹ Σnᵢ² = 3 ⟹ 三个平方都是 1 ⟹ max|nᵢ| = 1 < 2
    unfold baseN at hbase
    have ha1 : 1 ≤ a ^ 2 := one_le_sq_of_ne_zero ha
    have hb1 : 1 ≤ b ^ 2 := one_le_sq_of_ne_zero hb
    have hc1 : 1 ≤ c ^ 2 := one_le_sq_of_ne_zero hc
    have ha2 : a ^ 2 ≤ (1 : ℤ) := by omega
    have hb2 : b ^ 2 ≤ (1 : ℤ) := by omega
    have hc2 : c ^ 2 ≤ (1 : ℤ) := by omega
    obtain ⟨halo, hahi⟩ := abs_le_of_sq_le (n := 1) ha2
    obtain ⟨hblo, hbhi⟩ := abs_le_of_sq_le (n := 1) hb2
    obtain ⟨hclo, hchi⟩ := abs_le_of_sq_le (n := 1) hc2
    unfold collectiveAllowed at hcol
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all

/-- LAD3b：5 不可达（+1 分支需要 Σnᵢ² = 4，已被 4 否掉）。 -/
theorem five_not_ladder : ¬ IsLadderN 5 := by
  rintro ⟨a, b, c, ha, hb, hc, hbase | ⟨hbase, _⟩⟩
  · exact not_base_five ⟨a, b, c, ha, hb, hc, hbase.symm⟩
  · exact not_base_four ⟨a, b, c, ha, hb, hc, by unfold baseN at hbase ⊢; omega⟩

/-- LAD3c：8 不可达（+1 分支需要 Σnᵢ² = 7，被 LAD2 否掉）。 -/
theorem eight_not_ladder : ¬ IsLadderN 8 := by
  rintro ⟨a, b, c, ha, hb, hc, hbase | ⟨hbase, _⟩⟩
  · exact not_base_eight ⟨a, b, c, ha, hb, hc, hbase.symm⟩
  · exact not_base_seven ⟨a, b, c, ha, hb, hc, by unfold baseN at hbase ⊢; omega⟩

/-- LAD3d ★：16 不可达（16 与 15 都不是三个非零平方和）。
    —— 这是判死条件 D1 的算术核心：N=16 处没有阶梯。 -/
theorem sixteen_not_ladder : ¬ IsLadderN 16 := by
  rintro ⟨a, b, c, ha, hb, hc, hbase | ⟨hbase, _⟩⟩
  · exact not_base_sixteen ⟨a, b, c, ha, hb, hc, hbase.symm⟩
  · exact not_base_fifteen ⟨a, b, c, ha, hb, hc, by unfold baseN at hbase ⊢; omega⟩

/-! ### LAD4 禁区窗口定理（判死条件 D1）

一般形式 `window_empty_sq`：不可达的 N 在质量平方轴上撑开一个空窗
((N−1)·M₀², (N+1)·M₀²)。四个实例 4 / 5 / 8 / 16 全部落地。 -/

/-- LAD4 ★★★ 一般窗口定理：若 N 不可达，则没有任何阶梯态的质量平方落在
    ((N−1)·M₀², (N+1)·M₀²) 内（M₀ > 0，N ≥ 1）。 -/
theorem window_empty_sq {N : ℕ} (hNpos : 0 < N) (hN : ¬ IsLadderN N) {M₀ : ℝ} (hM : 0 < M₀)
    {K : ℕ} (hK : IsLadderN K)
    (hlo : strandMassSq (N - 1) M₀ < strandMassSq K M₀)
    (hhi : strandMassSq K M₀ < strandMassSq (N + 1) M₀) : False := by
  have hpos : (0 : ℝ) < M₀ ^ 2 := by positivity
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  unfold strandMassSq at hlo hhi
  rw [hcast] at hlo
  push_cast at hhi
  have h1 : (N : ℝ) - 1 < (K : ℝ) := by nlinarith [hlo, hpos]
  have h2 : (K : ℝ) < (N : ℝ) + 1 := by nlinarith [hhi, hpos]
  have hKle : K ≤ N := by
    by_contra hcon
    push Not at hcon
    have hc : ((N + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : N + 1 ≤ K)
    push_cast at hc
    linarith
  have hNle : N ≤ K := by
    by_contra hcon
    push Not at hcon
    have hc : ((K + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : K + 1 ≤ N)
    push_cast at hc
    linarith
  have : K = N := le_antisymm hKle hNle
  exact hN (this ▸ hK)

/-- LAD4' ★★★ N=16 禁区（D1 的形式化版本）：M₀ > 0 ⟹ 阶梯态的质量平方不在
    (15M₀², 17M₀²) 内。等价地：质量不在 √15·M₀–√17·M₀ 内
    （M₀ = 987.3 MeV 时 = 3824–4071 MeV）。
    **判据**：该区间内一旦出现任何纯规范胶球态，本模型的阶梯就死了。 -/
theorem sixteen_window_empty {M₀ : ℝ} (hM : 0 < M₀) {K : ℕ} (hK : IsLadderN K) :
    ¬ (strandMassSq 15 M₀ < strandMassSq K M₀ ∧ strandMassSq K M₀ < strandMassSq 17 M₀) := by
  rintro ⟨hlo, hhi⟩
  exact window_empty_sq (by norm_num) sixteen_not_ladder hM hK hlo hhi

/-- LAD4'' 其余三个窗口（4 / 5 / 8 禁区，都在 4 GeV 以下但同样是硬判据）：
    质量平方不在 (3,5)M₀²、(4,6)M₀²、(7,9)M₀² 内。 -/
theorem four_window_empty {M₀ : ℝ} (hM : 0 < M₀) {K : ℕ} (hK : IsLadderN K) :
    ¬ (strandMassSq 3 M₀ < strandMassSq K M₀ ∧ strandMassSq K M₀ < strandMassSq 5 M₀) := by
  rintro ⟨hlo, hhi⟩
  exact window_empty_sq (by norm_num) four_not_ladder hM hK hlo hhi

theorem five_window_empty {M₀ : ℝ} (hM : 0 < M₀) {K : ℕ} (hK : IsLadderN K) :
    ¬ (strandMassSq 4 M₀ < strandMassSq K M₀ ∧ strandMassSq K M₀ < strandMassSq 6 M₀) := by
  rintro ⟨hlo, hhi⟩
  exact window_empty_sq (by norm_num) five_not_ladder hM hK hlo hhi

theorem eight_window_empty {M₀ : ℝ} (hM : 0 < M₀) {K : ℕ} (hK : IsLadderN K) :
    ¬ (strandMassSq 7 M₀ < strandMassSq K M₀ ∧ strandMassSq K M₀ < strandMassSq 9 M₀) := by
  rintro ⟨hlo, hhi⟩
  exact window_empty_sq (by norm_num) eight_not_ladder hM hK hlo hhi

/-! ### LAD5 饱和定理（无标度）：N ≥ 25 ⟹ 相对间距 < 2% -/

/-- LAD5 ★★ 相邻阶相对间距 < 2%（N ≥ 25，**与 M₀ 无关**）。
    √(1+1/N) < 1.02 ⟺ 1/N < 0.0404 ⟺ N > 24.75。
    ⟹ ≥4 GeV 处「落阶」判据失去分辨率（脚本实测随机基线 100%），只剩禁区可判。 -/
theorem rung_spacing_lt_two_percent (N : ℕ) (hN : 25 ≤ N) :
    Real.sqrt ((N : ℝ) + 1) < (102 / 100 : ℝ) * Real.sqrt (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN25 : (25 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) ≤ (102 / 100 : ℝ) * Real.sqrt (N : ℝ) := by positivity
  have hsq : ((N : ℝ) + 1) < ((102 / 100 : ℝ) * Real.sqrt (N : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hN0)]
    nlinarith
  calc Real.sqrt ((N : ℝ) + 1)
      < Real.sqrt (((102 / 100 : ℝ) * Real.sqrt (N : ℝ)) ^ 2) :=
        Real.sqrt_lt_sqrt (by positivity) hsq
    _ = (102 / 100 : ℝ) * Real.sqrt (N : ℝ) := Real.sqrt_sq hpos

/-- LAD5b 质量版：相邻阶的质量差 < 该阶质量的 2%（M₀ > 0）。 -/
theorem rung_spacing_lt_two_percent_mass (N : ℕ) (hN : 25 ≤ N) {M₀ : ℝ} (hM : 0 < M₀) :
    ladderMass (N + 1) M₀ - ladderMass N M₀ < (2 / 100 : ℝ) * ladderMass N M₀ := by
  unfold ladderMass
  push_cast
  have h1 : Real.sqrt ((N : ℝ) + 1) < (102 / 100 : ℝ) * Real.sqrt (N : ℝ) :=
    rung_spacing_lt_two_percent N hN
  have h2 : Real.sqrt ((N : ℝ) + 1) * M₀ < (102 / 100 : ℝ) * Real.sqrt (N : ℝ) * M₀ :=
    mul_lt_mul_of_pos_right h1 hM
  nlinarith [h2]

/-! ### LAD6 单调性 -/

/-- LAD6：阶梯质量对 N 严格单调（√ 严格单调 × M₀ > 0）。 -/
theorem ladderMass_strictMono {K L : ℕ} (h : K < L) {M₀ : ℝ} (hM : 0 < M₀) :
    ladderMass K M₀ < ladderMass L M₀ := by
  unfold ladderMass
  have hKL : (K : ℝ) < (L : ℝ) := by exact_mod_cast h
  have hsq : Real.sqrt (K : ℝ) < Real.sqrt (L : ℝ) :=
    Real.sqrt_lt_sqrt (by positivity) hKL
  exact mul_lt_mul_of_pos_right hsq hM

/-! ### LAD7 与 MassGap 的对接 -/

/-- LAD7：`strandMassSq N M₀ = N·M₀²` 与阶梯质量一致：m² = N·M₀²（对任意 M₀）。
    把 MassGap 的 MG1（m² = N·M₀²）与本模块的 m = √N·M₀ 接上。 -/
theorem ladderMass_sq (N : ℕ) (M₀ : ℝ) :
    ladderMass N M₀ ^ 2 = strandMassSq N M₀ := by
  unfold ladderMass strandMassSq
  rw [mul_pow, Real.sq_sqrt (by positivity)]

end ProjectionPhysics.GlueballLadder
