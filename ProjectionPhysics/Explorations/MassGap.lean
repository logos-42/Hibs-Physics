-- ProjectionPhysics — MassGap：质量间隙的种子定理（条数离散 ⟹ 下界存在）
--
-- leo（2026-10-07）：「从有质量的电子变成光子，这件事本身就已经能说明存在一个下界。
--   质量可以被加速电荷产生的反引力场激发，然后消灭自己的旋度、散度，于是变成了光子。」
--  + 「有一些连续的流，我们可以用离散的方式来表示。」
--
-- 论证内核（本模块形式化）：
--   质量由**整数条数**决定（QFT3 锚定范数 / GQF3 m=√N·M₀ / 胶球
--   pureGlueMassSquared = 整数条数能量，N ∈ ℕ）。
--   于是质量谱**天生离散**：
--     · N = 0 ⟹ m² = 0         （光子：完全随流，无锚定）
--     · N ≥ 1 ⟹ m² ≥ M₀²       （最轻激发 = 单条，质量 = M₀）
--   ⟹ 区间 (0, M₀) 是空的 —— **质量间隙**：没有任意小但非零的质量。
--   电子的质量（N ≥ 1）→ 光子的质量（N = 0）是**整数跳变**，不能连续穿过
--   间隙 —— 这本身就是「有质量 ⟹ 有下界」的证明。
--
-- 本模块是**代数种子**（诚实边界）：
--   · 它证明「若质量由整数条数决定，则间隙存在」—— 严格、零 sorry；
--   · 它**不**证明连续 4 维 QFT 的完整质量间隙（路径积分 / 重整化 /
--     连续时空的构造仍是开放问题，仓库明确未支持连续 ∇）；
--   · 条数 → 质量的归一化（M₀）仍是标定输入（第二输入缺口，未变）。
--
-- 死法：若存在一个物理态其质量平方 ∈ (0, M₀²)（即条数不是整数，或
--   质量不由条数决定），本种子死。
--
-- 产物：本文件 + 聚合根 import；零 sorry 零 warning。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.MassCancellation
import ProjectionPhysics.Explorations.GlueballBridge

namespace ProjectionPhysics.MassGap

open ProjectionPhysics

-- ---------------------------------------------------------------------------
-- MG1 ★ 质量 = 条数的离散化
--   m²(N, M₀) = N·M₀²，N ∈ ℕ 是条数（整数），M₀ 是单条质量（标定）。
--   连续流（空间场 C）的激发用整数条数表示 —— 「连续流用离散表示」。
-- ---------------------------------------------------------------------------

/-- 条数质量平方：m² = N·M₀²。N 是整数条数，M₀ 是单条质量（标定输入）。 -/
def strandMassSq (N : ℕ) (M₀ : ℝ) : ℝ :=
  (N : ℝ) * M₀ ^ 2

/-- ★ MG1a：非零条数 ⟹ 质量平方严格正 —— 任何激发都有正质量（零 sorry）。
    N ≥ 1 且 M₀ > 0 ⟹ N·M₀² > 0。 -/
theorem strand_mass_sq_pos_of_nontrivial {N : ℕ} {M₀ : ℝ}
    (hN : 1 ≤ N) (hM₀ : 0 < M₀) :
    0 < strandMassSq N M₀ := by
  unfold strandMassSq
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt hN))
  positivity

/-- ★ MG1b：零条数 ⟹ 质量平方为零 —— 光子（完全随流，无锚定）。
    N = 0 ⟹ 0·M₀² = 0。 -/
theorem strand_mass_sq_zero_of_empty {M₀ : ℝ} :
    strandMassSq 0 M₀ = 0 := by
  unfold strandMassSq
  ring

-- ---------------------------------------------------------------------------
-- MG2 ★★ 质量间隙：最轻激发 ≥ 单条质量
--   任意非零质量态（N ≥ 1）的质量平方 ≥ 单条质量平方（N=1）——
--   区间 (0, M₀²) 里没有质量平方。这是「质量间隙」的代数种子。
-- ---------------------------------------------------------------------------

/-- ★★ MG2：单条是最轻激发 —— N ≥ 1 时 m²(N) ≥ m²(1) = M₀²。
    N ≥ 1 ⟹ N·M₀² ≥ 1·M₀²。 -/
theorem mass_gap_lower_bound {N : ℕ} {M₀ : ℝ} (hN : 1 ≤ N) :
    strandMassSq 1 M₀ ≤ strandMassSq N M₀ := by
  unfold strandMassSq
  have hNle : ((1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  exact mul_le_mul_of_nonneg_right hNle (sq_nonneg M₀)

/-- ★★ MG2b：间隙的「空区间」陈述 —— 0 与 M₀² 之间没有质量平方。
    任意质量平方要么是 0（光子），要么 ≥ M₀²（激发）。
    ∀ M², M² = 0 ∨ M₀² ≤ M² 若 M² = 某个条数的质量平方。 -/
theorem mass_gap_no_intermediate {N : ℕ} {M₀ : ℝ} :
    strandMassSq N M₀ = 0 ∨ strandMassSq 1 M₀ ≤ strandMassSq N M₀ := by
  by_cases hN : 1 ≤ N
  · right
    exact mass_gap_lower_bound hN
  · left
    have hN0 : N = 0 := by
      by_contra h
      have : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
      exact hN this
    subst N
    exact strand_mass_sq_zero_of_empty

-- ---------------------------------------------------------------------------
-- MG3 ★★★ 电子 → 光子是整数跳变（用户论证的形式化）
--   电子有质量（条数 N ≥ 1），光子无质量（条数 0）。
--   跃迁 N ≥ 1 → 0 是**整数跳变**：不可能连续穿过间隙 (0, M₀)，
--   ——因为条数是整数，中间不存在「分数条数」的质量态。
--   这是「从有质量电子变成光子本身就说明存在下界」的严格形式。
-- ---------------------------------------------------------------------------

/-- ★★★ MG3：质量函数在条数上的像是一个**离散集合** {N·M₀² : N ∈ ℕ}。
    任何两个不同条数的质量平方之间有空隙 —— 特别地，
    0（光子）与 M₀²（最轻激发）之间没有其他质量平方。
    这是「电子 ⟹ 光子 的跃迁本身证明间隙存在」的代数内核。 -/
theorem electron_to_photon_is_discrete_jump {M₀ : ℝ} (hM₀ : 0 < M₀) :
    -- 电子（N ≥ 1）的质量平方 ≠ 光子（N=0）的质量平方，且中间无值
    ∀ {N : ℕ}, 1 ≤ N →
      strandMassSq N M₀ ≠ 0 ∧
      strandMassSq 0 M₀ = 0 ∧
      strandMassSq 1 M₀ ≤ strandMassSq N M₀ := by
  intro N hN
  constructor
  · intro h
    have hpos : 0 < strandMassSq N M₀ := strand_mass_sq_pos_of_nontrivial hN hM₀
    linarith
  · constructor
    · exact strand_mass_sq_zero_of_empty
    · exact mass_gap_lower_bound hN

-- ---------------------------------------------------------------------------
-- MG4 ★ 与仓库胶球质量的对接：pureGlueMassSquared 已经是整数条数能量
--   胶球质量平方 = configurationFieldEnergy（Nat，整数）⟹ 同样离散 ⟹
--   同样的间隙论证直接适用（N = 条数能量，0 或 ≥ 1）。
-- ---------------------------------------------------------------------------

/-- ★ MG4：胶球的条数能量是整数 —— 质量平方离散性的仓库内见证。
    胶球质量平方（pureGlueMassSquared，Int）要么 0（无激发条数）要么 ≥ 1
    （至少一条激发）—— 整数离散，间隙的胶球体现。 -/
theorem glueball_mass_gap_present (g : ProjectionPhysics.Glueball) :
    ProjectionPhysics.pureGlueMassSquared g = 0 ∨
    1 ≤ ProjectionPhysics.pureGlueMassSquared g := by
  unfold ProjectionPhysics.pureGlueMassSquared
  by_cases h : configurationFieldEnergy g.configuration.modes = 0
  · left
    simp [h]
  · right
    have hpos : 0 < configurationFieldEnergy g.configuration.modes := Nat.pos_of_ne_zero h
    have hge : 1 ≤ configurationFieldEnergy g.configuration.modes := Nat.succ_le_of_lt hpos
    change (1 : ℤ) ≤ (configurationFieldEnergy g.configuration.modes : ℤ)
    exact_mod_cast hge

end ProjectionPhysics.MassGap