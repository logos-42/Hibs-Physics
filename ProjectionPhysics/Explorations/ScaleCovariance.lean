-- ProjectionPhysics — ScaleCovariance：标度类缺口的**账本更正**（SC1–SC8）
--
-- leo（2026-10-01）：「先做第二条」——核「ħ 是单位不是缺口」与「标度类缺口 = 缺第二个标度」。
--
-- ── 要更正的四条原话 ─────────────────────────────────────────────────────
--   1. theory-vibration-statistics.md §251「(iii) 数值层: ħ = 1.0546e−34 J·s —— 需要作用量标度，
--      最终与质量标度同源（与 966× 同一张脸）」
--   2. theory-vibration-closure.md §141「它的**数值层仍是标度**（与 966× 同一张脸）」
--   3. current-status.md §290「（与 966× 同一张脸）」
--   4. log.md 2026-10-01 那行的 (iii)
--   ⟹ 更正：**ħ 的数值与 966× 不是同一张脸。** ħ 的数值是**单位类**（可溶解，像 c）；
--      966×（= M₀/(2m_e)）是**比值类**（真缺口）。
--
-- ── 本模块的形式化内容（全部可证，不含新物理） ─────────────────────────────
--   SC1  尺度协变性：m²(N, M₀) = N·M₀² 在 M₀ ↦ lam·M₀ 下乘 lam²；m(N, M₀) = √N·M₀ 乘 lam
--   SC2  阶梯比值与 M₀ 无关：m²(N₁,M₀)/m²(N₂,M₀) = N₁/N₂
--   SC3  质量比值 = √(N₁/N₂)（与 M₀ 和单位无关）
--   SC4 ★★ **比值是重标定不变量** —— 阶梯比值对 M₀ ↦ lam·M₀ 零敏感
--   SC5 ★★ 重标定不变的输出**读不出标度**（不能区分 M₀ 与 lam·M₀，lam ≠ 1）
--   SC6 ★★★ **主结论**：阶梯比值（= 框架 QCD 层全部输出的形状）**原理上不可能输出 M₀ 的数值**
--        —— 不是「还没算出来」，是「这一形状不算」
--   SC7 ★★ ħ 的数值坐标随单位制改变 ⟹ 它是**坐标不是不变量**（真实例：单位制 1 与 2 给不同数）
--   SC8 ★★ 无量纲量的定义 = 重标定不变量 ⟹ **物理住在无量纲比里**
--
-- ── 账本更正的规则（本轮最有用的一条） ────────────────────────────────────
--   **规则：单个量纲常数的数值 = 单位（可被单位制吸收）；两个同类量之比 = 真缺口。**
--   推论（把仓库的九张脸重排）：
--     · 溶解（单位类）：c 的数值 ✓ 已做（§8 字典轮）、**ħ 的数值**、**M₀ 的数值**、e 的数值
--     · 真缺口（比值类）：**966× = M₀/(2m_e)**、**v/M₀ ≈ 252（层级问题）**、**α**、α_s、
--       G 的无量纲组合 G·m_p²/(ħc) ≈ 5.9e−39
--     · 未定类（需动力学方程，不属标度类）：ρ · α · k · κ · ν 那一组框架内部系数
--   ⟹ **干净陈述：标度类缺口 = 「框架只有一个标度 M₀，缺第二个标度」= 无量纲比 v/M₀。**
--      而 v/M₀ 就是标准的**层级问题**（v ≈ 246 GeV vs M₀ ≈ 1 GeV）——**标准理论也没解决它。**
--
-- ── 死法（写死，防止这条变成万能免责） ────────────────────────────────────
--   若出现一个**无法**归约为单位选择的量纲量（即：框架必须给出一个绝对标度，
--   不能被 M₀ ↦ lam·M₀ 吸收），则本更正的「单位类/比值类」划分**死**。
--   现框架的**全部**可证伪预言都是比值形（√2、√(7/3)、√5、√7、√(28/3)…）⟹ 与之相容。
--   检查点：SC6 说比值输出对标度零敏感；反例只需一个「对 lam 敏感的输出」出现在可证伪预言里。
--
-- ── 诚实边界 ─────────────────────────────────────────────────────────────
--   · 本模块**不含新物理、零新预言**。它是**账本更正**（把缺口的分类改对），不是发现。
--   · SC1–SC4 是初等代数；SC6 是 SC4 的逆否；SC7/SC8 是标准量纲分析的形式化。
--   · **本模块不给出第二个标度**——它只说明「第二个标度」才是真缺口的名字，
--     以及为什么现有形状（比值）永远给不出标度。
--   · M₀ 的**数值**被本模块注销为「单位」，但 M₀ 作为**标定动作**（拟合格点拿到的那个数）
--     仍是记账项：它说明「框架需要一个外部尺度输入」，这一点没变。

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section

namespace ProjectionPhysics.ScaleCovariance

-- ---------------------------------------------------------------------------
-- 定义
-- ---------------------------------------------------------------------------

/-- 阶梯质量平方：m²(N, M₀) = N·M₀²（仓库的胶球谱形式，N = 内部模式数）。 -/
def mSq (N : ℝ) (M0 : ℝ) : ℝ := N * M0 ^ 2

/-- 阶梯质量：m(N, M₀) = √N·M₀。 -/
def mMass (N : ℝ) (M0 : ℝ) : ℝ := Real.sqrt N * M0

/-- **重标定不变量**：对 M₀ ↦ lam·M₀（lam > 0）不变的输出。
    —— 这就是「无量纲量」在标度方向上的定义。 -/
def RescalingInvariant (g : ℝ → ℝ) : Prop := ∀ lam M0 : ℝ, 0 < lam → g (lam * M0) = g M0

-- ---------------------------------------------------------------------------
-- SC1 尺度协变性
-- ---------------------------------------------------------------------------

/-- ★ SC1a：m² 在 M₀ ↦ lam·M₀ 下乘 lam²。 -/
theorem SC1a_mSq_rescale (N M0 lam : ℝ) : mSq N (lam * M0) = lam ^ 2 * mSq N M0 := by
  unfold mSq
  ring

/-- ★ SC1b：m 在 M₀ ↦ lam·M₀ 下乘 lam。 -/
theorem SC1b_mMass_rescale (N M0 lam : ℝ) : mMass N (lam * M0) = lam * mMass N M0 := by
  unfold mMass
  ring

-- ---------------------------------------------------------------------------
-- SC2 / SC3 比值与标度无关
-- ---------------------------------------------------------------------------

/-- ★★ SC2：阶梯质量平方的比值 = 模式数之比（**与 M₀ 无关**）。 -/
theorem SC2_mSq_ratio_scale_free (N1 N2 M0 : ℝ) (hN2 : N2 ≠ 0) (hM0 : M0 ≠ 0) :
    mSq N1 M0 / mSq N2 M0 = N1 / N2 := by
  unfold mSq
  have h2 : (M0 : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hM0
  have hden : N2 * M0 ^ 2 ≠ 0 := mul_ne_zero hN2 h2
  rw [div_eq_div_iff hden (by exact hN2)]
  ring

/-- ★★ SC3：质量比 = √(N₁/N₂)（与 M₀ 无关，也与单位制无关）。 -/
theorem SC3_mMass_ratio_scale_free (N1 N2 M0 : ℝ) (hN2 : 0 < N2) (hM0 : M0 ≠ 0) :
    mMass N1 M0 / mMass N2 M0 = Real.sqrt N1 / Real.sqrt N2 := by
  unfold mMass
  have hs2 : Real.sqrt N2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN2)
  rw [div_eq_div_iff (mul_ne_zero hs2 hM0) hs2]
  ring

-- ---------------------------------------------------------------------------
-- SC4 ★★ 比值是重标定不变量
-- ---------------------------------------------------------------------------

/-- ★★ SC4：**阶梯比值对 M₀ 的重标定零敏感**（重标定不变量）。
    这是「框架 QCD 层输出」的形状。 -/
theorem SC4_ratio_invariant (N1 N2 : ℝ) (hN2 : N2 ≠ 0) :
    RescalingInvariant (fun M0 => mSq N1 M0 / mSq N2 M0) := by
  intro lam M0 hlam
  by_cases hM0 : M0 = 0
  · subst hM0
    simp [mSq]
  · simp only [mSq]
    rw [mul_pow]
    have hlam2 : (lam : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hlam)
    have hM02 : (M0 : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hM0
    have hden : N2 * (lam ^ 2 * M0 ^ 2) ≠ 0 := mul_ne_zero hN2 (mul_ne_zero hlam2 hM02)
    have hden' : N2 * M0 ^ 2 ≠ 0 := mul_ne_zero hN2 hM02
    rw [div_eq_div_iff hden hden']
    ring

-- ---------------------------------------------------------------------------
-- SC5 / SC6 ★★★ 主结论：结构层原理上给不出标度
-- ---------------------------------------------------------------------------

/-- ★★ SC5：**重标定不变的输出读不出标度** —— 只要 lam ≠ 1，
    「g 读出了 M₀」这个说法要求 g 在 M₀ 与 lam·M₀ 上取不同值，与不变性矛盾。 -/
theorem SC5_invariant_cannot_read_scale (g : ℝ → ℝ) (hinv : RescalingInvariant g)
    (M0 lam : ℝ) (hlam : 0 < lam) : ¬ (g (lam * M0) ≠ g M0) := by
  intro h
  exact h (hinv lam M0 hlam)

/-- ★★★ SC6（主结论）：**框架 QCD 层的输出形状 = 阶梯比值，它原理上不可能输出 M₀ 的数值。**
    不是「还没算出来」，是「这一形状不算」：比值输出对 M₀ ↦ lam·M₀ 零敏感。 -/
theorem SC6_ladder_cannot_output_scale (N1 N2 : ℝ) (hN2 : N2 ≠ 0)
    (M0 lam : ℝ) (hlam : 0 < lam) :
    ¬ (mSq N1 (lam * M0) / mSq N2 (lam * M0) ≠ mSq N1 M0 / mSq N2 M0) :=
  SC5_invariant_cannot_read_scale _ (SC4_ratio_invariant N1 N2 hN2) M0 lam hlam

-- ---------------------------------------------------------------------------
-- SC7 ★★ ħ 的数值是坐标不是不变量
-- ---------------------------------------------------------------------------

/-- ħ 在「作用量单位 = u」的单位制下的**坐标**（数值）。 -/
def hbarCoord (hbar0 u : ℝ) : ℝ := hbar0 / u

/-- ★★ SC7a：**ħ 的数值随单位制改变** ⟹ 它是坐标，不是不变量。
    （诚实：hbar0 是符号，实参 1.054571817e−34 J·s 是 SI 制下的坐标值。） -/
theorem SC7a_hbar_coord_changes (hbar0 : ℝ) (h : hbar0 ≠ 0) :
    ∃ u1 u2 : ℝ, 0 < u1 ∧ 0 < u2 ∧ hbarCoord hbar0 u1 ≠ hbarCoord hbar0 u2 := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  unfold hbarCoord
  intro hc
  have hc' : hbar0 / 1 = hbar0 / 2 := hc
  simp only [div_one] at hc'
  have hz : hbar0 = 0 := by linarith
  exact h hz

/-- ★★ SC7b：重标定不变量**不随单位制变**（α 那一类）。 -/
theorem SC7b_invariant_does_not_change (alpha : ℝ) :
    ∀ u1 u2 : ℝ, 0 < u1 → 0 < u2 → (fun _ : ℝ => alpha) u1 = (fun _ : ℝ => alpha) u2 := by
  intro u1 u2 h1 h2
  rfl

-- ---------------------------------------------------------------------------
-- SC8 ★★ 物理住在无量纲比里
-- ---------------------------------------------------------------------------

/-- ★★ SC8：**无量纲量的定义就是重标定不变量** —— 于是「物理住在无量纲比里」
    与「比值读不出标度」（SC5/SC6）合起来 ⟹ 结构层（只给比值）原理上不含标度信息。 -/
theorem SC8_dimensionless_iff_invariant (g : ℝ → ℝ) :
    RescalingInvariant g ↔ ∀ lam M0 : ℝ, 0 < lam → g (lam * M0) = g M0 :=
  Iff.rfl

end ProjectionPhysics.ScaleCovariance
