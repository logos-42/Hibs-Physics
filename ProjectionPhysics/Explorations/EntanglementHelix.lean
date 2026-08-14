-- ProjectionPhysics — 双螺旋纠缠的经典骨架：局域隐变量模型的形式化
--
-- 物理背景（leo, 2026-08-14）：
--   流动空间假设下，光子 = 完全随空间流动（SLS2, dτ = 0）——
--   光子的世界线就是空间流动线。
--   纠缠光子对 = 同一流动管内的双螺旋：两股相位差 π（反相），
--   沿公共轴随空间流动，相位由流动携带。
--   本模块回答：这种"经典双螺旋"能证明量子纠缠吗？
--
-- 结论（代数内核，本模块证）：
--   EH1–EH2 ★ CHSH 局域界：任何局域确定性 ±1 模型（双螺旋是其特例）
--     ——结果只依赖本地设置与共享隐变量 λ，λ 分布任意（含"两股相位
--     完全锁死"的最大关联分布）——CHSH 值 |S| ≤ 2 < 2√2（量子界）。
--     ⟹ 双螺旋作为局域轨迹模型无法复现量子关联 = 贝尔不等式的代数核心。
--   EH3–EH4 双螺旋反相结构：B(λ,·) = −A(λ,·)（反相锁定）
--     ⟹ 对齐设置下乘积恒为 −1：完全反关联 E(a,a) = −1（与量子一致）。
--     ——几何锁相给出"纠缠的一半"（完美反关联），
--       但给不出角度连续的 −cos 2Δ 关联（另一半，量子独有）。
--
-- 诚实边界：
--   - 本模块是贝尔定理的经典局域界内容，不是量子力学本身。
--   - 隐变量空间取有限类型（构型空间流动的离散骨架）；
--     连续分布是 Fintype 的极限情形（Python 侧蒙特卡洛验证）。
--   - 量子界 2√2 需要希尔伯特空间形式化（Pauli 矩阵自旋期望），
--     不在本模块——留作后续（Tsirelson 界的 Lean 版）。
--
-- 对应脚本：scripts/verify_entanglement_helix.py（数值 + 蒙特卡洛）
-- 对应 wiki：docs/wiki/theory-entanglement-helix.md

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs

namespace ProjectionPhysics

/-! ### EH1. CHSH 组合项与 ±1 结果代数 -/

/-- CHSH 组合项：S 的单事件贡献
    `A B − A B' + A' B + A' B'`（A,A' 为 Alice 两设置的结果，B,B' 为 Bob）。 -/
def chshTerm (A A' B B' : Int) : Int :=
  A * B - A * B' + A' * B + A' * B'

/-- 核心引理：四个 ±1 结果的 CHSH 组合 ∈ {−2, 2}。 -/
theorem chsh_core (A A' B B' : Int) (hA : A = 1 ∨ A = -1) (hA' : A' = 1 ∨ A' = -1)
    (hB : B = 1 ∨ B = -1) (hB' : B' = 1 ∨ B' = -1) :
    chshTerm A A' B B' = 2 ∨ chshTerm A A' B B' = -2 := by
  rcases hA with hA | hA <;> rcases hA' with hA' | hA' <;>
    rcases hB with hB | hB <;> rcases hB' with hB' | hB' <;>
    simp [chshTerm, hA, hA', hB, hB']

/-! ### EH2. CHSH 期望界：任何局域隐变量分布下 |S| ≤ 2 -/

/-- ★ 贝尔不等式（CHSH）的代数形式：
    隐变量空间 Λ 为有限类型，p : Λ → ℝ 为概率质量（非负、和为 1）；
    每个 λ 给出局域结果 A λ, A' λ, B λ, B' λ ∈ {±1}（结果只依赖本地设置
    与共享 λ——局域性条件）。则 CHSH 期望 |S| ≤ 2。
    双螺旋（B = −A 反相锁定的两股）是满足这些条件的局域模型，
    因此无论 λ 分布多强关联，S 都无法超过 2。 -/
theorem chsh_expectation_bound {Λ : Type} [Fintype Λ] (p : Λ → ℝ)
    (hp_nonneg : ∀ lam, 0 ≤ p lam) (hp_sum : ∑ lam, p lam = 1)
    (A A' B B' : Λ → Int) (hA : ∀ lam, A lam = 1 ∨ A lam = -1)
    (hA' : ∀ lam, A' lam = 1 ∨ A' lam = -1) (hB : ∀ lam, B lam = 1 ∨ B lam = -1)
    (hB' : ∀ lam, B' lam = 1 ∨ B' lam = -1) :
    |∑ lam, p lam * ((chshTerm (A lam) (A' lam) (B lam) (B' lam) : Int) : ℝ)| ≤ 2 := by
  let e : Λ → ℝ := fun lam => ((chshTerm (A lam) (A' lam) (B lam) (B' lam) : Int) : ℝ)
  have he : ∀ lam, e lam = 2 ∨ e lam = -2 := by
    intro lam
    have hc := chsh_core (A lam) (A' lam) (B lam) (B' lam) (hA lam) (hA' lam) (hB lam) (hB' lam)
    rcases hc with hc | hc <;> simp [e, hc]
  have habs : ∀ lam, |e lam| = 2 := by
    intro lam
    rcases he lam with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  change |∑ lam, p lam * e lam| ≤ 2
  calc
    |∑ lam, p lam * e lam| ≤ ∑ lam, |p lam * e lam| := by
      simpa using Finset.abs_sum_le_sum_abs (fun lam => p lam * e lam) Finset.univ
    _ = ∑ lam, |p lam| * |e lam| := by simp [abs_mul]
    _ = ∑ lam, p lam * 2 := by
      apply Finset.sum_congr rfl
      intro lam hlam
      rw [abs_of_nonneg (hp_nonneg lam), habs lam]
    _ = (∑ lam, p lam) * 2 := by rw [← Finset.sum_mul Finset.univ]
    _ = 2 := by rw [hp_sum]; norm_num

/-! ### EH3. 双螺旋：反相锁定的两股流线 -/

-- 双螺旋假设：光子 2 的相位 = 光子 1 的相位 + π（反相）。
-- 任何 ±1 结果函数 A(λ, a)，第二股取 B(λ, b) := −A(λ, b)。
-- ⟹ 对齐设置 (a = b) 下乘积恒为 −1：完全反关联。

/-- 反相股：B = −A ⟹ A·B = −1（±1 结果的符号必然相反）。 -/
theorem helix_strand_anticorrelation (A B : Int) (hA : A = 1 ∨ A = -1) (hB : B = -A) :
    A * B = -1 := by
  rcases hA with hA | hA <;> simp [hB, hA]

/-! ### EH4. 对齐设置的完全反关联 -/

/-- 双螺旋在相同设置下的关联恒为 −1（对任意隐变量分布取平均）：
    E(a,a) = −1。这与量子单态一致——双螺旋精确复现"反关联"这一半。 -/
theorem helix_aligned_correlation {Λ : Type} [Fintype Λ] (p : Λ → ℝ)
    (hp_sum : ∑ lam, p lam = 1) (A B : Λ → Int) (hA : ∀ lam, A lam = 1 ∨ A lam = -1)
    (hB : ∀ lam, B lam = -A lam) :
    ∑ lam, p lam * ((A lam * B lam : Int) : ℝ) = -1 := by
  calc
    ∑ lam, p lam * ((A lam * B lam : Int) : ℝ)
        = ∑ lam, p lam * (-1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro lam hlam
          have h := helix_strand_anticorrelation (A lam) (B lam) (hA lam) (hB lam)
          rw [h]
          norm_num
    _ = -1 := by
      rw [← Finset.sum_mul Finset.univ]
      rw [hp_sum]
      norm_num

/-! ### 结论注释（不证，属数值/量子侧） -/

-- EH2 与 EH3 合读：
--   双螺旋 = 局域模型（EH2 适用）⟹ |S| ≤ 2（经典最优，饱和局域界）；
--   反相锁定（EH3）⟹ E(a,a) = −1（对齐反关联，与量子一致）。
--   量子力学预言 S = 2√2 ≈ 2.828 > 2（Aspect 等实验实测一致）。
--   ⟹ 双螺旋作为"两条独立但相位锁定的经典轨迹"不能证明量子纠缠；
--     纠缠必须活在流场本身（构型空间的非局域流动，玻姆型引导场），
--     双螺旋只是真实空间投影——这是 Python 侧蒙特卡洛的检验内容。

end ProjectionPhysics
