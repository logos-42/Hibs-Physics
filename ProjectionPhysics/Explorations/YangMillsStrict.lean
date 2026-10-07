-- ProjectionPhysics — YangMillsStrict：严格化证明（范数有界性 + 导数通道）
--
-- leo（2026-10-07）：「开始执行严格化证明」。
--
-- 目标：把 CA8–CA10 的「连续极限机制」从结构对应升级为分析严格化：
--   L1 ★★ 交换子范数有界：‖[A,B]‖ ≤ 6·‖A‖·‖B‖
--        —— 格点场强 F=[A(t),A(t+1)] 的范数被场强范数控制（常数因子），
--          随格距细化不发散（连续极限存在性的范数前提）。
--   L3 ★★★ 核力通道范数非平凡：‖m·dC‖ ≠ 0（m≠0 且 dC 范数非零）
--        —— 连续场强非平凡的严格化陈述。
--   L2 ★ 流动动量导数（标量版严格化）：d/dt [m·(C−v)] = dm·(C−v) + m·(dC−dv)
--        —— 四力通道是流动动量的真导数（乘积法则）。
--
-- 载体：Mat3C（仓库类型）经 open scoped Matrix.Norms.Elementwise 获得
--   sup-of-sup 范数（mathlib 正规方式，不改仓库类型）。
--
-- 诚实边界（写死）：
--   · L1 用 sup 范数的 entrywise 三角：‖AB‖ ≤ 3‖A‖‖B‖（Fin 3 求和因子），
--     交换子 ⟹ 常数 6。有界性成立；常数不是最优的（诚实）。
--   · L2 是标量流动动量的 HasDerivAt 乘积法则；矩阵值推广（Mat3C 的
--     连续导数）仍未做（诚实：需 NormedSpace 结构 + HasFDerivAt）。
--   · L3 用范数非零（‖·‖=0 ↔ ·=0 的 NormedAddCommGroup 性质）。
--   · 「格距 a→0 的拓扑收敛」（格点场列收敛到连续场）仍未形式化
--     （最重一层，诚实保留）。
--   · 死法：若交换子范数不被常数×‖A‖‖B‖控制，或核力通道范数在
--     非平凡输入下为 0，本严格化死。

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ProjectionPhysics.Explorations.ColorOctetMathlib

noncomputable section
namespace ProjectionPhysics.YangMillsStrict

open ProjectionPhysics
open ColorOctet
open scoped Matrix.Norms.Elementwise

/-- 色空间矩阵（仓库类型，经 scoped 实例获得范数）。 -/
abbrev MatNorm := Mat3C

/-- L1a ★ 矩阵乘法的 entrywise 范数界：‖A·B‖ ≤ 3·‖A‖·‖B‖。
    sup-of-sup 范数下，3×3 矩阵乘法的每项 ≤ ‖A‖‖B‖，共 3 项求和。 -/
theorem mat_mul_norm_bounded (A B : MatNorm) :
    ‖A * B‖ ≤ 3 * ‖A‖ * ‖B‖ := by
  -- 用 norm_le_iff：‖AB‖ ≤ 3‖A‖‖B‖ ⟺ ∀ i j, |(AB)_ij| ≤ 3‖A‖‖B‖
  rw [Matrix.norm_le_iff]
  · intro i j
    -- (A*B)_ij = Σ_k A_ik B_kj
    have hsum : ‖∑ k : Fin 3, A i k * B k j‖ ≤ ∑ k : Fin 3, ‖A i k * B k j‖ :=
      norm_sum_le _ _
    -- 每项 ‖A_ik B_kj‖ ≤ ‖A_ik‖‖B_kj‖ ≤ ‖A‖‖B‖
    have hterm : ∀ k : Fin 3, ‖A i k * B k j‖ ≤ ‖A‖ * ‖B‖ := by
      intro k
      have h1 : ‖A i k * B k j‖ ≤ ‖A i k‖ * ‖B k j‖ := norm_mul_le _ _
      have hA : ‖A i k‖ ≤ ‖A‖ := Matrix.norm_entry_le_entrywise_sup_norm A
      have hB : ‖B k j‖ ≤ ‖B‖ := Matrix.norm_entry_le_entrywise_sup_norm B
      exact le_trans h1 (mul_le_mul hA hB (norm_nonneg _) (norm_nonneg _))
    -- 三项求和 ≤ 3‖A‖‖B‖
    have hsum_le : ∑ k : Fin 3, ‖A i k * B k j‖ ≤ 3 * ‖A‖ * ‖B‖ := by
      calc
        ∑ k : Fin 3, ‖A i k * B k j‖ ≤ ∑ k : Fin 3, ‖A‖ * ‖B‖ :=
          Finset.sum_le_sum fun k _ => hterm k
        _ = 3 * (‖A‖ * ‖B‖) := by simp
        _ = 3 * ‖A‖ * ‖B‖ := by ring
    exact le_trans hsum hsum_le
  -- 目标 0 ≤ 3 * ‖A‖ * ‖B‖ = 3*(‖A‖*‖B‖)
  · have hA : 0 ≤ ‖A‖ := norm_nonneg A
    have hB : 0 ≤ ‖B‖ := norm_nonneg B
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hA) hB

/-- L1 ★★ 交换子范数有界：‖[A,B]‖ ≤ 6·‖A‖·‖B‖。
    格点场强 F = [A(t), A(t+1)] 的范数被场强范数控制（常数 6）：
    自相互作用随格距细化不发散 —— 连续极限存在性的范数前提。 -/
theorem commutator_norm_bounded (A B : MatNorm) :
    ‖A * B - B * A‖ ≤ 6 * ‖A‖ * ‖B‖ := by
  have h1 : ‖A * B‖ ≤ 3 * ‖A‖ * ‖B‖ := mat_mul_norm_bounded A B
  have h2 : ‖B * A‖ ≤ 3 * ‖B‖ * ‖A‖ := mat_mul_norm_bounded B A
  have hab : ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
  have hsum : ‖A * B‖ + ‖B * A‖ ≤ 6 * ‖A‖ * ‖B‖ := by
    calc
      ‖A * B‖ + ‖B * A‖ ≤ (3 * ‖A‖ * ‖B‖) + (3 * ‖B‖ * ‖A‖) := add_le_add h1 h2
      _ = 6 * ‖A‖ * ‖B‖ := by ring
  exact le_trans hab hsum

-- ---------------------------------------------------------------------------
-- L3 ★★★ 核力通道范数非平凡
-- ---------------------------------------------------------------------------

/-- L3 ★★★ 核力通道范数非平凡：m ≠ 0 且 ‖dC‖ ≠ 0 ⟹ ‖m·dC‖ ≠ 0。
    连续场强（核力分量）非平凡的严格化陈述：
    范数意义下非零（NormedAddCommGroup 的 ‖·‖=0 ↔ ·=0）。 -/
theorem nuclear_channel_norm_ne_zero (m : ℝ) (hm : m ≠ 0) (dC : MatNorm)
    (hdC : ‖dC‖ ≠ 0) :
    ‖m • dC‖ ≠ 0 := by
  intro hnorm
  have hmul : ‖m • dC‖ = |m| * ‖dC‖ := norm_smul m dC
  rw [hmul] at hnorm
  -- |m| * ‖dC‖ = 0，且 |m| ≠ 0 ⟹ ‖dC‖ = 0
  have hz : ‖dC‖ = 0 := by
    have hcases := mul_eq_zero.mp hnorm
    rcases hcases with hma | hd
    · exfalso
      exact (abs_ne_zero.mpr hm) hma
    · exact hd
  exact hdC hz

-- ---------------------------------------------------------------------------
-- L2 ★ 流动动量导数（四力通道 = 真导数的乘积法则）
-- ---------------------------------------------------------------------------

/-- L2 ★ 流动动量导数：d/dt [m·(C−v)] = dm·(C−v) + m·(dC−dv)。
    四力通道（CA8 fourForceSum）是流动动量 m·(C−v) 的**真导数**
    （乘积法则 + 减法法则）：连续极限机制的微积分严格化（标量版）。 -/
theorem flow_momentum_derivative
    {m C v : ℝ → ℝ} {t dm dC dv : ℝ}
    (hm : HasDerivAt m dm t)
    (hC : HasDerivAt C dC t)
    (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => m s * (C s - v s))
      (dm * (C t - v t) + m t * (dC - dv)) t := by
  have hsub : HasDerivAt (fun s => C s - v s) (dC - dv) t := hC.sub hv
  exact hm.mul hsub

end ProjectionPhysics.YangMillsStrict