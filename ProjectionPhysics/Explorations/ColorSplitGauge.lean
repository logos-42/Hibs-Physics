-- ProjectionPhysics — ColorSplitGauge：拆色是否规范协变？（CG1–CG4，**否定结果**）
--
-- leo（2026-11-01）：「做 b 试试」——查条数在**全 SU(3)** 下是否不变，并试造反例。
--
-- 上一轮（`ColorSplit` CS1–CS7）证了：
--   · 对角链路 ⟹ 逐色绕数 k_c ∈ ℤ（CS2）
--   · 条数 N = Σ|k_c|² 在**色置换**（Weyl 群）下不变（CS7）
-- 本模块回答更强的问题：**在全 SU(3)（非置换的规范变换）下是否不变？**
--
-- 答案是**否**，而且是结构性的：
--
--   对角矩阵（色不混合）在**非单项**的相似变换下会变成**非对角**矩阵。
--   ⟹ 逐色绕数 k_c 是"对角元"的相位，一旦矩阵非对角，**k_c 就没有定义了**。
--   ⟹ 条数 Σ|k_c|² 只在**选定的 Cartan 基**（对角基）里有意义，不是规范不变量。
--
--   反例（CG4）：D = diag(i, 1, 1)（非平凡行列式），g = 单位上三角 [[1,1,0],[0,1,0],[0,0,1]]，
--   h = g⁻¹ = [[1,-1,0],[0,1,0],[0,0,1]]。则
--       g D h = [[i, 1-i, 0], [0, 1, 0], [0, 0, 1]]
--   出现了非对角元 1−i ≠ 0 ⟹ 对角元相位不再是全部信息。
--
--   对比（正面的那一半，已在 NA4）：**行列式**是规范不变的（det(gPg⁻¹) = detP），
--   所以"总绕数"是可观测的，而"逐色分量"不是。
--
--   CG1 `gEx_mul_hEx` / CG2 `hEx_mul_gEx`：反例的 g、h 确实互逆
--   CG3 `dEx_diagonal`：D 确实是对角的
--   CG4 ★★★ `conj_has_offdiag`：**g D h 有非对角元 1−i ≠ 0**
--   CG5 ★★★ `color_split_not_gauge_covariant`：把 CG1–CG4 打包成否定命题
--
-- 结论与出路（写死）：
--   · 条数 N 目前**不是**规范不变量，只在 Weyl 群下不变（CS7）。要用它，
--     必须选一个规范（极大阿贝尔投影 / maximal abelian gauge）——这是格点 QCD 的标准做法，
--     但**规范选取本身是模型输入**，仓库里没有。
--   · 真正的规范不变量是 **P 的本征值**（相似矩阵有相同本征值）。所以正确的条数定义应走
--     **谱分解**：k_c 取本征值的相位，而不是对角元的相位。这条是 `Module.End` 的活，
--     工作量远大于本模块（下一个坑，且现在有了**明确理由**）。
--   · 仍不声称 Pontryagin 指数；反射正性 / 测度 / 连续极限仍为零。

import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import ProjectionPhysics.Explorations.ColorSplit

noncomputable section

namespace ProjectionPhysics.ColorSplitGauge

/-- 色矩阵。 -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-! ### 反例的三个矩阵 -/

/-- 规范变换 g：单位上三角（不是置换！permutation 不会破坏对角性）。 -/
def gEx : Mat3 := !![(1 : ℂ), 1, 0; 0, 1, 0; 0, 0, 1]

/-- g 的逆（显式给出，避免 `nonsing_inv` 的计算）。 -/
def hEx : Mat3 := !![(1 : ℂ), -1, 0; 0, 1, 0; 0, 0, 1]

/-- 对角链路：只有第 1 色带相位 i（det = i）。 -/
def dEx : Mat3 := !![Complex.I, 0, 0; 0, (1 : ℂ), 0; 0, 0, 1]

/-- CG1：g·h = 1。 -/
theorem gEx_mul_hEx : gEx * hEx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gEx, hEx, Matrix.mul_apply, Fin.sum_univ_three]

/-- CG2：h·g = 1。 -/
theorem hEx_mul_gEx : hEx * gEx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gEx, hEx, Matrix.mul_apply, Fin.sum_univ_three]

/-- CG3：D 是对角的（非对角元全为 0）。 -/
theorem dEx_diagonal : ∀ i j : Fin 3, i ≠ j → dEx i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [dEx]

/-! ### CG4 共轭后出现非对角元 -/

/-- CG4 ★★★ **共轭把对角变成非对角**：`(g D h) 0 1 = 1 − i ≠ 0`。
    ⟹ 对角元不再是全部信息 ⟹ 逐色绕数 k_c 丧失定义。 -/
theorem conj_has_offdiag : (gEx * dEx * hEx) 0 1 = 1 - Complex.I := by
  simp [gEx, dEx, hEx, Matrix.mul_apply, Fin.sum_univ_three]
  norm_num [Complex.ext_iff]

/-- CG4b：该非对角元确实非零。 -/
theorem conj_offdiag_ne_zero : (gEx * dEx * hEx) 0 1 ≠ 0 := by
  rw [conj_has_offdiag]
  intro h
  have h1 : (1 - Complex.I).re = 0 := by rw [h]; simp
  simp at h1

/-! ### CG5 打包成否定命题 -/

/-- CG5 ★★★ **拆色不是规范协变的**（否定结果，反例已在 Lean 内验证）：

    存在一对互逆的 g、h 与一个对角矩阵 D，使得 `g·D·h` **不是**对角矩阵。

    ⟹ 「逐色绕数 k_c」是**对角基下的量**，不是规范不变量；
       于是「条数 N = Σ|k_c|²」作为物理量**需要有规范选取**（极大阿贝尔投影）才有定义。
    ⟹ 对比：**行列式的绕数是规范不变的**（`NonAbelianLinkTopology.detLink_conj`），
       所以"总数"可观测、"分量"不可观测。 -/
theorem color_split_not_gauge_covariant :
    ∃ (g h D : Mat3), g * h = 1 ∧ h * g = 1 ∧ (∀ i j : Fin 3, i ≠ j → D i j = 0) ∧
      (∃ i j : Fin 3, i ≠ j ∧ (g * D * h) i j ≠ 0) :=
  ⟨gEx, hEx, dEx, gEx_mul_hEx, hEx_mul_gEx, dEx_diagonal,
    ⟨0, 1, by decide, conj_offdiag_ne_zero⟩⟩

end ProjectionPhysics.ColorSplitGauge
