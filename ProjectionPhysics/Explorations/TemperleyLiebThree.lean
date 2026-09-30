-- ProjectionPhysics — TemperleyLiebThree：TL₃(δ) 的中心与"态依赖量子数"的存在性
--
-- leo（2026-09-29）：按三股试的结果（BraidThree.lean BT1–BT5）是**一条否定**：
--   2 维既约 Burau 里全扭转 (σ₁σ₂)³ = t³·I 是**纯量** ⟹ 从它读出的相位对所有辫词都一样
--   ⟹ 该表示不含态依赖的量子数，且自旋最多 3/2（给不出 J = 2, 3）。
-- 用户指定下一步：上 TL/Jones 表示（level k ≥ 4 才有 j = 2）。本模块给出 TL₃ 侧的结构事实。
--
-- 内容（全部在 TL₃(δ) 的 5 维左正则表示里，基 {1, e₁, e₂, e₁e₂, e₂e₁}，系数环 ℤ[δ]）：
--   TL1/TL2  定义关系 e₁² = δe₁、e₂² = δe₂
--   TL3/TL4  e₁e₂e₁ = e₁、e₂e₁e₂ = e₂（TL 的"圈"关系）
--   ZC1/ZC2  **显式中心元** Z（与 L₁、L₂ 都交换）
--   ZNS      ★ Z **不是纯量** ⟹ 中心 ⊋ 标量
--            ⟹ 对照 BT2/BT3：2 维既约 Burau 的中心元是纯量（无态依赖）；
--              TL₃ 的中心维数是 2（数值：解 L_z = R_z 得 rank 3）⟹ **态依赖的离散标签存在**
--            ⟹ BT3 那条堵点在 TL 里被解除（这是本步的正结果）。
--
-- 数值侧（scripts/verify_tl3_jones.py，产物 artifacts/glueball_ring_twist/tl3_jones.json）：
--   结合律 125 组全过；braid 关系在骨架形式 σᵢ = A + A⁻¹eᵢ（δ = −(A²+A⁻²)）下成立；
--   Δ = (σ₁σ₂)³ **中心但非纯量**，特征值 A^{±6}（多重度 1 与 4 ⟹ 与 TL₃ ≅ M₁ ⊕ M₂ 一致）；
--   两个标量的相位 = 3/(k+2) 与 1−3/(k+2)（只在 k = 1, 4 上退化）。
--   诚实边界：这两个值**不等于** SU(2)_k 主权重的 j(j+1)/(k+2) ⟹ 还不能直接读成 J。

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

noncomputable section
namespace ProjectionPhysics.TL3

open Matrix

/-- TL 参数 δ，取成多项式环 ℤ[δ] 的变量。 -/
abbrev delta : Polynomial ℤ := Polynomial.X

/-- 左乘 e₁ 在基 {1, e₁, e₂, e₁e₂, e₂e₁} 下的 5×5 矩阵。 -/
def L1 : Matrix (Fin 5) (Fin 5) (Polynomial ℤ) :=
  !![0, 0, 0, 0, 0;
     1, delta, 0, 0, 1;
     0, 0, 0, 0, 0;
     0, 0, 1, delta, 0;
     0, 0, 0, 0, 0]

/-- 左乘 e₂ 在基 {1, e₁, e₂, e₁e₂, e₂e₁} 下的 5×5 矩阵。 -/
def L2 : Matrix (Fin 5) (Fin 5) (Polynomial ℤ) :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     1, 0, delta, 1, 0;
     0, 0, 0, 0, 0;
     0, 1, 0, 0, delta]

/-- 显式中心元 Z（数值解 L_z = R_z 的核里取常数项为 0 的那个方向）。 -/
def Z : Matrix (Fin 5) (Fin 5) (Polynomial ℤ) :=
  !![0, 0, 0, 0, 0;
     -delta, 1 - delta ^ 2, 0, 0, 0;
     -delta, 0, 1 - delta ^ 2, 0, 0;
     1, 0, 0, 1 - delta ^ 2, 0;
     1, 0, 0, 0, 1 - delta ^ 2]

/-- TL₁：e₁² = δ·e₁。 -/
theorem TL1_e1_sq : L1 * L1 = delta • L1 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [L1, Matrix.mul_apply, Fin.sum_univ_succ]

/-- TL₂：e₂² = δ·e₂。 -/
theorem TL2_e2_sq : L2 * L2 = delta • L2 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [L2, Matrix.mul_apply, Fin.sum_univ_succ]

/-- TL₃：e₁e₂e₁ = e₁。 -/
theorem TL3_e1_e2_e1 : L1 * L2 * L1 = L1 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [L1, L2, Matrix.mul_apply, Fin.sum_univ_succ]

/-- TL₄：e₂e₁e₂ = e₂。 -/
theorem TL4_e2_e1_e2 : L2 * L1 * L2 = L2 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [L1, L2, Matrix.mul_apply, Fin.sum_univ_succ]

/-- ZC₁：Z 与 e₁ 交换。 -/
theorem ZC1_comm_L1 : Z * L1 = L1 * Z := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Z, L1, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- ZC₂：Z 与 e₂ 交换。 -/
theorem ZC2_comm_L2 : Z * L2 = L2 * Z := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Z, L2, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- ZNS：★ Z **不是纯量矩阵**。
    ⟹ 中心的维数 ≥ 2（1 与 Z 线性无关）⟹ 存在非纯量中心元
    ⟹ 它与 2 维既约 Burau 的局面（BT2/BT3：中心元 = t³·I 是纯量）形成对照：
      "态依赖的离散标签"在 TL₃ 里**存在**。 -/
theorem ZNS_Z_not_scalar : ¬ ∃ c : Polynomial ℤ, Z = Matrix.scalar (Fin 5) c := by
  rintro ⟨c, hc⟩
  have h30 : Z 3 0 = (Matrix.scalar (Fin 5) c) 3 0 := by rw [hc]
  simp [Z, Matrix.scalar_apply] at h30

end ProjectionPhysics.TL3
