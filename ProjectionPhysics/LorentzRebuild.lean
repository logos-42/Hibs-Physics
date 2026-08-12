-- ProjectionPhysics — LorentzRebuild：新假设下的洛伦兹变换推导（mathlib 版）
--
-- 新假设（leo）：光速 c = 空间本身的等效速度（矢量光速），空间以 c 流动。
--   ⟹ 惯性系 = 随空间流动的参考系（SLS6）
--   ⟹ 观测者相对空间流动的速度 v 是"偏离空间的程度"
--   ⟹ 快度（rapidity）θ 满足 tanh θ = v/c
--   ⟹ 洛伦兹 boost 矩阵 Λ(θ) = [[cosh θ, −sinh θ], [−sinh θ, cosh θ]]
--
-- 本模块用 mathlib（ℝ、矩阵、双曲函数）证明：
--   LR1. boost 保持闵可夫斯基度规 η = diag(−1, 1)（1+1 维）
--   LR2. γ = cosh θ，γ² − γ²β² = 1（β = tanh θ）
--   LR3. boost 复合 = 快度加法（洛伦兹群的结构）
--   LR4. 速度加法定理（快度可加性 ⟹ 速度非线性加法）
--   LR5. 光速不变：β = 1（光子 = 完全随空间流动）时 boost 无定义（分母 1−β² = 0）
--
-- 推导路径（相对论重构的 mathlib 落地）：
--   SLS6 假设（空间流动普适）→ 惯性系定义 → 快度参数化 → boost 矩阵
--   → 度规保持（洛伦兹群）→ 复合律 → 速度加法 → 光速不变

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

noncomputable section
open Matrix

namespace LorentzRebuild

/-! ### LR1. 1+1 维闵可夫斯基时空与 boost -/

/-- 1+1 维时空坐标（t, x）。 -/
abbrev Spacetime : Type := Fin 2 → ℝ

/-- 闵可夫斯基度规 η = diag(−1, 1)（1+1 维）。
    符号约定：时间分量 −1（度规签名 (−,+)）。 -/
def eta : Matrix (Fin 2) (Fin 2) ℝ := !![ -1, 0; 0, 1 ]

/-- 洛伦兹 boost（快度 θ 参数化）：连接随空间流动系与偏离空间 v 的系。
    β = v/c = tanh θ，γ = cosh θ。 -/
def boost (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ Real.cosh θ, -Real.sinh θ; -Real.sinh θ, Real.cosh θ ]

/-- 洛伦兹变换定义：保持闵可夫斯基度规的线性映射（洛伦兹群成员）。 -/
def IsLorentz (Λ : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Λᵀ * eta * Λ = eta

/-- ★ LR1：boost 是洛伦兹变换——保持闵可夫斯基度规。
    这是"偏离空间流动的观测者"与"随空间流动的观测者"之间的
    坐标变换（快度参数化 ⟹ 自动满足度规保持）。 -/
theorem boost_is_lorentz (θ : ℝ) : IsLorentz (boost θ) := by
  unfold IsLorentz boost eta
  -- 展开矩阵乘法（2×2）：对角元 -cosh²+sinh² = -1，非对角 0
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply] <;> ring_nf <;>
    rw [← Real.cosh_sq_sub_sinh_sq θ] <;> ring

/-! ### LR2. γ 与 β 的关系 -/

/-- 速度参数 β = tanh θ（观测者偏离空间流动的程度）。 -/
def beta (θ : ℝ) : ℝ := Real.tanh θ

/-- γ = cosh θ（洛伦兹因子）。 -/
def gamma (θ : ℝ) : ℝ := Real.cosh θ

/-- ★ LR2：γ² − γ²β² = 1（cosh²θ − sinh²θ = 1 的 boost 形式）。
    即 γ = 1/√(1−β²)——标准洛伦兹因子，在新假设下
    β 被解释为"偏离空间流动的速度/光速"。 -/
theorem gamma_sq_minus_beta_sq (θ : ℝ) :
    gamma θ ^ 2 - (gamma θ ^ 2) * (beta θ ^ 2) = 1 := by
  unfold gamma beta
  rw [Real.tanh_eq_sinh_div_cosh]
  have hcosh : Real.cosh θ ≠ 0 := Real.cosh_pos θ |>.ne'
  field_simp [hcosh]
  rw [Real.cosh_sq_sub_sinh_sq]

/-! ### LR3. boost 复合 = 快度加法 -/

/-- ★ LR3：boost 复合 = 快度加法——洛伦兹变换构成群（阿贝尔子群）。
    两次连续的"偏离空间流动"变换等价于一次快度相加的变换。 -/
theorem boost_mul_boost (θ₁ θ₂ : ℝ) :
    boost θ₁ * boost θ₂ = boost (θ₁ + θ₂) := by
  unfold boost
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Real.sinh_add, Real.cosh_add] <;> ring

/-- ★ LR3b：快度加法 = 速度加法定理（相对论速度加法）。
    tanh(θ₁+θ₂) = (tanh θ₁ + tanh θ₂)/(1 + tanh θ₁·tanh θ₂)。
    这是 E = mc² 之外相对论最著名的可检验公式，
    在新假设下它是"空间流动系中速度叠加"的直接推论。 -/
theorem rapidity_add_velocity_add (θ₁ θ₂ : ℝ) :
    Real.tanh (θ₁ + θ₂) =
      (Real.tanh θ₁ + Real.tanh θ₂) / (1 + Real.tanh θ₁ * Real.tanh θ₂) := by
  -- 双侧展开为 sinh/cosh，交叉相乘后化简（速度加法定理）
  have hcosh1 : Real.cosh θ₁ ≠ 0 := Real.cosh_pos θ₁ |>.ne'
  have hcosh2 : Real.cosh θ₂ ≠ 0 := Real.cosh_pos θ₂ |>.ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hcosh1, hcosh2]

/-! ### LR4. 光速不变边界 -/

/-- ★ LR4：光速不变 = 空间流动速度的普适性（SLS6 的 mathlib 版）。
    光子 β = 1（完全随空间流动）时，γ = cosh θ 无有限快度——
    1 − β² = 0 ⟹ 洛伦兹因子发散。任何有限快度 θ 都有 |tanh θ| < 1，
    即任何偏离空间流动的观测者都测到 β < 1（不可能达到空间流动速度）。 -/
theorem finite_rapidity_never_reaches_light (θ : ℝ) :
    Real.tanh θ < 1 := by
  exact Real.tanh_lt_one θ

/-! ### LR5. 显式变换（坐标形式） -/

/-- boost 作用于时空坐标：(t, x) ↦ (γt − γβx, −γβt + γx)。
    这是新假设下"偏离空间流动的观测者看到的时间/空间坐标"。 -/
def boostCoord (θ : ℝ) (p : Spacetime) : Spacetime :=
  ![ Real.cosh θ * p 0 - Real.sinh θ * p 1
   , -Real.sinh θ * p 0 + Real.cosh θ * p 1 ]

/-- ★ LR5a：时间坐标变换 t' = γ(t − βx)（标准洛伦兹时间变换）。 -/
theorem boost_time_component (θ : ℝ) (p : Spacetime) :
    (boostCoord θ p) 0 = Real.cosh θ * p 0 - Real.sinh θ * p 1 := by
  simp [boostCoord]

/-- ★ LR5b：空间坐标变换 x' = γ(x − βt)（标准洛伦兹空间变换）。 -/
theorem boost_space_component (θ : ℝ) (p : Spacetime) :
    (boostCoord θ p) 1 = -Real.sinh θ * p 0 + Real.cosh θ * p 1 := by
  simp [boostCoord]

end LorentzRebuild

end
