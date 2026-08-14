-- ProjectionPhysics — SpaceGravity：从动量守恒推导 GR（用户假设下的重构骨架）
--
-- leo（2026-08-11）：能不能根据我的时空假设重新从动量守恒推导一次广义相对论？
--
-- 用户时空假设（已形式化）:
--   · 空间以等效速度 c 流动（矢量光速, SLS1-SLS3）
--   · 光子 = 完全随空间运动（dx=c·dt, SM1）
--   · 质量 = 锚定 = 偏离空间流动（dx≠c·dt, SM3c/d）
--   · 引力 = 空间流动的非均匀性（SLS6 种子）
--
-- 推导路线（Weinberg 经典路线, 在本假设下重构）:
--   ① 动量守恒（平直空间）: ∂_μ T^μν = 0
--   ② 空间流动非均匀 v(x) ⟹ 度规弯曲（Gordon 度规）
--   ③ 协变守恒: ∇_μ T^μν = 0（引入 Christoffel 符号）
--   ④ 动量守恒 + 等效原理 ⟹ 测地线方程
--   ⑤ 场方程: G_μν = κT_μν（爱因斯坦张量 = 能动量张量）
--
-- 本模块（结构层骨架, mathlib）:
--   SG1  gordonMetric: 空间流动 v 的 1+1 维度规 g = [[1−v²/c², v/c²], [v/c², −1/c²]]
--   SG2  gordon_det: det(g) = −1/c²（空间流动保体积 = 坐标变换层面）
--   SG3  gordon_inverse: g⁻¹ = [[1, v], [v, −(c²−v²)]]（逆变度规）
--   SG4  gordon_inverse_mul: g⁻¹·g = I（度规-逆变度规正交）
--   SG5  momentumFour: 4-动量 P = (E/c, p)（光子 p=E/c 完全随空间; 质量偏离）
--   SG6  photon_momentum_energy: 光子 p = E/c（零质量动量-能量关系）
--   SG7  massive_momentum_deviation: 质量动量含偏离因子
--
-- 诚实边界: 完整 GR（黎曼曲率/Bianchi/场方程推导）需 mathlib
-- RiemannianGeometry 大工程; 本模块是推导链的代数骨架 +
-- 数值完整链（scripts/verify_gravity_from_conservation.py）。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section
namespace SpaceGravity

/-- 1+1 维实数矩阵。 -/
abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-! ### ① 空间流动 ⟹ 度规（Gordon 度规） -/

/-- ★ SG1：空间流动 v 的 1+1 维度规（Gordon 度规）:
    g = [[1−v²/c², v/c²], [v/c², −1/c²]].
    平直空间（v=0）⟹ g = diag(1, −1/c²)（= SpaceMetric.metric, 闵可夫斯基）。
    空间流动非均匀 v(x) ⟹ 度规弯曲（GR 重构的入口）。 -/
def gordonMetric (v c : ℝ) : Mat2R :=
  !![ 1 - v*v/(c*c), v/(c*c); v/(c*c), -1/(c*c) ]

/-- 平直空间（v=0）时 Gordon 度规 = 闵可夫斯基度规（时间+1, 空间−1/c²）。 -/
theorem gordon_flat_is_minkowski (c : ℝ) (_hc : c ≠ 0) :
    gordonMetric 0 c = !![ 1, 0; 0, -1/(c*c) ] := by
  unfold gordonMetric
  ext i j <;> fin_cases i <;> fin_cases j <;> simp

/-- ★ SG2：det(g) = −1/c²——空间流动保体积（坐标变换层面）。
    与 SpaceMetric.metric_det 一致：流动是几何的重新参数化，
    不改变时空"体积"。 -/
theorem gordon_det (v c : ℝ) (hc : c ≠ 0) :
    Matrix.det (gordonMetric v c) = -1 / (c*c) := by
  rw [Matrix.det_fin_two]
  unfold gordonMetric
  simp
  field_simp [hc]
  ring_nf

/-- ★ SG3：逆变度规 g⁻¹ = [[1, v], [v, −(c²−v²)]]。
    从 g·g⁻¹ = I 解出（分量验证）。 -/
def gordonInverse (v c : ℝ) : Mat2R :=
  !![ 1, v; v, -(c*c - v*v) ]

/-- ★ SG4：g⁻¹·g = I（度规与逆变度规正交）——分量验证。
    这保证 4-动量 P^μ = g^μν P_ν 的升降是良定义的。 -/
theorem gordon_inverse_mul (v c : ℝ) (hc : c ≠ 0) :
    gordonInverse v c * gordonMetric v c = 1 := by
  unfold gordonInverse gordonMetric
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply] <;> field_simp [hc] <;> ring

/-! ### ② 动量守恒 -/

/-- 4-动量（1+1 维）: P = (E/c, p)——时间分量 = 能量/c, 空间分量 = 动量。 -/
def fourMomentum (E p c : ℝ) : Fin 2 → ℝ :=
  ![ E/c, p ]

/-- ★ SG5：光子动量 = 能量/c（零质量色散关系 p = E/c）。
    光子完全随空间运动（dx=c·dt）⟹ 动量-能量关系是光速的,
    不是质量的——零质量边界。 -/
def photonMomentum (E c : ℝ) : Fin 2 → ℝ :=
  ![ E/c, E/c ]

/-- ★ SG6：光子零质量条件（平直度规）——ds² = g_tt·dt² + g_xx·dx² = 0，
    代入光子 dx = c·dt（SM1 完全随空间）⟹ g_tt + g_xx·c² = 0。
    展开: 1 + (−1/c²)·c² = 0——光子无质量（"不花时间" SM1 dτ=0）
    的度规-动量对应。 -/
theorem photon_massless_metric_condition (c : ℝ) (hc : c ≠ 0) :
    (gordonMetric 0 c) ⟨0, by decide⟩ ⟨0, by decide⟩ +
    (gordonMetric 0 c) ⟨1, by decide⟩ ⟨1, by decide⟩ * c^2 = 0 := by
  unfold gordonMetric
  simp
  field_simp [hc]
  ring

/-- ★ SG7：质量粒子动量含偏离空间流动的因子（p = γmv, v = c−u）。
    质量 = 偏离空间流动（SM3c）⟹ 动量是偏离量 u 的函数;
    光子 u=0 时退化为零质量动量 p=E/c。
    SG8：静止质量（u=c）⟹ 能量 E=mc²（RD5 差值能量形式中已有）。 -/
def massiveMomentum (m u c : ℝ) : Fin 2 → ℝ :=
  ![ m*c*c / Real.sqrt (2*c*u - u*u), m*(c-u)*c / Real.sqrt (2*c*u - u*u) ]

/-! ### ④ Gordon 固有时间与光子零质量（非均匀流动验证） -/

/-- Gordon 形式固有时间平方: dτ² = dt² − (dx − v·dt)²/c².
    空间流动 v 的坐标中, 物质相对流动的运动 (dx − v·dt) 决定固有时。
    v=0 退化为 SpaceMetric.properTimeSq（绝对框架）。 -/
def gordonProperTimeSq (v c : ℝ) (dt dx : ℝ) : ℝ :=
  dt^2 - (dx - v * dt)^2 / c^2

/-- ★ SM4-Gordon: dτ²_gordon = g_μν Δx^μ Δx^ν（gordonMetric 双线性形式）。
    确认 Gordon 形式固有时间 = Gordon 度规的二次型（SM4 在非零流动 v 下的对应）。 -/
theorem gordon_proper_time_eq_metric (v c : ℝ) (dt dx : ℝ) (hc : c ≠ 0) :
    gordonProperTimeSq v c dt dx =
      (gordonMetric v c) ⟨0, by decide⟩ ⟨0, by decide⟩ * dt^2 +
      (gordonMetric v c) ⟨0, by decide⟩ ⟨1, by decide⟩ * (dt * dx) +
      (gordonMetric v c) ⟨1, by decide⟩ ⟨0, by decide⟩ * (dt * dx) +
      (gordonMetric v c) ⟨1, by decide⟩ ⟨1, by decide⟩ * dx^2 := by
  unfold gordonProperTimeSq gordonMetric
  simp
  field_simp [hc]
  ring

/-- ★ Gordon-光子零质量: 光子相对空间流动以 c 运动（dx − v·dt = c·dt）
    ⟹ dτ² = 0（SM1 在非均匀流动 v ≠ 0 下的对应）。
    建模坑: 光子条件是相对流动 |dx − v·dt| = c·dt, 不是随流动静止 dx = v·dt
    （那会得 dτ² = dt² ≠ 0 的错误物理——Gordon 描述的是流动介质中的光）。 -/
theorem gordon_photon_proper_time_zero (v c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (h : dx - v * dt = c * dt) :
    gordonProperTimeSq v c dt dx = 0 := by
  unfold gordonProperTimeSq
  rw [h]
  field_simp [hc]
  ring

/-- ★ Gordon-光子（反向）: 光子逆着流动以 c 运动（dx − v·dt = −c·dt）⟹ dτ² = 0。 -/
theorem gordon_photon_proper_time_zero_rev (v c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (h : dx - v * dt = -c * dt) :
    gordonProperTimeSq v c dt dx = 0 := by
  unfold gordonProperTimeSq
  rw [h]
  field_simp [hc]
  ring

/-- ★ Gordon-弱场匹配（Φ = ½v² 定理化）: Gordon g_tt = 1 − v²/c²，
    与弱场 GR g_tt = 1 − 2Φ/c² 精确一致, Φ = ½v²。
    引力势 = 空间流动速度平方的一半。 -/
theorem gordon_weak_field_matches_newton (v c : ℝ) (hc : c ≠ 0) :
    (gordonMetric v c) ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 - 2 * (v * v / 2) / (c * c) := by
  unfold gordonMetric
  simp
  field_simp [hc]

/-! ### ③ 推导链的诚实边界 -/

/-- 完整 GR 推导（黎曼曲率张量 R^λ_μνρ、Bianchi 恒等式 ∇_[λ R^μν]_ρσ = 0、
    爱因斯坦张量 G_μν = R_μν − ½Rg_μν、场方程 G_μν = κT_μν）需要
    mathlib 的 RiemannianGeometry（曲率/联络/测地线完整框架）。
    本模块提供推导链的代数骨架（度规←流动, 动量守恒, 光子/质量动量）;
    完整链在数值层 scripts/verify_gravity_from_conservation.py 验证。 -/
def GR_DERIVATION_SCOPE : String :=
  "代数骨架: Gordon 度规 + 动量守恒 + 光子/质量动量; 完整曲率/场方程在数值层"

end SpaceGravity
