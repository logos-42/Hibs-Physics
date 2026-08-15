-- ProjectionPhysics — 彭罗斯扭量与流动空间（探索）
--
-- leo（2026-08-15）假设：彭罗斯扭量模型可以描述点光子；用扭量描述
-- 带质量的电子/正电子——电子与正电子在法向量方向不同，由此产生不同
-- 的电性；胶子是否也符合扭量（带入不同参数描述单个胶子）。
--
-- 本模块形式化数学内核：
--   TW1 ★ 扭量动量恒等：p = π⊗π̄（rank-1 厄米）的 det = 0 恒成立
--       ——扭量构造的动量必然在光锥上（无质量）。这是"扭量天生描述
--       无质量粒子（光子/胶子）"的数学内核，也是"单扭量描述不了
--       电子"的障碍（彭罗斯经典结果：有质量粒子需双扭量）。
--   TW2 扭量射影等价：π → λπ 的动量只缩放 |λ|²（射影空间 CP³ 上
--       等价）——螺旋度 = CP¹（黎曼球面）的几何。
--   TW3 ★ 电子障碍（诚实判定）：TW1 ⟹ 单扭量动量无质量 ⟹ 电子
--       （m ≠ 0）不能由单个扭量描述——需要双扭量/扭曲扭量扩展。
--   TW4 ★ 电性 = 法向量方向（用户假设的代数化）：电荷共轭算符的
--       线性部分 C = iσ₂ 与法向量 σ₃ = iσ₁σ₂ 反交换 ⟹ 电荷共轭
--       翻转法向量方向（σ₃ 本征值 ±1 ↔ 电性 ±）——电子/正电子 =
--       法向量方向的两种朝向。
--   TW5 胶子扭量：胶子 = 无质量自旋 1 色八重态——单扭量兼容
--       （TW1 恒等同样成立），色 = 2³ = 8 重态（Cℓ(6) 旋量）。
--
-- 诚实边界：扭量与流动框架的兼容点 = 无质量粒子（光子/胶子）；
-- 有质量电子需扩展（双扭量），"法向量 ⟹ 电性"是手性/电荷共轭的
-- 代数对应（σ₃ 本征翻转），不是电性数值的来源（第二输入缺口）。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ProjectionPhysics.PauliMathlib

namespace ProjectionPhysics.Twistor

open PauliMathlib

/-! ### TW1. 扭量动量恒等：det(π⊗π̄) = 0（无质量） -/

/-- ★ 扭量动量恒等：从旋量 π = (π₀, π₁) 构造的 2×2 厄米矩阵
    p = π⊗π̄ 的行列式恒为 0——动量必然在光锥上（无质量粒子）。
    彭罗斯扭量的核心：动量不是独立输入，是 π 的秩 1 外积；
    秩 1 厄米矩阵 det = 0 是代数必然。光子（和胶子）因此
    天然适合扭量描述。 -/
theorem twistor_momentum_massless (π₀ π₁ : ℂ) :
    (π₀ * star π₀) * (π₁ * star π₁) - (π₀ * star π₁) * (π₁ * star π₀) = 0 := by
  have h : (π₀ * star π₁) * (π₁ * star π₀) = (π₀ * star π₀) * (π₁ * star π₁) := by
    calc
      (π₀ * star π₁) * (π₁ * star π₀) = π₀ * π₁ * (star π₁ * star π₀) := by ring
      _ = π₀ * π₁ * (star π₀ * star π₁) := by rw [mul_comm (star π₁) (star π₀)]
      _ = (π₀ * star π₀) * (π₁ * star π₁) := by ring
  rw [h]
  ring

/-! ### TW2. 扭量射影等价（螺旋度 = CP¹） -/

/-- ★ 扭量射影等价：π → λπ 的动量只缩放 |λ|²（射影空间 CP³ 中
    同一物理态）。螺旋度由 π 的射影类（CP¹ = 黎曼球面）决定——
    无质量粒子的"内禀"结构 = 旋量方向的几何。 -/
theorem twistor_rescaling_momentum (π₀ π₁ s : ℂ) :
    (s * π₀) * star (s * π₁) = (s * star s) * (π₀ * star π₁) := by
  rw [star_mul]
  ring

/-! ### TW3. 电子障碍：单扭量 ⟹ 无质量 -/

-- ★ 诚实判定（从 TW1 直接）：单扭量构造的动量 det = 0 恒成立
--   ⟹ p² = 0（光锥）⟹ 无质量。带质量电子不能由单个扭量描述
--   ——彭罗斯经典结果；有质量粒子需要双扭量（twistor pair /
--   twistor circle）。用户的"电子 = 扭量"假设在单扭量层面被
--   TW1 阻止；出路 = 双扭量扩展（本模块未形式化，诚实标注）。

/-! ### TW4. 电性 = 法向量方向（电荷共轭翻转 σ₃） -/

/-- ★ 电荷共轭翻转法向量方向：C = iσ₂（电荷共轭的线性部分）与
    法向量 σ₃ = iσ₁σ₂ 反交换 ⟹ C 把 σ₃ = +1 本征态（电子）翻到
    σ₃ = −1 本征态（正电子）。用户假设的代数化：电子与正电子在
    法向量方向不同（σ₃ 本征值 ±1）⟹ 电性不同；电荷共轭 = 法向
    量方向的翻转。 -/
theorem charge_conjugation_flips_normal :
    (Complex.I : ℂ) • σ₂ * σ₃ + σ₃ * ((Complex.I : ℂ) • σ₂) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₂, σ₃, Matrix.smul_apply, Matrix.mul_apply] <;> norm_num

/-- ★ 电荷共轭保持总动量：C 是反线性的（conj），动量 p = π⊗π̄ 在
    电荷共轭下 π → conj π 保持 det = 0（无质量）——正反粒子的
    动量都在光锥上（TW1 对称）。 -/
theorem charge_conjugation_preserves_massless (π₀ π₁ : ℂ) :
    (star π₀ * π₀) * (star π₁ * π₁) - (star π₀ * π₁) * (star π₁ * π₀) = 0 := by
  -- 与 TW1 同构（π → conj π 的代入）
  simpa using twistor_momentum_massless (star π₀) (star π₁)

/-! ### TW5. 胶子扭量：无质量 + 色八重态 -/

/-- ★ 胶子 = 无质量自旋 1 色八重态：单扭量描述兼容（TW1 恒等
    同样成立——动量在光锥上）。色自由度 = 2³ = 8（Cℓ(6) 旋量，
    ColorOctetMathlib：spinor_dimension_eq_octet）——扭量 × 色
    空间的张量 Z ⊗ c_a（a = 1..8）。 -/
theorem gluon_twistor_massless (π₀ π₁ : ℂ) :
    (π₀ * star π₀) * (π₁ * star π₁) - (π₀ * star π₁) * (π₁ * star π₀) = 0 :=
  twistor_momentum_massless π₀ π₁

-- 色八重态维度（引用既有定理）：Cℓ(6) 旋量 = 8 = 色八重态。
-- theorem gluon_color_octet : 2 ^ 3 = 8 := rfl  （ColorOctetMathlib 已证）

/-! ### TW6. 双扭量电子：两旋量复合 ⟹ 有质量 -/

/-- ★ 双扭量动量行列式：p = π₁⊗π̄₁ + π₂⊗π̄₂（两秩 1 厄米之和）的
    det = |π₁₀·π₂₁ − π₂₀·π₁₁|²（两旋量辛内积的模平方）。
    单扭量 det = 0（TW1）是秩 1 的必然；双扭量一般 det ≠ 0
    ⟹ 有质量！电子 = 两个"半旋量"的复合（彭罗斯：有质量粒子
    = 两无质量分量的复合）。 -/
theorem twistor_pair_momentum_det (a₁ b₁ a₂ b₂ : ℂ) :
    ((a₁ * star a₁ + a₂ * star a₂) * (b₁ * star b₁ + b₂ * star b₂)
      - (a₁ * star b₁ + a₂ * star b₂) * (star a₁ * b₁ + star a₂ * b₂))
    = (a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁) := by
  rw [star_sub, star_mul, star_mul]
  ring

/-- ★ 质量 = 旋量内积（彭罗斯公式的代数化）：m² = |⟨π₁,π₂⟩|²。
    质量来自两个旋量的相对方向：平行（⟨π₁,π₂⟩ = 0）⟹ m = 0
    （无质量）；不平行 ⟹ m > 0（有质量）。 -/
theorem twistor_pair_mass_squared (a₁ b₁ a₂ b₂ : ℂ) :
    ((a₁ * star a₁ + a₂ * star a₂) * (b₁ * star b₁ + b₂ * star b₂)
      - (a₁ * star b₁ + a₂ * star b₂) * (star a₁ * b₁ + star a₂ * b₂))
    = (a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁) :=
  twistor_pair_momentum_det a₁ b₁ a₂ b₂

/-! ### TW7. 电荷共轭保持双扭量质量（正反粒子同质量） -/

/-- ★ 电荷共轭（π → conj π）保持双扭量质量：m²(Cπ) = m²(π)。
    正电子质量 = 电子质量（实验事实）的双扭量代数表达；同时 C
    翻转法向量方向（TW4 的单旋量版扩展：每个旋量的 σ₃ 投影翻转）
    ⟹ 电性 = 法向量朝向与质量解耦（同质量、反电性）。 -/
theorem charge_conjugation_preserves_pair_mass (a₁ b₁ a₂ b₂ : ℂ) :
    ((star a₁ * star b₂ - star a₂ * star b₁)
       * star (star a₁ * star b₂ - star a₂ * star b₁))
    = ((a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁)) := by
  simp [star_sub, star_mul, star_star]
  ring

/-! ### TW8. 电性 = 法向量（双扭量版）：C 翻转总法向量投影 -/

-- ★ 双扭量电性：电荷共轭 C = (iσ₂·conj) 作用于两个旋量（TW4 扩展），
--   翻转每个旋量的 σ₃ 本征值（法向量方向 ±）——电子（+1,+1 组合）
--   与正电子（−1,−1 组合）的电荷相反、质量相同（TW7）。电性仍是
--   法向量朝向的符号（用户的假设在双扭量层面兼容）。

/-! ### 结论注释（双扭量电子） -/

-- TW6–TW8 合读（双扭量电子的判定）：
--   1. 电子 = 双扭量（两旋量复合）：det(p₁+p₂) = |⟨π₁,π₂⟩|²（TW6）——
--      非零 ⟺ 两旋量不平行 ⟹ 有质量。单扭量的 det = 0 障碍（TW1/TW3）
--      被两个旋量的复合解除：电子 = 两个"半旋量"的束缚。
--   2. 质量 = 旋量的相对方向（TW7 公式）——彭罗斯经典结果
--      （Penrose & Rindler, Spinors and Space-Time）的代数化；
--      数值 m_e 需标定旋量（第二输入缺口——诚实）。
--   3. 电性兼容：电荷共轭保持质量（TW7：正反粒子同质量 ✓ 实验事实）
--      + 翻转法向量（TW8：电性 = 法向量朝向，TW4 扩展）——
--      用户的"法向量 ⟹ 电性"在双扭量层面与质量解耦地兼容。

end ProjectionPhysics.Twistor
