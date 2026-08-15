-- ProjectionPhysics — QFTFlow：量子场论 × 流动空间（激发态 + 全域纠缠）
--
-- leo（2026-08-15）假设：用流动空间框架重新定义量子场论的"激发态"，
-- 并纳入全域性量子纠缠：
--   · 标准 QFT：激发态 = 产生算符作用在真空态 a†(p)|0⟩，粒子 = 场的激发；
--     真空 = 最低能量基态。
--   · 流动空间重释：非激发（unexcited）= 完全随空间流动的模式（光子，
--     dτ = 0，SLS2/SM1）；激发（excited）= 偏离空间流动的模式（锚定，
--     dτ > 0，MC1/SM3c）。"激发" = 从全域流动中分离出局部锚定。
--   · 全域纠缠：纠缠不是粒子间的超距作用，而是空间场自身的相干结构
--     ——反相双螺旋在任何位置完全反关联（无距离衰减）；三方向
--     （σ₁,σ₂,σ₃）构成不可分离的纠缠基底（GHZ 判据：单体约化混合）。
--   · ★ 统一命题：无质量（非激发）⟺ 秩 1（单扭量 det = 0，可分）；
--     有质量（激发）⟺ 秩 2（双扭量 det = |⟨π₁,π₂⟩|²，两半旋量纠缠复合）。
--
-- 本模块形式化数学内核：
--   QFT1 ★ 非激发 = 完全随流：dx = c·dt ⟹ dτ² = 0（引用 SM1）
--   QFT2 ★ 激发 ⟹ 偏离空间流动：0 < dτ² ⟹ dx ≠ c·dt（引用 SM3c）
--   QFT3 激发态质量 = 锚定范数：m² = |ψ₁|²+|ψ₀|²，非零旋量 ⟹ m² > 0（引用 MC4'/MC2'）
--   QFT4 多激发质量加法：三方向叠加 m² = m₁²+m₂²+m₃²（引用 MC6'）+
--        叠加锚定永不减少（新证——产生算符叠加只增质量）
--   QFT5 ★ 全域相干：cos(θ+π) = −cos θ——反相双螺旋在任何位置完全
--        反关联（与位置 θ 无关 = 无距离衰减，全域性解析内核）
--   QFT6 三方向 = 全域纠缠基底：(σ₁+σ₂+σ₃)² = 3I（引用 SH3）+ det ≠ 0
--   QFT7 ★ GHZ 三体纠缠判据：|GHZ⟩ 的单体约化 ρ_A = ½I 是混合态
--        （ρ² ≠ ρ，Tr(ρ²) = ½ < 1——三体纠缠 ⟹ 单体不可纯化）
--   QFT8 ★ 秩判据：双扭量 det = |⟨π₁,π₂⟩|²；det = 0 ⟺ 两旋量平行
--        （无质量 ⟺ 非激发 ⟺ 可分）；非平行 ⟹ m² > 0（激发）
--   QFT9 ★ 统一命题：单扭量 det = 0（非激发/秩 1/可分）∧
--        双扭量 det = |⟨π₁,π₂⟩|²（激发/秩 2/纠缠）——质量 ⟺ 激发 ⟺ 纠缠
--
-- 诚实边界：QFT1–4 是已有公设（SM/MC）的激发态重述；QFT5 是三角恒等
-- （数学内核真但平凡）；QFT6–7 是标准量子信息（GHZ 判据）的代数化；
-- QFT8–9 是 TW1/TW6（彭罗斯经典）的组合——真正的框架贡献 = "激发 =
-- 锚定偏离 + 秩 2 纠缠"的概念统一（解释层），非新物理预言。数值层：
-- 全域纠缠"与距离无关"需数值验证（E(Δ) 无距离衰减）。

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ProjectionPhysics.SpaceMetric
import ProjectionPhysics.MinimalCoreMathlib
import ProjectionPhysics.PauliMathlib
import ProjectionPhysics.Explorations.SphericalHarmonics
import ProjectionPhysics.Explorations.Twistor

noncomputable section
open Matrix
open PauliMathlib

namespace ProjectionPhysics.QFTFlow

/-! ### QFT1–QFT4. 激发态 = 偏离空间流动（锚定） -/

/-! ### QFT1. 非激发 = 完全随流 -/

/-- ★ QFT1：非激发（unexcited）= 完全随空间流动的模式（dx = c·dt）
    ⟹ dτ² = 0——不花时间。流动空间的"真空/基态模式" = 光锥上的
    流动本身（光子）；非激发不是"死寂"，而是与空间流动完全同步。
    对应标准 QFT：真空态 |0⟩ = 场的基态；此处基态 = 随流模式。 -/
theorem unexcited_comoving_zero_time (c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (h : dx = c * dt) :
    SpaceMetric.properTimeSq c dt dx = 0 :=
  SpaceMetric.photon_proper_time_zero c dt dx hc h

/-! ### QFT2. 激发 ⟹ 偏离空间流动 -/

/-- ★ QFT2：激发态（有质量，dτ² > 0）⟹ 偏离空间流动（dx ≠ c·dt）。
    标准 QFT 中激发态 = 能量高于真空的态；流动空间中，激发 = 从
    全域流动中分离（锚定）——"空间阻力"的精确形式（SM3c 重述）。 -/
theorem excited_implies_deviation_from_flow (c : ℝ) (dt dx : ℝ)
    (hc : c ≠ 0) (h : 0 < SpaceMetric.properTimeSq c dt dx) :
    dx ≠ c * dt :=
  SpaceMetric.mass_implies_deviation_from_flow c dt dx hc h

/-! ### QFT3. 激发态质量 = 锚定范数 -/

/-- ★ QFT3a：激发态的质量平方 = 锚定范数 m² = |ψ₁|² + |ψ₀|²
    （激发强度 = 旋量流对空间运动的锚定量，MC4' 重述）。
    "激发态粒子"的质量不是场的能量，而是空间流动的锚定效果。 -/
theorem excitation_mass_sq_components (ψ : MinimalCoreMathlib.Spinor) :
    MinimalCoreMathlib.anchorMassSq ψ =
      Complex.normSq (ψ ⟨1, by decide⟩) + Complex.normSq (ψ ⟨0, by decide⟩) :=
  MinimalCoreMathlib.anchorMassSq_component ψ

/-- ★ QFT3b：非零锚定旋量（被激发的内部运动状态）⟹ 质量平方 > 0。
    激发态粒子 = 有内部运动（自旋流）的模式——自旋非零 ⟹ m ≠ 0（MC2'）。 -/
theorem excitation_mass_pos_of_nonzero (ψ : MinimalCoreMathlib.Spinor) (h : ψ ≠ 0) :
    0 < MinimalCoreMathlib.anchorMassSq ψ :=
  MinimalCoreMathlib.anchorMassSq_pos_of_nonzero ψ h

/-! ### QFT4. 多激发质量加法（产生算符叠加） -/

/-- ★ QFT4a：多激发（三方向叠加）质量平方 = 各激发锚定之和：
    m² = m₁² + m₂² + m₃²（MC6' 定义，胶球 √N·M₀ 序列的代数种子——
    "产生算符"每叠加一个方向模式，质量平方加一项）。 -/
theorem multi_excitation_mass_add (ψ₁ ψ₂ ψ₃ : MinimalCoreMathlib.Spinor) :
    MinimalCoreMathlib.glueballMassSq3 ψ₁ ψ₂ ψ₃ =
      MinimalCoreMathlib.anchorMassSq ψ₁ + MinimalCoreMathlib.anchorMassSq ψ₂ +
        MinimalCoreMathlib.anchorMassSq ψ₃ :=
  rfl

/-- ★ QFT4b：叠加锚定永不减少——激发叠加只会增加（至少不减少）质量。
    （产生算符叠加模式的单调性：m²(叠加) ≥ m²(单个)。） -/
theorem superposition_mass_never_decreases (ψ₁ ψ₂ ψ₃ : MinimalCoreMathlib.Spinor) :
    MinimalCoreMathlib.anchorMassSq ψ₁ ≤
      MinimalCoreMathlib.glueballMassSq3 ψ₁ ψ₂ ψ₃ := by
  rw [multi_excitation_mass_add]
  have h2 : 0 ≤ MinimalCoreMathlib.anchorMassSq ψ₂ := by
    unfold MinimalCoreMathlib.anchorMassSq
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have h3 : 0 ≤ MinimalCoreMathlib.anchorMassSq ψ₃ := by
    unfold MinimalCoreMathlib.anchorMassSq
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  linarith

/-! ### QFT5–QFT7. 全域纠缠 = 空间场相干 -/

/-! ### QFT5. 全域相干：反相双螺旋无距离衰减 -/

/-- ★ QFT5a：反相恒等 cos(θ+π) = −cos θ，对任意位置相位 θ 成立。
    双螺旋纠缠（EH 系列）的两股反相流（λ 与 λ+π）在任何位置完全
    反关联——反相关系与位置无关 = 全域性（无距离衰减）的解析内核：
    纠缠不是"相隔很远才发生的关联"，而是空间场处处自带的相干结构。 -/
theorem antiphase_anticorrelation_global (θ : ℝ) :
    Real.cos (θ + Real.pi) = -Real.cos θ := by
  rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
  ring

/-- ★ QFT5b：反相双螺旋在任意点的关联乘积 = −cos²θ ≤ 0（完全反关联），
    且对任意位置 θ 相同——全域纠缠关联不依赖测量位置（距离）。 -/
theorem antiphase_correlation_any_point (θ : ℝ) :
    Real.cos θ * Real.cos (θ + Real.pi) = -(Real.cos θ) ^ 2 := by
  rw [antiphase_anticorrelation_global θ]
  ring

/-! ### QFT6. 三方向 = 全域纠缠基底 -/

/-- ★ QFT6a：三方向纠缠算符的平方 = 球对称标量 3I（引用 SH3）——
    三个方向互相连接成为整体结构；交叉项被反交换消灭。
    "全域纠缠基底" = 空间三方向不可分离地构成一个整体。 -/
theorem three_direction_entanglement_basis :
    (σ₁ + σ₂ + σ₃) * (σ₁ + σ₂ + σ₃) = (3 : ℂ) • (1 : Mat2C) :=
  SphericalHarmonics.triplet_operator_sq_is_three

/-- ★ QFT6b：三方向纠缠算符可逆（det = −3 ≠ 0）——三方向叠加不是
    投影（信息不损失），联合旋量流非零 ⟹ 三方向全域纠缠是"满秩"
    的：任何非零旋量都被三方向联合捕获（MC6' 的 det 论证）。 -/
theorem three_direction_invertible :
    Matrix.det (σ₁ + σ₂ + σ₃) ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp [σ₁, σ₂, σ₃]
  have h2 : (1 + -Complex.I) * (1 + Complex.I) = 2 := by
    apply Complex.ext <;> simp [Complex.I_re, Complex.I_im] <;> ring
  rw [h2]
  norm_num

/-! ### QFT7. GHZ 三体纠缠判据：单体约化混合 -/

/-- GHZ 态 |GHZ⟩ = (|000⟩+|111⟩)/√2 的单体约化密度矩阵
    ρ_A = Tr_BC(|GHZ⟩⟨GHZ|) = ½I（最大混合态）。
    标准量子信息结果（三体纠缠 ⟹ 任意单体约化混合）。 -/
def ghzReducedA : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- ★ QFT7a：GHZ 单体约化是混合态：ρ_A² ≠ ρ_A（不是纯态投影）。
    三体纠缠 ⟹ 只看单个方向（单体）无法纯化——全域纠缠意味着
    "单独一个方向的信息是不完整的"（三方向全域纠缠的 GHZ 判据）。 -/
theorem ghz_reduced_is_mixed :
    ghzReducedA * ghzReducedA ≠ ghzReducedA := by
  intro h
  have h00 := congr_fun (congr_fun h ⟨0, by decide⟩) ⟨0, by decide⟩
  norm_num [ghzReducedA, Matrix.mul_apply] at h00

/-- ★ QFT7b：GHZ 单体约化的纯度 Tr(ρ_A²) = ½ < 1（最大混合）。
    纯态判据 Tr(ρ²) = 1；混合程度 ½ 恰为 2 维最大混合——单体
    约化损失了全部关联信息（全域纠缠的量化判据）。 -/
theorem ghz_reduced_purity :
    Matrix.trace (ghzReducedA * ghzReducedA) = (1 / 2 : ℂ) := by
  norm_num [ghzReducedA, Matrix.trace, Matrix.mul_apply]

/-! ### QFT8–QFT9. 统一：质量 ⟺ 激发 ⟺ 秩 2 纠缠 -/

/-! ### QFT8. 秩判据：双扭量 det = 辛内积模平方 -/

/-- 双扭量动量行列式 det(p₁+p₂) = s·star s，s = a₁b₂−a₂b₁（两旋量辛内积）。 -/
def pairDet (a₁ b₁ a₂ b₂ : ℂ) : ℂ :=
  (a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁)

/-- ★ QFT8a：双扭量 det = |⟨π₁,π₂⟩|²（引用 TW6）——两秩 1 外积之和的
    行列式 = 两旋量辛内积的模平方。质量 = 两半旋量的相对方向。 -/
theorem pair_det_eq_symplectic_normSq (a₁ b₁ a₂ b₂ : ℂ) :
    pairDet a₁ b₁ a₂ b₂ =
      (a₁ * star a₁ + a₂ * star a₂) * (b₁ * star b₁ + b₂ * star b₂)
        - (a₁ * star b₁ + a₂ * star b₂) * (star a₁ * b₁ + star a₂ * b₂) := by
  unfold pairDet
  rw [← ProjectionPhysics.Twistor.twistor_pair_momentum_det a₁ b₁ a₂ b₂]

/-- ★ QFT8b：无质量 ⟺ 两旋量平行：det = 0 ⟺ ⟨π₁,π₂⟩ = 0。
    秩 2 矩阵退化为秩 1（无质量/非激发）恰好当两个半旋量平行——
    "可分"（非纠缠） = 秩 1 = 无质量（光子边界）。 -/
theorem pair_massless_iff_parallel (a₁ b₁ a₂ b₂ : ℂ) :
    pairDet a₁ b₁ a₂ b₂ = 0 ↔ a₁ * b₂ - a₂ * b₁ = 0 := by
  unfold pairDet
  constructor
  · intro h
    by_contra hs
    have hstar : star (a₁ * b₂ - a₂ * b₁) ≠ 0 := star_ne_zero.mpr hs
    have hprod : (a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁) ≠ 0 :=
      mul_ne_zero hs hstar
    exact hprod h
  · intro h
    rw [h]
    simp

/-- ★ QFT8c：非平行 ⟹ 有质量（激发）：辛内积非零 ⟹ m² > 0。
    电子 = 两半旋量的纠缠复合；旋量方向不平行 = 激发 = 锚定。 -/
theorem pair_mass_pos_of_nonparallel (a₁ b₁ a₂ b₂ : ℂ)
    (h : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    0 < Complex.normSq (a₁ * b₂ - a₂ * b₁) :=
  Complex.normSq_pos.mpr h

/-! ### QFT9. 统一命题：质量 ⟺ 激发 ⟺ 纠缠 -/

/-- ★ QFT9：统一秩判据——
    单扭量（秩 1）：det = 0 恒成立（TW1）⟹ 无质量 ⟹ 非激发 ⟹ 可分；
    双扭量（秩 2）：det = |⟨π₁,π₂⟩|²，det = 0 ⟺ 两旋量平行（QFT8b）。
    合读：无质量（非激发，完全随流）⟺ 秩 1（单扭量，可分）；
    有质量（激发，锚定偏离）⟺ 秩 2（双扭量，两半旋量纠缠复合）。
    在流动空间中，"激发态粒子"与"纠缠"是同一个秩 2 结构的两个面。 -/
theorem unified_rank_entanglement (a₁ b₁ a₂ b₂ : ℂ) :
    ((a₁ * star a₁) * (b₁ * star b₁) - (a₁ * star b₁) * (b₁ * star a₁) = 0) ∧
    (pairDet a₁ b₁ a₂ b₂ = 0 ↔ a₁ * b₂ - a₂ * b₁ = 0) := by
  constructor
  · exact ProjectionPhysics.Twistor.twistor_momentum_massless a₁ b₁
  · exact pair_massless_iff_parallel a₁ b₁ a₂ b₂

/-! ### 结论注释 -/

-- QFT1–QFT9 合读（QFT × 流动空间的判定）：
--   1. 激发态 = 偏离空间流动：非激发（光子）完全随流（QFT1，dτ=0），
--      激发（质量粒子）锚定偏离（QFT2，dτ>0）；激发强度 = 锚定范数
--      （QFT3，m²=|ψ₁|²+|ψ₀|²），叠加只增不减（QFT4）。
--   2. 全域纠缠 = 空间场相干：反相双螺旋任何位置完全反关联（QFT5，
--      无距离衰减）；三方向不可分离（QFT6，(σ₁+σ₂+σ₃)²=3I 且 det≠0）；
--      GHZ 判据：单体约化混合（QFT7，ρ_A=½I，Tr(ρ²)=½<1）。
--   3. ★ 统一：质量 ⟺ 激发 ⟺ 秩 2 纠缠（QFT8–9）——无质量 = 秩 1
--      = 单扭量 = 可分（非激发）；有质量 = 秩 2 = 双扭量 = 两半旋量
--      纠缠复合（激发）。标准 QFT 的"粒子 = 场的激发"在流动空间中
--      成为"粒子 = 空间流动的秩 2 锚定结构"——激发与纠缠同源。
--   4. 诚实边界：数学内核多为已知物理（三角恒等/GHZ 判据/彭罗斯
--      双扭量）的代数化 + 已有公设（SM/MC）重述；框架贡献 = 概念
--      统一（解释层）。"全域纠缠无距离衰减"的数值验证见
--      scripts/verify_qft_flow.py（E(Δ) 与传播距离无关）。

end ProjectionPhysics.QFTFlow

end
