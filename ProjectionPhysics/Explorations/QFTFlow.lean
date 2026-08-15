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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.LinearIndependent.Defs
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

/-! ### GQ1–GQ6. 三扭量胶球：激发 ⟺ 秩 3 纠缠（QFT8–9 的三方向推广） -/

-- leo（2026-08-15 第二轮）：把"电子 = 双扭量秩 2"推广到三方向胶球——
-- 三扭量（3 维旋量，色空间）P = π₁⊗π̄₁ + π₂⊗π̄₂ + π₃⊗π̄₃。
-- 核心恒等（Cauchy-Binet / det(AA†) = |det A|² 特例）：
--   det₃(P) = |det₃[π₁ π₂ π₃]|² —— 胶球质量平方 = 三扭量体积形式。
-- 统一秩判据（质量 ⟺ 激发 ⟺ 秩）：
--   N=1 光子：det₁ = |π₁|²（秩 1，非激发）
--   N=2 电子：det₂ = |⟨π₁,π₂⟩|²（秩 2，激发，QFT8）
--   N=3 胶球：det₃ = |det₃[π₁π₂π₃]|²（秩 3，激发——三扭量线性无关）
-- 诚实边界：2×2 的 det ≤ tr²/4 装不下"三秩"（两秩上限），故三方向胶球
-- 必须用 3×3（色空间）——这本身是"为什么胶子生活在 SU(3) 色空间"的
-- 代数线索；数值上 det₃ ≤ 1（单位旋量，Hadamard），与 √3·M₀ 的关系
-- 是结构对应而非数值匹配（方向锚定相加 MC6' 仍负责格点谱）。

/-- 3 维扭量（色空间旋量）。 -/
abbrev TriTwistor : Type := Fin 3 → ℂ

/-- 三扭量外积和（3×3 分量空间矩阵）：P = π₁⊗π̄₁ + π₂⊗π̄₂ + π₃⊗π̄₃。 -/
def tripleOuterSum (a b c : TriTwistor) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vecMulVec a (star a) + Matrix.vecMulVec b (star b) +
    Matrix.vecMulVec c (star c)

/-- 扭量矩阵（行 = 三个扭量）：A i j = 第 i 个扭量的第 j 分量。 -/
def triMatrix (a b c : TriTwistor) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (match i with
    | ⟨0, _⟩ => a j
    | ⟨1, _⟩ => b j
    | _ => c j)

/-! ### GQ1. 三扭量外积和 = Aᵀ(Aᵀ)ᴴ -/

/-- ★ GQ1：三扭量外积和 = 列扭量矩阵与其共轭转置之积：
    P = Aᵀ·(Aᵀ)ᴴ（A 的行 = 三个扭量）。这使 det(P) 能写成
    det(A)·conj(det A) = |det₃[π₁ π₂ π₃]|²（GQ2）。 -/
theorem triple_outer_eq_conj_mul (a b c : TriTwistor) :
    tripleOuterSum a b c =
      (triMatrix a b c).transpose * (triMatrix a b c).transpose.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tripleOuterSum, triMatrix, Matrix.vecMulVec, Matrix.mul_apply,
          Matrix.conjTranspose, Fin.sum_univ_three] <;> ring

/-! ### GQ2. 三扭量 det 恒等（胶球质量 = 体积形式） -/

/-- ★ GQ2：三扭量 det 恒等——det₃(Σπᵢ⊗π̄ᵢ) = det A · conj(det A) =
    |det₃[π₁ π₂ π₃]|²（det(AA†) = |det A|²，Cauchy-Binet 的 N=3 特例）。
    胶球质量平方 = 三扭量的体积形式：三方向张满 ⟹ 非零。
    与电子的 det₂ = |⟨π₁,π₂⟩|²（TW6）同构：N 个扭量的 N×N 外积和
    的 det = |N 阶行列式|²——质量 = 扭量的 N 维辛体积。 -/
theorem triple_outer_det (a b c : TriTwistor) :
    Matrix.det (tripleOuterSum a b c) =
      Matrix.det (triMatrix a b c) * star (Matrix.det (triMatrix a b c)) := by
  rw [triple_outer_eq_conj_mul]
  rw [Matrix.det_mul]
  rw [Matrix.det_conjTranspose, Matrix.det_transpose]

/-! ### GQ3. 质量 ≠ 0 ⟺ 扭量矩阵 det ≠ 0 -/

/-- ★ GQ3：胶球质量平方 ≠ 0 ⟺ det₃[π₁ π₂ π₃] ≠ 0
    （ℂ 是域：det A · conj(det A) ≠ 0 ⟺ det A ≠ 0）。
    无质量（非激发）⟺ det 为零；有质量（激发）⟺ det 非零。 -/
theorem triple_mass_ne_zero_iff_det (a b c : TriTwistor) :
    Matrix.det (tripleOuterSum a b c) ≠ 0 ↔
      Matrix.det (triMatrix a b c) ≠ 0 := by
  rw [triple_outer_det]
  constructor
  · intro h hd
    apply h
    rw [hd]
    simp
  · intro hd
    have hs : star (Matrix.det (triMatrix a b c)) ≠ 0 := star_ne_zero.mpr hd
    exact mul_ne_zero hd hs

/-! ### GQ4. 激发 ⟺ 三扭量线性无关（秩 3 判据） -/

/-- ★ GQ4a：胶球激发（质量 ≠ 0）⟹ 三扭量线性无关（秩 3）——
    det₃ ≠ 0 ⟹ 行独立（mathlib）。三方向胶球的"激发 ⟹ 秩"判据：
    电子 = 两旋量独立（秩 2），胶球 = 三扭量独立（秩 3）。
    扭量张满 ⟹ 激发（质量）。 -/
theorem triple_excited_implies_independent (a b c : TriTwistor)
    (h : Matrix.det (tripleOuterSum a b c) ≠ 0) :
    LinearIndependent ℂ (fun i : Fin 3 => (triMatrix a b c) i) := by
  rw [triple_mass_ne_zero_iff_det] at h
  exact Matrix.linearIndependent_rows_of_det_ne_zero h

/-- ★ GQ4b：三扭量线性相关（秩 < 3）⟹ 非激发（质量 = 0）——
    ¬LI ⟹ det₃ = 0（mathlib）。退化方向：扭量不全独立 ⟹ 无质量。 -/
theorem triple_dependent_implies_massless (a b c : TriTwistor)
    (h : ¬ LinearIndependent ℂ (fun i : Fin 3 => (triMatrix a b c) i)) :
    Matrix.det (tripleOuterSum a b c) = 0 := by
  rw [triple_outer_det]
  have hd : Matrix.det (triMatrix a b c) = 0 :=
    Matrix.det_eq_zero_of_not_linearIndependent_rows h
  rw [hd]
  simp

/-! ### GQ5. 退化（两扭量相等）⟹ 无质量 -/

/-- ★ GQ5：两扭量相等（π₃ = π₂）⟹ det₃ = 0 ⟹ 无质量——
    三扭量退化到两扭量结构（秩 ≤ 2），"第三方向"不独立 = 非激发。
    胶球需要三个独立方向（秩 3）才有质量。 -/
theorem triple_degenerate_massless (a b : TriTwistor) :
    Matrix.det (tripleOuterSum a b b) = 0 := by
  rw [triple_outer_det]
  have hd : Matrix.det (triMatrix a b b) = 0 := by
    rw [Matrix.det_fin_three]
    simp [triMatrix]
    ring
  rw [hd]
  simp

/-! ### GQ6. 统一秩判据表（N = 1, 2, 3） -/

/-- ★ GQ6：统一秩判据——质量² = |det_N[π₁...π_N]|²：
    N=1（光子）：det₁[π₁⊗π̄₁] = π₁π̄₁ = |π₁|²（秩 1，非激发）；
    N=2（电子）：det₂ = |⟨π₁,π₂⟩|²（秩 2，激发，pairDet/QFT8）；
    N=3（胶球）：det₃ = |det₃[π₁π₂π₃]|²（秩 3，激发，GQ2）。
    一条链：质量 ⟺ 激发 ⟺ 扭量独立（秩 = 扭量数）——电子与胶球
    是同一判据的两个实例（2 维辛体积 vs 3 维体积形式）。 -/
theorem excitation_rank_unified (z a₁ b₁ a₂ b₂ : ℂ) (a b c : TriTwistor) :
    (Matrix.det !![z] = z) ∧
    (pairDet a₁ b₁ a₂ b₂ =
      (a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁)) ∧
    (Matrix.det (tripleOuterSum a b c) =
      Matrix.det (triMatrix a b c) *
        star (Matrix.det (triMatrix a b c))) := by
  constructor
  · exact Matrix.det_fin_one_of z
  constructor
  · rfl
  · exact triple_outer_det a b c

/-! ### 结论注释（三扭量胶球） -/

-- GQ1–GQ6 合读（三秩纠缠的判定）：
--   1. ★ 三扭量 det 恒等（GQ2）：det₃(Σπᵢ⊗π̄ᵢ) = |det₃[π₁ π₂ π₃]|²——
--      Cauchy-Binet 的 N=3 特例；胶球质量平方 = 三扭量体积形式。
--   2. ★ 秩判据（GQ3–GQ4）：激发 ⟺ det ≠ 0 ⟺ 三扭量线性无关（秩 3）；
--      退化（两扭量相等）⟹ 无质量（GQ5）。与电子（秩 2，QFT8）同构。
--   3. ★ 统一链（GQ6）：质量² = |det_N[π₁...π_N]|² 对 N = 1（光子）、
--      2（电子）、3（胶球）——"激发 ⟺ 秩 2"是"激发 ⟺ 秩 = 扭量数"
--      的特例；胶球 = 三扭量全纠缠（W 型：三对辛内积都贡献，数值 N13）。
--   4. 诚实边界：2×2 矩阵秩 ≤ 2，装不下三个独立方向——三方向胶球
--      必须用 3×3（色空间），这是"胶子生活在 SU(3)"的代数线索；
--      det₃ ≤ |π₁||π₂||π₃|（Hadamard，单位旋量时 ≤ 1）⟹ 三扭量
--      体积给出的是结构判据（秩 ⟺ 质量），√3·M₀ 格点谱仍由
--      方向锚定相加（MC6'）负责——两者是互补而非竞争。

/-! ### GQN1–GQN6. 一般 N 扭量：det(AA†) = |det A|²（Cauchy-Binet 方阵特例） -/

-- leo（2026-08-15 第三轮）：把 GQ2（N=3）推广到一般 N——N 个 N 维扭量的
-- 外积和 P = Σᵢ πᵢ⊗π̄ᵢ，det(P) = |det[π₁...π_N]|²。
-- 数学状态（诚实）：mathlib 无完整 Cauchy-Binet（矩形 m×n 的子式平方和），
-- 本轮形式化方阵特例 det(AA†) = |det A|²（Cauchy-Binet 在 m = n 时只剩
-- 唯一一项）——这正是"扭量数 = 空间维数"的激发条件；m < n 时 det = 0
-- （秩不足，非激发），m > n 的完整子式和未形式化（诚实标注）。
-- 物理统一链：质量² = |det_N[π₁...π_N]|² 对任意 N——光子（N=1，秩 1）、
-- 电子（N=2，秩 2）、胶球（N=3，秩 3）都是同一恒等的实例。

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- N 个 N 维扭量的外积和（分量空间矩阵）：Pᵢⱼ = Σₖ πₖᵢ·conj(πₖⱼ)。 -/
def outerSumN (f : N → N → ℂ) : Matrix N N ℂ :=
  fun i j => ∑ k : N, f k i * star (f k j)

/-- 扭量矩阵（行 = N 个扭量）：A i j = 第 i 个扭量的第 j 分量。 -/
def twistorMat (f : N → N → ℂ) : Matrix N N ℂ :=
  fun i j => f i j

/-! ### GQN1. 一般 N：外积和 = Aᵀ(Aᵀ)ᴴ -/

/-- ★ GQN1：N 扭量外积和 = 扭量矩阵与其共轭转置之积（一般 N）。
    P = Aᵀ·(Aᵀ)ᴴ（A i j = 第 i 个扭量的第 j 分量）——GQ1（N=3）
    是一般情形的特例；这是 det 恒等（GQN2）的前提。 -/
theorem outer_sum_eq_conj_mul (f : N → N → ℂ) :
    outerSumN f =
      (twistorMat f).transpose * (twistorMat f).transpose.conjTranspose := by
  ext i j
  simp [outerSumN, twistorMat, Matrix.mul_apply, Matrix.conjTranspose]

/-! ### GQN2. 一般 N：det(P) = |det A|²（Cauchy-Binet 方阵特例） -/

/-- ★ GQN2：一般 N 统一恒等——det(Σᵢ πᵢ⊗π̄ᵢ) = det A · conj(det A) =
    |detₙ[π₁...π_N]|²（det(AA†) = |det A|²，Cauchy-Binet 在 m = n 时的
    唯一项）。质量² = |N 阶行列式|² 对任意 N：光子（N=1）、电子（N=2，
    TW6）、胶球（N=3，GQ2）都是这一恒等的实例。 -/
theorem outer_sum_det (f : N → N → ℂ) :
    Matrix.det (outerSumN f) =
      Matrix.det (twistorMat f) * star (Matrix.det (twistorMat f)) := by
  rw [outer_sum_eq_conj_mul]
  rw [Matrix.det_mul]
  rw [Matrix.det_conjTranspose, Matrix.det_transpose]

/-! ### GQN3. 一般 N：质量 ≠ 0 ⟺ det ≠ 0 -/

/-- ★ GQN3：质量平方 ≠ 0 ⟺ detₙ[π₁...π_N] ≠ 0（ℂ 是域）。
    无质量（非激发）⟺ det 为零；有质量（激发）⟺ det 非零——任意 N。 -/
theorem outer_sum_det_ne_zero_iff (f : N → N → ℂ) :
    Matrix.det (outerSumN f) ≠ 0 ↔
      Matrix.det (twistorMat f) ≠ 0 := by
  rw [outer_sum_det]
  constructor
  · intro h hd
    apply h
    rw [hd]
    simp
  · intro hd
    have hs : star (Matrix.det (twistorMat f)) ≠ 0 := star_ne_zero.mpr hd
    exact mul_ne_zero hd hs

/-! ### GQN4. 一般 N：激发 ⟺ 秩 N -/

/-- ★ GQN4a：激发（质量 ≠ 0）⟹ N 扭量线性无关（秩 N）——任意 N。
    电子 = 两扭量独立（秩 2）、胶球 = 三扭量独立（秩 3）是 N = 2, 3 特例；
    统一判据：扭量张满 ⟹ 激发（质量）。 -/
theorem excited_implies_independent_N (f : N → N → ℂ)
    (h : Matrix.det (outerSumN f) ≠ 0) :
    LinearIndependent ℂ (fun i : N => (twistorMat f) i) := by
  rw [outer_sum_det_ne_zero_iff] at h
  exact Matrix.linearIndependent_rows_of_det_ne_zero h

/-- ★ GQN4b：N 扭量线性相关（秩 < N）⟹ 非激发（质量 = 0）——任意 N。
    退化方向：扭量不全独立 ⟹ 无质量（GQ4b 的一般化）。 -/
theorem dependent_implies_massless_N (f : N → N → ℂ)
    (h : ¬ LinearIndependent ℂ (fun i : N => (twistorMat f) i)) :
    Matrix.det (outerSumN f) = 0 := by
  rw [outer_sum_det]
  have hd : Matrix.det (twistorMat f) = 0 :=
    Matrix.det_eq_zero_of_not_linearIndependent_rows h
  rw [hd]
  simp

/-! ### GQN5. 统一链（N = 1, 2, 一般 N） -/

/-- ★ GQN5：统一秩判据表——质量² = |det_N[π₁...π_N]|²：
    N=1（光子）：det₁ = π₁π̄₁ = |π₁|²（秩 1，非激发）；
    N=2（电子）：det₂ = |⟨π₁,π₂⟩|²（秩 2，激发，pairDet/QFT8）；
    一般 N：detₙ = |detₙ[π₁...π_N]|²（秩 N，激发，GQN2）。
    一条链（任意 N）：质量 ⟺ 激发 ⟺ 扭量独立（秩 = 扭量数）。 -/
theorem rank_unified_general (z a₁ b₁ a₂ b₂ : ℂ) (f : N → N → ℂ) :
    (Matrix.det !![z] = z) ∧
    (pairDet a₁ b₁ a₂ b₂ =
      (a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁)) ∧
    (Matrix.det (outerSumN f) =
      Matrix.det (twistorMat f) * star (Matrix.det (twistorMat f))) := by
  constructor
  · exact Matrix.det_fin_one_of z
  constructor
  · rfl
  · exact outer_sum_det f

/-! ### GQN6. 一致性：GQ2（N=3 特例）= GQN2（一般 N） -/

/-- ★ GQN6a：三扭量外积和 = 一般 N 外积和的 N=3 实例（triMatrix 对应）。
    验证一般定理覆盖特例：GQN2 在 N=3 时精确还原 GQ2。 -/
theorem triple_outer_eq_general (a b c : TriTwistor) :
    tripleOuterSum a b c =
      outerSumN (fun i j => triMatrix a b c i j) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tripleOuterSum, outerSumN, triMatrix, Matrix.vecMulVec, Fin.sum_univ_three] <;> ring

/-- ★ GQN6b：det 一致性——GQ2 的 det₃ = 一般 N 恒等在 N=3 时的值。
    形式化验证："一般定理 ⟹ 特例"（GQN2 蕴含 GQ2）。 -/
theorem triple_det_eq_general_det (a b c : TriTwistor) :
    Matrix.det (tripleOuterSum a b c) =
      Matrix.det (outerSumN (fun i j => triMatrix a b c i j)) := by
  rw [triple_outer_eq_general]

/-! ### 结论注释（一般 N 扭量） -/

-- GQN1–GQN6 合读（Cauchy-Binet 方阵特例的判定）：
--   1. ★ 一般 N 统一恒等（GQN2）：det(Σᵢ πᵢ⊗π̄ᵢ) = |detₙ[π₁...π_N]|²——
--      det(AA†) = |det A|² 对任意 N；GQ2（N=3）、TW6（N=2）、det₁（N=1）
--      都是特例（GQN6 形式化验证 N=3 一致性）。
--   2. ★ 统一链（GQN3–GQN5）：质量² = |det_N|²，激发 ⟺ 秩 N——光子/电子/
--      胶球是同一恒等的三个实例（"激发 ⟺ 秩 = 扭量数"对任意 N）。
--   3. 诚实边界：mathlib 无完整 Cauchy-Binet（矩形 m×n 子式平方和），
--      本轮证 m = n 方阵特例；m < n（扭量数 < 维数）时 det(P) = 0（秩不足
--      非激发），m > n 的完整子式和未形式化——"扭量数 ≥ 维数且满秩"是
--      激发（质量）的必要条件，m = n 是 Cauchy-Binet 单项目恰好给出
--      |det A|² 的情形。

/-! ### GQM1–GQM3. 多扭量叠加（m > n）：Cauchy-Binet 子式平方和 -/

-- leo（2026-08-15 第四轮）：m = n 已证（GQN2）；现在 m > n——m 个扭量
-- 叠加在 n 维空间，det(P) = 所有 n×n 子式的模平方和（Cauchy-Binet）：
--   det(AA†) = Σ_{S ⊆ [m], |S| = n} |det(A[:, S])|²
-- 物理（我们的假设）：多扭量叠加的质量² = 所有 n 元子族的"子纠缠体积"
-- 平方和——全域纠缠 = 所有子结构的纠缠之和。
-- 数学状态（诚实）：mathlib 无完整 Cauchy-Binet（一般 Finset 版未形式化，
-- 数值 N16–N18 全维验证）；本轮形式化显式版：
--   GQM1 ★ n=2, m=3：det(p₁+p₂+p₃) = |⟨π₁,π₂⟩|²+|⟨π₁,π₃⟩|²+|⟨π₂,π₃⟩|²
--       （C(3,2) = 3 个子式——质量² = 每对半旋量的纠缠贡献之和）
--   GQM2 ★ n=2, m=3 激发判据：det ≠ 0 ⟺ 至少一对不平行
--   GQM3 n=3, m=4：det(P) = Σ_{4 个三元子族} |det₃[π_S]|²（分量展开）

/-- 三扭量（2 维）外积和：p = π₁π₁† + π₂π₂† + π₃π₃†（2×2 分量空间矩阵）。 -/
def tripleOuter2D (a₁ b₁ a₂ b₂ a₃ b₃ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ a₁ * star a₁ + a₂ * star a₂ + a₃ * star a₃,
      a₁ * star b₁ + a₂ * star b₂ + a₃ * star b₃ ;
      b₁ * star a₁ + b₂ * star a₂ + b₃ * star a₃,
      b₁ * star b₁ + b₂ * star b₂ + b₃ * star b₃ ]

/-- 三对辛内积平方和（C(3,2) = 3 个 2×2 子式）。 -/
def pairDetSum (a₁ b₁ a₂ b₂ a₃ b₃ : ℂ) : ℂ :=
  (a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁) +
  (a₁ * b₃ - a₃ * b₁) * star (a₁ * b₃ - a₃ * b₁) +
  (a₂ * b₃ - a₃ * b₂) * star (a₂ * b₃ - a₃ * b₂)

/-- 辅助：s·star s = (normSq s : ℂ)——ℂ 值模平方 = 非负实数嵌入。 -/
lemma mul_star_self_ofReal_normSq (s : ℂ) :
    s * star s = (Complex.normSq s : ℂ) := by
  apply Complex.ext <;> simp [Complex.normSq] <;> ring

/-- 辅助：非零 ⟹ s·star s ≠ 0（模平方的 ℂ 值非零）。 -/
lemma mul_star_self_ne_zero_of_ne_zero (s : ℂ) (h : s ≠ 0) : s * star s ≠ 0 := by
  rw [mul_star_self_ofReal_normSq]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Complex.normSq_pos.mpr h))

/-- 辅助：三项非负实数，一项 > 0 ⟹ 和 ≠ 0。 -/
lemma normSq_sum_ne_zero_of_one_pos {x y z : ℝ} (hx : 0 < x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) : x + y + z ≠ 0 := by
  linarith

/-- ★ GQM1：n=2, m=3 显式 Cauchy-Binet——det(p₁+p₂+p₃) =
    |⟨π₁,π₂⟩|² + |⟨π₁,π₃⟩|² + |⟨π₂,π₃⟩|²（C(3,2) = 3 个子式平方和）。
    多扭量叠加（2 维）的质量² = 所有对（i<j）的辛内积平方和——
    每对半旋量的纠缠贡献相加（QFT4"叠加质量加法"的纠缠版）。
    与 m = n（GQN2 单子式）对照：m > n 是子式平方和，m = n 是唯一项。 -/
theorem triple_outer_2d_det (a₁ b₁ a₂ b₂ a₃ b₃ : ℂ) :
    Matrix.det (tripleOuter2D a₁ b₁ a₂ b₂ a₃ b₃) =
      pairDetSum a₁ b₁ a₂ b₂ a₃ b₃ := by
  unfold tripleOuter2D pairDetSum
  rw [Matrix.det_fin_two]
  simp
  ring

/-- ★ GQM2：n=2, m=3 激发判据——det ≠ 0 ⟺ 至少一对辛内积非零
    （至少一对不平行）。多扭量叠加（2 维）的激发条件 = 任意一对
    半旋量纠缠：一对非零 ⟹ 质量 > 0；全部平行 ⟹ 无质量。 -/
theorem triple_outer_2d_excited_iff (a₁ b₁ a₂ b₂ a₃ b₃ : ℂ) :
    Matrix.det (tripleOuter2D a₁ b₁ a₂ b₂ a₃ b₃) ≠ 0 ↔
      (a₁ * b₂ - a₂ * b₁ ≠ 0) ∨ (a₁ * b₃ - a₃ * b₁ ≠ 0) ∨
        (a₂ * b₃ - a₃ * b₂ ≠ 0) := by
  rw [triple_outer_2d_det]
  unfold pairDetSum
  constructor
  · intro h
    by_contra hnone
    push_neg at hnone
    have hz : (a₁ * b₂ - a₂ * b₁) * star (a₁ * b₂ - a₂ * b₁) +
        (a₁ * b₃ - a₃ * b₁) * star (a₁ * b₃ - a₃ * b₁) +
        (a₂ * b₃ - a₃ * b₂) * star (a₂ * b₃ - a₃ * b₂) = 0 := by
      rw [hnone.1, hnone.2.1, hnone.2.2]
      simp
    exact h hz
  · intro h
    rcases h with h1 | h2 | h3
    · rw [mul_star_self_ofReal_normSq, mul_star_self_ofReal_normSq,
          mul_star_self_ofReal_normSq]
      have hn1 : 0 < Complex.normSq (a₁ * b₂ - a₂ * b₁) := Complex.normSq_pos.mpr h1
      have hn2 : 0 ≤ Complex.normSq (a₁ * b₃ - a₃ * b₁) := Complex.normSq_nonneg _
      have hn3 : 0 ≤ Complex.normSq (a₂ * b₃ - a₃ * b₂) := Complex.normSq_nonneg _
      have hs := normSq_sum_ne_zero_of_one_pos hn1 hn2 hn3
      simpa using (Complex.ofReal_ne_zero.mpr hs : ((Complex.normSq (a₁ * b₂ - a₂ * b₁) +
        Complex.normSq (a₁ * b₃ - a₃ * b₁) + Complex.normSq (a₂ * b₃ - a₃ * b₂) : ℝ) : ℂ) ≠ 0)
    · rw [mul_star_self_ofReal_normSq, mul_star_self_ofReal_normSq,
          mul_star_self_ofReal_normSq]
      have hn2 : 0 < Complex.normSq (a₁ * b₃ - a₃ * b₁) := Complex.normSq_pos.mpr h2
      have hn1 : 0 ≤ Complex.normSq (a₁ * b₂ - a₂ * b₁) := Complex.normSq_nonneg _
      have hn3 : 0 ≤ Complex.normSq (a₂ * b₃ - a₃ * b₂) := Complex.normSq_nonneg _
      have hs := normSq_sum_ne_zero_of_one_pos hn2 hn1 hn3
      simpa [add_comm, add_left_comm, add_assoc] using
        (Complex.ofReal_ne_zero.mpr hs : ((Complex.normSq (a₁ * b₃ - a₃ * b₁) +
          Complex.normSq (a₁ * b₂ - a₂ * b₁) + Complex.normSq (a₂ * b₃ - a₃ * b₂) : ℝ) : ℂ) ≠ 0)
    · rw [mul_star_self_ofReal_normSq, mul_star_self_ofReal_normSq,
          mul_star_self_ofReal_normSq]
      have hn3 : 0 < Complex.normSq (a₂ * b₃ - a₃ * b₂) := Complex.normSq_pos.mpr h3
      have hn1 : 0 ≤ Complex.normSq (a₁ * b₂ - a₂ * b₁) := Complex.normSq_nonneg _
      have hn2 : 0 ≤ Complex.normSq (a₁ * b₃ - a₃ * b₁) := Complex.normSq_nonneg _
      have hs := normSq_sum_ne_zero_of_one_pos hn3 hn1 hn2
      simpa [add_comm, add_left_comm, add_assoc] using
        (Complex.ofReal_ne_zero.mpr hs : ((Complex.normSq (a₂ * b₃ - a₃ * b₂) +
          Complex.normSq (a₁ * b₂ - a₂ * b₁) + Complex.normSq (a₁ * b₃ - a₃ * b₁) : ℝ) : ℂ) ≠ 0)

/-! ### GQM3. n=3, m=4：四扭量叠加（3 维）— 4 个三元子式平方和 -/

/-- 四扭量（3 维）外积和（3×3）：P = Σᵢ₌₁⁴ πᵢπᵢ†。 -/
def quadOuter3D (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![ a₁ * star a₁ + a₂ * star a₂ + a₃ * star a₃ + a₄ * star a₄,
      a₁ * star b₁ + a₂ * star b₂ + a₃ * star b₃ + a₄ * star b₄,
      a₁ * star c₁ + a₂ * star c₂ + a₃ * star c₃ + a₄ * star c₄ ;
      b₁ * star a₁ + b₂ * star a₂ + b₃ * star a₃ + b₄ * star a₄,
      b₁ * star b₁ + b₂ * star b₂ + b₃ * star b₃ + b₄ * star b₄,
      b₁ * star c₁ + b₂ * star c₂ + b₃ * star c₃ + b₄ * star c₄ ;
      c₁ * star a₁ + c₂ * star a₂ + c₃ * star a₃ + c₄ * star a₄,
      c₁ * star b₁ + c₂ * star b₂ + c₃ * star b₃ + c₄ * star b₄,
      c₁ * star c₁ + c₂ * star c₂ + c₃ * star c₃ + c₄ * star c₄ ]

/-- 3×3 行列式（Sarrus 展开，行 = 三个扭量）。 -/
def det₃ (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℂ) : ℂ :=
  a₁ * (b₂ * c₃ - c₂ * b₃) - b₁ * (a₂ * c₃ - c₂ * a₃) + c₁ * (a₂ * b₃ - b₂ * a₃)

/-- 四个 3×3 子式平方和（C(4,3) = 4 个子族）。 -/
def tripleDetSum4 (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ : ℂ) : ℂ :=
  (det₃ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃) * star (det₃ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃) +
  (det₃ a₁ b₁ c₁ a₂ b₂ c₂ a₄ b₄ c₄) * star (det₃ a₁ b₁ c₁ a₂ b₂ c₂ a₄ b₄ c₄) +
  (det₃ a₁ b₁ c₁ a₃ b₃ c₃ a₄ b₄ c₄) * star (det₃ a₁ b₁ c₁ a₃ b₃ c₃ a₄ b₄ c₄) +
  (det₃ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄) * star (det₃ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄)

/-- ★ GQM3：n=3, m=4 显式 Cauchy-Binet——det(P) =
    Σ_{S ⊆ {1..4}, |S|=3} |det₃[π_S]|²（C(4,3) = 4 个子式平方和）。
    四扭量叠加（3 维）的质量² = 所有三元子族的"子纠缠体积"平方和——
    全域纠缠 = 所有子结构的纠缠之和。 -/
theorem quad_outer_3d_det (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ : ℂ) :
    Matrix.det (quadOuter3D a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄) =
      tripleDetSum4 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ := by
  unfold quadOuter3D tripleDetSum4 det₃
  rw [Matrix.det_fin_three]
  simp
  ring

/-! ### 结论注释（多扭量叠加 Cauchy-Binet） -/

-- GQM1–GQM3 合读（m > n 的判定）：
--   1. ★ 显式 Cauchy-Binet（GQM1/GQM3）：多扭量叠加的质量² = 所有 n 元
--      子族的子式平方和——n=2, m=3 为三对辛内积和；n=3, m=4 为四个
--      三元体积平方和。m = n（GQN2）是唯一子式的特例。
--   2. ★ 激发判据（GQM2）：n=2, m=3 时 det ≠ 0 ⟺ 至少一对不平行——
--      叠加中任意一对半旋量纠缠即激发；全平行 ⟹ 无质量。
--   3. 诚实边界：一般 m,n 的 Finset 版 Cauchy-Binet mathlib 无且未形式化
--      （数值 N16–N18 全维验证）；GQM3 若分量展开过慢则降级为数值 +
--      注释（减法原则）。物理上这是标准线性代数恒等——框架贡献 =
--      "质量² = 全纠缠结构（所有子族体积平方和）"的解释层重述。

end ProjectionPhysics.QFTFlow

end
