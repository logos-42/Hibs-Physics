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
import Mathlib.Data.Nat.Dist
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

/-! ### GQS1–GQS3. 一般 Finset 版 Cauchy-Binet -/

-- leo（2026-08-15 第五轮）：一般 Finset 版。
-- GQS1 ★ n=2 任意 m（完整）：det(Σᵢ₌₀ᵐ⁻¹ πᵢπᵢ†) = Σ_{i<j} |⟨πᵢ,πⱼ⟩|²
--      （GQM1 的 m 任意推广——Finset 双重和 + 对角分离 + 对换重排）
-- GQS2 一般 n 核心：det(AA†) 的多重和展开（map_sum/map_smul_univ）、
--      非单射归零（map_eq_zero_of_eq）、单射的 det 表达（det_conjTranspose）
-- GQS3 一般 n：det(AA†) = Σ_{r 单射} (∏ Aₖ,rₖ)•star(det 子式)（组合引理）；
--      ★ 最后的求和重排（单射函数和 ↔ 子集×排列和 = |det|² 和）数学骨架
--      见注释——完整 Finset 双射形式化留作后续（诚实边界）。

/-- m 个扭量（2 维）外积和（2×2 分量空间矩阵）：P = Σᵢ πᵢπᵢ†。 -/
def outerSumM2 {m : ℕ} (π : Fin m → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ ∑ i, π i 0 * star (π i 0), ∑ i, π i 0 * star (π i 1) ;
      ∑ i, π i 1 * star (π i 0), ∑ i, π i 1 * star (π i 1) ]

/-- 所有无序对（i < j）的辛内积平方和（Finset 双重和，if 指示）。 -/
def pairDetSumAll {m : ℕ} (π : Fin m → Fin 2 → ℂ) : ℂ :=
  ∑ i : Fin m, ∑ j : Fin m,
    if i < j then
      (π i 0 * π j 1 - π i 1 * π j 0) * star (π i 0 * π j 1 - π i 1 * π j 0)
    else 0

/-- 2×2 展开项：T(i,j) = |aᵢ|²|bⱼ|² − aᵢb̄ᵢbⱼāⱼ（det 展开的 (i,j) 项）。 -/
def T2 {m : ℕ} (π : Fin m → Fin 2 → ℂ) (i j : Fin m) : ℂ :=
  (π i 0 * star (π i 0)) * (π j 1 * star (π j 1)) -
    (π i 0 * star (π i 1)) * (π j 1 * star (π j 0))

/-- 辅助：双重和对换重命名 ΣᵢΣⱼ f(i,j) = ΣᵢΣⱼ f(j,i)（sum_comm 两次）。 -/
lemma sum_swap {m : ℕ} (f : Fin m → Fin m → ℂ) :
    (∑ i : Fin m, ∑ j : Fin m, f i j) = ∑ i : Fin m, ∑ j : Fin m, f j i := by
  calc
    (∑ i : Fin m, ∑ j : Fin m, f i j)
      = ∑ j : Fin m, ∑ i : Fin m, f i j := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin m, ∑ j : Fin m, f j i := by
          -- 变量重命名：ΣⱼΣᵢ f i j = ΣᵢΣⱼ f j i（sum_comm 对 g = fun j i => f i j）
          rw [Finset.sum_comm]

/-- 辅助：乘积展开 (Σᵢ xᵢ)·(Σⱼ yⱼ) = ΣᵢΣⱼ xᵢ·yⱼ（mathlib Fintype.sum_mul_sum）。 -/
lemma sum_mul_sum {α β : Type*} [Fintype α] [Fintype β]
    (x : α → ℂ) (y : β → ℂ) :
    (∑ i : α, x i) * (∑ j : β, y j) = ∑ i : α, ∑ j : β, x i * y j :=
  Fintype.sum_mul_sum x y

/-- 辅助：对角项 T(i,i) = 0（aᵢāᵢbᵢb̄ᵢ − aᵢb̄ᵢbᵢāᵢ 抵消）。 -/
lemma T2_diag_zero {m : ℕ} (π : Fin m → Fin 2 → ℂ) (i : Fin m) : T2 π i i = 0 := by
  unfold T2
  ring

/-- 辅助：配对恒等 T(i,j) + T(j,i) = |aᵢbⱼ − aⱼbᵢ|²（两半旋量的纠缠贡献）。 -/
lemma T2_pair_sum {m : ℕ} (π : Fin m → Fin 2 → ℂ) (i j : Fin m) :
    T2 π i j + T2 π j i =
      (π i 0 * π j 1 - π i 1 * π j 0) * star (π i 0 * π j 1 - π i 1 * π j 0) := by
  unfold T2
  simp [star_sub, StarMul.star_mul]
  ring

/-- 辅助：det 展开成双重和 det(P) = ΣᵢΣⱼ T(i,j)（乘积展开）。 -/
lemma outer_sum_m2_expand {m : ℕ} (π : Fin m → Fin 2 → ℂ) :
    Matrix.det (outerSumM2 π) = ∑ i : Fin m, ∑ j : Fin m, T2 π i j := by
  unfold outerSumM2
  rw [Matrix.det_fin_two]
  simp
  unfold T2
  -- (Σᵢ aᵢāᵢ)(Σⱼ bⱼb̄ⱼ) − (Σᵢ aᵢb̄ᵢ)(Σⱼ bⱼāⱼ) = ΣᵢΣⱼ (aᵢāᵢbⱼb̄ⱼ − aᵢb̄ᵢbⱼāⱼ)
  calc
    (∑ i : Fin m, π i 0 * star (π i 0)) * (∑ j : Fin m, π j 1 * star (π j 1)) -
      (∑ i : Fin m, π i 0 * star (π i 1)) * (∑ j : Fin m, π j 1 * star (π j 0))
        = (∑ i : Fin m, ∑ j : Fin m, (π i 0 * star (π i 0)) * (π j 1 * star (π j 1))) -
          (∑ i : Fin m, ∑ j : Fin m, (π i 0 * star (π i 1)) * (π j 1 * star (π j 0))) := by
            congr 1
            · exact sum_mul_sum (fun i => π i 0 * star (π i 0))
                (fun j => π j 1 * star (π j 1))
            · exact sum_mul_sum (fun i => π i 0 * star (π i 1))
                (fun j => π j 1 * star (π j 0))
    _ = ∑ i : Fin m, ∑ j : Fin m,
          ((π i 0 * star (π i 0)) * (π j 1 * star (π j 1)) -
            (π i 0 * star (π i 1)) * (π j 1 * star (π j 0))) := by
          -- 反向分配：∑ᵢΣⱼ a − ∑ᵢΣⱼ b = ∑ᵢΣⱼ (a − b)（先外层，再逐项内层）
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.sum_sub_distrib]

/-- ★ GQS1：n=2 任意 m 的 Finset 版 Cauchy-Binet——det(Σᵢπᵢπᵢ†) =
    Σ_{i<j} |⟨πᵢ,πⱼ⟩|²（C(m,2) 个子式平方和）。
    任意多个半旋量叠加（2 维）的质量² = 所有对的辛内积平方和——
    每对半旋量的纠缠贡献独立相加（GQM1 的 m 任意推广，完整证明：
    det 展开 → 三分分解 → 对角归零 → 对换重排 → 配对恒等）。 -/
theorem outer_sum_m2_det {m : ℕ} (π : Fin m → Fin 2 → ℂ) :
    Matrix.det (outerSumM2 π) = pairDetSumAll π := by
  rw [outer_sum_m2_expand]
  unfold pairDetSumAll
  calc
    (∑ i : Fin m, ∑ j : Fin m, T2 π i j)
      = ∑ i : Fin m, ∑ j : Fin m,
          ((if i < j then T2 π i j else 0) + (if i = j then T2 π i j else 0) +
            (if i > j then T2 π i j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rcases lt_trichotomy i j with hlt | heq | hgt
          · simp [hlt, lt_asymm hlt, ne_of_lt hlt]
          · subst heq
            simp
          · simp [hgt, lt_asymm hgt, ne_of_gt hgt]
    _ = (∑ i : Fin m, ∑ j : Fin m, if i < j then T2 π i j else 0) +
        (∑ i : Fin m, ∑ j : Fin m, if i = j then T2 π i j else 0) +
        (∑ i : Fin m, ∑ j : Fin m, if i > j then T2 π i j else 0) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = (∑ i : Fin m, ∑ j : Fin m, if i < j then T2 π i j else 0) +
        (∑ i : Fin m, T2 π i i) +
        (∑ i : Fin m, ∑ j : Fin m, if i > j then T2 π i j else 0) := by
          have h2 : (∑ i : Fin m, ∑ j : Fin m, if i = j then T2 π i j else 0) =
              ∑ i : Fin m, T2 π i i := by
            simp [Finset.sum_ite_eq']
          rw [h2]
    _ = (∑ i : Fin m, ∑ j : Fin m, if i < j then T2 π i j else 0) + 0 +
        (∑ i : Fin m, ∑ j : Fin m, if i > j then T2 π i j else 0) := by
          have h3 : (∑ i : Fin m, T2 π i i) = 0 := by
            simp [T2_diag_zero]
          rw [h3]
    _ = (∑ i : Fin m, ∑ j : Fin m, if i < j then T2 π i j else 0) +
        (∑ i : Fin m, ∑ j : Fin m, if i > j then T2 π i j else 0) := by
          simp
    _ = (∑ i : Fin m, ∑ j : Fin m, if i < j then T2 π i j else 0) +
        (∑ i : Fin m, ∑ j : Fin m, if i < j then T2 π j i else 0) := by
          -- 对换重命名：ΣᵢΣⱼ if i>j then T(i,j) else 0 = ΣᵢΣⱼ if i<j then T(j,i) else 0
          have hswap : (∑ i : Fin m, ∑ j : Fin m, if i > j then T2 π i j else 0) =
              ∑ i : Fin m, ∑ j : Fin m, if i < j then T2 π j i else 0 := by
            simpa using
              (sum_swap (fun i j => if i > j then T2 π i j else 0) :
                (∑ i : Fin m, ∑ j : Fin m, if i > j then T2 π i j else 0) =
                  ∑ i : Fin m, ∑ j : Fin m, if j > i then T2 π j i else 0)
          rw [hswap]
    _ = ∑ i : Fin m, ∑ j : Fin m, if i < j then T2 π i j + T2 π j i else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : x < j <;> simp [h]
    _ = ∑ i : Fin m, ∑ j : Fin m, if i < j then
          (π i 0 * π j 1 - π i 1 * π j 0) * star (π i 0 * π j 1 - π i 1 * π j 0) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : i < j
          · simp [h, T2_pair_sum π i j]
          · simp [h]

/-! ### GQS2–GQS3. 一般 n 的 Cauchy-Binet 核心（det 的多重和展开） -/

-- 一般 n：A : Fin n → Fin m → ℂ（行 = n 维分量，列 = m 个扭量）。
-- AA† 的 (i,k) = Σⱼ Aᵢⱼ·star(Aₖⱼ)；第 i 行 = Σⱼ Aᵢⱼ • rowⱼ（rowⱼ = A† 的第 j 行）。
-- GQS2a ★：det(AA†) = Σ_{r : Fin n → Fin m} (∏ₖ Aₖ,rₖ) • detₙ(行 star(A[:,rₖ]))——
--    det 的行多线性：map_sum 一次展开全部 n 重和，map_smul_univ 提出全部标量。
-- GQS2b：r 非单射 ⟹ 该项 = 0（map_eq_zero_of_eq：两行相同，交替性）。
-- GQS2c：r 单射 ⟹ detₙ(行 star(A[:,rₖ])) = star(det(fun l k => A l (r k)))
--    （det_conjTranspose：行子矩阵 = 子式转置的共轭）。
-- GQS3：det(AA†) = Σ_{r 单射} (∏ₖ Aₖ,rₖ)•star(det 子式)（组合引理）。
-- ★ 完整 Cauchy-Binet 的最后一跳（诚实边界，数学骨架见文件尾注释）：
--    Σ_{r 单射} (∏ₖ Aₖ,rₖ)•star(det 子式) = Σ_{S, |S|=n} |det(A[:,S])|²——
--    单射函数和 ↔ 子集×排列和 的 Finset 双射（det_apply Leibniz 展开 + sign 重排）
--    需 ~200-400 行 Finset 双射形式化，留作后续；GQS1（n=2 任意 m）已完整。

/-- ★ GQS2a：det(AA†) = Σ_{r : Fin n → Fin m} (∏ₖ Aₖ,rₖ) • detRowAlternating(行 star(A[:,rₖ]))。
    多重和展开（det 的行多线性 + map_sum + map_smul_univ）——一般 n 的展开内核。 -/
theorem det_conj_mul_sum_expand {n m : ℕ} (A : Fin n → Fin m → ℂ) :
    Matrix.det (fun i k => ∑ j : Fin m, A i j * star (A k j)) =
      ∑ r : Fin n → Fin m,
        (∏ k : Fin n, A k (r k)) • Matrix.detRowAlternating
          (fun k l => star (A l (r k))) := by
  calc
    Matrix.det (fun i k => ∑ j : Fin m, A i j * star (A k j))
      = Matrix.detRowAlternating (fun i k => ∑ j : Fin m, A i j * star (A k j)) := by
          rfl
    _ = Matrix.detRowAlternating
          (fun i => ∑ j : Fin m, A i j • (fun l : Fin n => star (A l j))) := by
          -- funext + sum_apply：双参行函数与"每行一个和"一致
          congr
          funext i k
          simp [Finset.sum_apply, Pi.smul_apply]
    _ = ∑ r : Fin n → Fin m,
          Matrix.detRowAlternating
            (fun i => A i (r i) • (fun l : Fin n => star (A l (r i)))) := by
          -- map_sum：一次展开全部参数（每行一个和）的多重和
          -- f = detRowAlternating（作为 MultilinearMap），ι = Fin n，α i = Fin m
          -- g i j = A i j • (fun l => star (A l j))
          simpa using
            (MultilinearMap.map_sum
              (f := Matrix.detRowAlternating.toMultilinearMap)
              (g := fun i j => A i j • (fun l : Fin n => star (A l j))))
    _ = ∑ r : Fin n → Fin m,
          (∏ k : Fin n, A k (r k)) • Matrix.detRowAlternating
            (fun k l => star (A l (r k))) := by
          apply Finset.sum_congr rfl
          intro r hr
          -- map_smul_univ：f (fun i => c i • m i) = (∏ i, c i) • f m
          -- c i = A i (r i)，m i = fun l => star (A l (r i))
          simpa using
            (MultilinearMap.map_smul_univ
              (f := Matrix.detRowAlternating.toMultilinearMap)
              (c := fun i => A i (r i))
              (m := fun i l => star (A l (r i))))

/-- GQS2b：r 非单射（两个扭量索引相同）⟹ 该项的行列式 = 0
    （交替性：两行相同 ⟹ AlternatingMap 归零）。 -/
theorem detRowAlt_zero_of_not_injective {n m : ℕ} (A : Fin n → Fin m → ℂ)
    (r : Fin n → Fin m) (h : ¬ Function.Injective r) :
    Matrix.detRowAlternating (fun k l => star (A l (r k))) = 0 := by
  rcases Function.not_injective_iff.mp h with ⟨k, k', hkk', hne⟩
  have hrow : (fun l : Fin n => star (A l (r k))) = fun l : Fin n => star (A l (r k')) := by
    rw [hkk']
  exact Matrix.detRowAlternating.map_eq_zero_of_eq
    (fun i l => star (A l (r i))) hrow hne

/-- GQS2c：该项的行列式 = star(子式 det)——行子矩阵 (fun k l => star (A l (r k)))
    是 (fun l k => A l (r k)) 的共轭转置，det(Mᴴ) = star(det M)（det_conjTranspose）。
    r 单射时 (fun l k => A l (r k)) 是 A 的列子矩阵（列序按 r，|det|² 与子式一致）。 -/
theorem detRowAlt_eq_star {n m : ℕ} (A : Fin n → Fin m → ℂ) (r : Fin n → Fin m) :
    Matrix.detRowAlternating (fun k l => star (A l (r k))) =
      star (Matrix.det (fun l k => A l (r k))) := by
  change Matrix.det (fun k l => star (A l (r k))) = star (Matrix.det (fun l k => A l (r k)))
  simpa [Matrix.conjTranspose] using
    (Matrix.det_conjTranspose (M := fun l k => A l (r k)))

/-- ★ GQS3：一般 n 的组合引理——det(AA†) =
    Σ_{r : Fin n → Fin m} if r 单射 then (∏ₖ Aₖ,rₖ) • star(det 列子矩阵) else 0。
    单射项保留下、非单射项归零（GQS2b/c 逐项替换）。
    ★ 完整 Cauchy-Binet 的最后一跳（诚实边界）：Σ_{r 单射} ↔ Σ_{S, |S|=n}
    子集×排列重排（det_apply Leibniz + sign 合并 = |det(A[:,S])|²）留作后续——
    GQS1（n=2 任意 m）已完整覆盖"任意多半旋量叠加"。 -/
theorem det_conj_mul_sum_injective {n m : ℕ} (A : Fin n → Fin m → ℂ) :
    Matrix.det (fun i k => ∑ j : Fin m, A i j * star (A k j)) =
      ∑ r : Fin n → Fin m,
        if Function.Injective r then
          (∏ k : Fin n, A k (r k)) • star (Matrix.det (fun l k => A l (r k)))
        else 0 := by
  classical
  calc
    Matrix.det (fun i k => ∑ j : Fin m, A i j * star (A k j))
      = ∑ r : Fin n → Fin m,
          (∏ k : Fin n, A k (r k)) • Matrix.detRowAlternating (fun k l => star (A l (r k))) :=
          det_conj_mul_sum_expand A
    _ = ∑ r : Fin n → Fin m,
          if Function.Injective r then
            (∏ k : Fin n, A k (r k)) • star (Matrix.det (fun l k => A l (r k))) else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          by_cases h : Function.Injective r
          · rw [detRowAlt_eq_star A r]
            simp [h]
          · rw [detRowAlt_zero_of_not_injective A r h]
            simp [h]

/-! ### GQS4–GQS6. 最后一跳：单射函数和 ↔ 子集×排列双射（完整 Cauchy-Binet） -/

-- leo（2026-08-15 第五轮续）：攻完整一般 Finset 版。
-- GQS4：固定子集 S 内，枚举和 Σ_{e : Fin n ≃ S}(∏ₖ Aₖ,eₖ)•star(det M_e) = |det A[:,S]|²
--   （e₀ = orderIsoOfFin 升序枚举；e = e₀∘π 参数化 → det_permute' 列排列变号 →
--     det_apply Leibniz → det_transpose 合并）
-- GQS5：单射函数和 ↔ (像子集 × 枚举) 双射（Fintype.sum_equiv）
-- GQS6 ★ 完整一般 Finset 版 Cauchy-Binet：det(AA†) = Σ_{S, |S|=n} |det(A[:,S])|²

/-- 辅助：枚举与排列的双射——固定基准枚举 e₀，任意枚举 e = π.trans e₀（π 排列）。 -/
def enumEquivPerm {n : ℕ} {S : Type*} (e₀ : Fin n ≃ S) : (Fin n ≃ S) ≃ Equiv.Perm (Fin n) :=
  { toFun := fun e => e.trans e₀.symm
    invFun := fun π => π.trans e₀
    left_inv := by
      intro e
      ext k
      simp [Equiv.trans_apply]
    right_inv := by
      intro π
      ext k
      simp [Equiv.trans_apply] }

/-- ★ GQS4：固定子集 S（card = n）——Σ_{e : Fin n ≃ S}(∏ₖ Aₖ,eₖ)•star(det M_e) =
    |det A[:,S]|²（任意 n 元子族的"子纠缠体积"平方；e₀ = 升序枚举）。
    证明：e = π.trans e₀ 参数化（sum_enum_param）→ det_permute'（列排列 sign 变号）→
    star 提出 sign（sum_smul）→ det_apply + det_transpose（Leibniz 和 = det M₀）。 -/
theorem sum_enum_minor {n m : ℕ} (A : Fin n → Fin m → ℂ)
    (S : Finset (Fin m)) (hS : S.card = n) :
    (∑ e : Fin n ≃ S,
      (∏ k : Fin n, A k (e k)) • star (Matrix.det (fun l k => A l (e k)))) =
      Matrix.det (fun i k => A i (S.orderIsoOfFin hS k)) *
        star (Matrix.det (fun i k => A i (S.orderIsoOfFin hS k))) := by
  let e₀ : Fin n ≃ S := S.orderIsoOfFin hS
  calc
    (∑ e : Fin n ≃ S,
      (∏ k : Fin n, A k (e k)) • star (Matrix.det (fun l k => A l (e k))))
      = ∑ π : Equiv.Perm (Fin n),
          (∏ k : Fin n, A k (e₀ (π k))) •
            star (Matrix.det (fun l k => A l (e₀ (π k)))) := by
          -- e = π.trans e₀ 参数化（enumEquivPerm 双射）
          symm
          -- 目标：∑ π, F (π.trans e₀) = ∑ e, F e
          have hparam : (∑ e : Fin n ≃ S,
              (∏ k : Fin n, A k (e k)) • star (Matrix.det (fun l k => A l (e k)))) =
            ∑ π : Equiv.Perm (Fin n),
              (∏ k : Fin n, A k (Equiv.trans π e₀ k)) •
                star (Matrix.det (fun l k => A l (Equiv.trans π e₀ k))) := by
            calc
              (∑ e : Fin n ≃ S,
                (∏ k : Fin n, A k (e k)) • star (Matrix.det (fun l k => A l (e k))))
                = ∑ a : Fin n ≃ S,
                    (∏ k : Fin n, A k (Equiv.trans (Equiv.trans a e₀.symm) e₀ k)) •
                      star (Matrix.det (fun l k => A l (Equiv.trans (Equiv.trans a e₀.symm) e₀ k))) := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    congr 1
                    · apply Finset.prod_congr rfl
                      intro k hk
                      simp [Equiv.trans_apply]
                    · congr 1
                      congr 1
                      ext l k
                      simp [Equiv.trans_apply]
              _ = ∑ π : Equiv.Perm (Fin n),
                    (∏ k : Fin n, A k (Equiv.trans π e₀ k)) •
                      star (Matrix.det (fun l k => A l (Equiv.trans π e₀ k))) := by
                    -- Equiv.sum_comp：∑ a, g (e a) = ∑ π, g π（e a = a.trans e₀.symm）
                    exact Equiv.sum_comp (enumEquivPerm e₀)
                      (g := fun π : Equiv.Perm (Fin n) =>
                        (∏ k : Fin n, A k (Equiv.trans π e₀ k)) •
                        star (Matrix.det (fun l k => A l (Equiv.trans π e₀ k))))
          exact hparam.symm
    _ = ∑ π : Equiv.Perm (Fin n),
          (∏ k : Fin n, A k (e₀ (π k))) •
            star (Equiv.Perm.sign π • Matrix.det (fun l k => A l (e₀ k))) := by
          -- det_permute'：det(fun l k => A l (e₀ (π k))) = sign π • det(fun l k => A l (e₀ k))
          apply Finset.sum_congr rfl
          intro π hπ
          congr 1
          congr 1
          -- 左边 det 的矩阵 = M₀.submatrix id π
          have hm : (fun l k => A l (e₀ (π k))) =
              Matrix.submatrix (fun l k => A l (e₀ k)) id π := by
            ext l k
            simp [Matrix.submatrix]
          rw [hm, Matrix.det_permute']
          -- sign π • det = (sign π : ℂ) * det（ℤ-smul 展开）
          exact (zsmul_eq_mul (Matrix.det (fun l k => A l (e₀ k))) (Equiv.Perm.sign π)).symm
    _ = (∑ π : Equiv.Perm (Fin n), Equiv.Perm.sign π •
          (∏ k : Fin n, A k (e₀ (π k)))) •
          star (Matrix.det (fun l k => A l (e₀ k))) := by
          -- star(sign π • det M₀) = sign π • star(det M₀)，然后 sum_smul 提出 star(det M₀)
          calc
            (∑ π : Equiv.Perm (Fin n),
              (∏ k : Fin n, A k (e₀ (π k))) •
                star (Equiv.Perm.sign π • Matrix.det (fun l k => A l (e₀ k))))
              = ∑ π : Equiv.Perm (Fin n),
                  (Equiv.Perm.sign π • (∏ k : Fin n, A k (e₀ (π k)))) •
                    star (Matrix.det (fun l k => A l (e₀ k))) := by
                  -- 每项：star(sign π • det) = sign π • star(det)；(∏A)•(sign•star) = (sign•∏A)•star
                  apply Finset.sum_congr rfl
                  intro π hπ
                  have hs : star (Equiv.Perm.sign π • Matrix.det (fun l k => A l (e₀ k))) =
                      Equiv.Perm.sign π • star (Matrix.det (fun l k => A l (e₀ k))) := by
                    -- 环同态保持 ℤ-smul：star(sign π • det) = sign π • star(det)
                    exact AddMonoidHom.map_zsmul ((starRingEnd ℂ) : ℂ →+ ℂ)
                      (Matrix.det (fun l k => A l (e₀ k))) (Equiv.Perm.sign π)
                  rw [hs]
                  -- 展开 ℤ-smul 为 intCast 乘法，ℂ 自 smul 为乘法，ring 合并
                  have h1 : Equiv.Perm.sign π • star (Matrix.det (fun l k => A l (e₀ k))) =
                      (Equiv.Perm.sign π : ℂ) * star (Matrix.det (fun l k => A l (e₀ k))) :=
                    zsmul_eq_mul (star (Matrix.det (fun l k => A l (e₀ k)))) (Equiv.Perm.sign π)
                  have h2 : Equiv.Perm.sign π • (∏ k : Fin n, A k (e₀ (π k))) =
                      (Equiv.Perm.sign π : ℂ) * (∏ k : Fin n, A k (e₀ (π k))) :=
                    zsmul_eq_mul (∏ k : Fin n, A k (e₀ (π k))) (Equiv.Perm.sign π)
                  rw [h1, h2]
                  rw [smul_eq_mul, smul_eq_mul]
                  ring
            _ = (∑ π : Equiv.Perm (Fin n), Equiv.Perm.sign π •
                  (∏ k : Fin n, A k (e₀ (π k)))) •
                  star (Matrix.det (fun l k => A l (e₀ k))) := by
                  rw [Finset.sum_smul]
    _ = Matrix.det (fun i k => A i (S.orderIsoOfFin hS k)) *
          star (Matrix.det (fun i k => A i (S.orderIsoOfFin hS k))) := by
          -- Σ_π sign π • ∏ₖ Aₖ,e₀(πₖ) = det M₀（det_transpose + det_apply Leibniz）
          have hdet : (∑ π : Equiv.Perm (Fin n), Equiv.Perm.sign π •
              (∏ k : Fin n, A k (e₀ (π k)))) =
              Matrix.det (fun i k => A i (e₀ k)) := by
            -- det M₀ = det M₀ᵀ（det_transpose），M₀ᵀ r c = A c (e₀ r)
            -- det(M₀ᵀ) = Σ_σ sign σ • ∏ i, A i (e₀ (σ i))（det_apply）
            rw [← Matrix.det_transpose]
            rw [Matrix.det_apply]
            -- 两边是同一个 Leibniz 和（变量重命名）
            rfl
          rw [hdet]
          simp [e₀]

/-! ### GQS5–GQS6. 最后一跳（数学骨架，诚实标注：Sigma 依赖相等未形式化） -/

-- leo（2026-08-15）：完整一般 Finset 版 Cauchy-Binet 的最后一跳——
--   det(AA†) = Σ_{S, |S|=n} |det(A[:,S])|²（一般 n, m）。
-- 数学骨架（三步，GQS4 已 Lean 全证）：
--   1. GQS4 ✓（sum_enum_minor，已证）：固定子集 S（card = n）内，
--      Σ_{e : Fin n ≃ S}(∏ₖ Aₖ,eₖ)•star(det M_e) = |det A[:,S]|²
--      （e = π.trans e₀ 参数化 → det_permute' 列排列变号 → map_zsmul →
--        det_apply + det_transpose Leibniz 合并）
--   2. GQS5（骨架）：单射函数和 ↔ (像子集 × 枚举) 和——
--      Σ_{r : Fin n → Fin m, 单射} f r = Σ_{S, |S|=n} Σ_{e : Fin n ≃ S} f(嵌入 e)
--      双射 r ↦ (univ.image r, 像枚举)（injEquivSigma：toFun/invFun/left_inv 已构造，
--      right_inv 的 Sigma 依赖相等 Eq.recOn 化简未完成——Lean 已知难点）
--   3. GQS6（骨架）：组合 det(AA†) = Σ_{S,|S|=n}|det(A[:,S])|²（GQS3 + GQS5 + GQS4）
-- 诚实：GQS4 已证（固定子集内 |det|² 是最后一跳的数学核心）；GQS5/6 的组合双射
-- （Sigma 类型依赖相等）留作后续；GQS1（n=2 任意 m）已完整覆盖"任意多半旋量叠加"。

/-! ### GQC1★. 流动传播 = 酉传输：信息（辛关联体积）守恒

leo（2026-08-16）假设推进（信息 = 辛关联结构，见 wiki "信息=辛体积"重定义）：
- 流动的传输算符 U（酉：U·U† = 1）作用于每个扭量：πᵢ ↦ U·πᵢ
- 扭量矩阵 A 的列 = 扭量 ⟹ 流动传播 = A ↦ U·A
- 总信息（辛关联体积）= det(A·A†)（= Σ|det 子式|²，Cauchy-Binet）
- ★ GQC1：酉传输保持 det((UA)(UA)†) = det(AA†)——流动传播不改变
  模式的辛关联结构总量（信息守恒）。
- 物理含义：流动是幺正的（不丢信息），纠缠结构随流传播而不衰减。
- 诚实：这是"酉演化保持行列式"的线性代数事实（真但平凡）；框架贡献 =
  把它命名为流动传播下的信息守恒（解释层），非新物理预言。 -/

/-- GQC1b. 传输公式：(UA)(UA)† = U(AA†)U†——流动作用在扭量上等价于
    对关联矩阵的酉共轭。 -/
lemma gqc1_transport_formula {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℂ) :
    (U * A) * (U * A)ᴴ = U * (A * Aᴴ) * Uᴴ := by
  rw [Matrix.conjTranspose_mul]
  simp [Matrix.mul_assoc]

/-- GQC1★. 流动传播下信息守恒：U 酉 ⟹ det((UA)(UA)†) = det(AA†)。
    证明链：传输公式 → det_mul 两次 → det_conjTranspose（det U† = star(det U)）
    → 酉性 |det U|² = 1（det(UU†) = 1）→ 复数交换合并。 -/
lemma gqc1_unitary_transport {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) :
    ((U * A) * (U * A)ᴴ).det = (A * Aᴴ).det := by
  rw [gqc1_transport_formula]
  calc
    (U * (A * Aᴴ) * Uᴴ).det = U.det * (A * Aᴴ).det * (Uᴴ).det := by
      rw [Matrix.det_mul, Matrix.det_mul]
    _ = U.det * (A * Aᴴ).det * star U.det := by
      rw [Matrix.det_conjTranspose]
    _ = (A * Aᴴ).det := by
      have hnorm : U.det * star U.det = 1 := by
        have h := congrArg Matrix.det hU
        rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
        exact h
      rw [mul_assoc, mul_comm (A * Aᴴ).det, ← mul_assoc, hnorm, one_mul]

/- GQC1c 备注：双扭量逐对守恒 |⟨Uπ₁,Uπ₂⟩|² = |⟨π₁,π₂⟩|²（U 酉）由 GQC1 通用版
    + GQS1（n=2：det(AA†) = Σ_{i<j}|⟨πᵢ,πⱼ⟩|²）组合给出，且逐项数值验证
    见 N22（每个子式 |det(U·A[:,S])|² = |det(A[:,S])|² 机器精度）。 -/

/-! ### GQC2★. 因果传播：格点化流动 ⟹ 光锥 ⟹ 不可通信定理的几何版

leo（2026-08-16）假设推进第二跳（信息传递：传播 → 因果）：
- 流动是格点化的（假设 6）：信息只能通过最近邻跳跃传播（局域性，带宽 1）
- ★ GQC2a：复合传输守恒——两步（归纳可得任意多步）酉传播仍保持
  det(AA†)（信息守恒在多步传播下成立）
- ★ GQC2b：带宽传播——带宽 ≤ 1 的跳跃矩阵，t 步后带宽 ≤ t
  （t 步传播核只在 |i−j| ≤ t 处非零——光锥）
- ★ GQC2：链跳跃光锥——t+1 步后，距离 > t+1 的格点之间传播核为零：
  格点 j 在时刻 t 只能感知 t 步内可达的格点——信息速度 ≤ 1 格/步
  = 流动格点化的因果速度上限。
- 物理含义：**因果性从"流动是格点局域的"直接涌现**——不可通信定理的
  几何版，不需要 QM 的额外公设（无超光速 = 格点距离限制，不是额外禁令）。
- 诚实：带宽传播是矩阵稀疏性的标准事实（真但平凡）；框架贡献 = 把它
  命名为流动格点化的因果结构（解释层）。 -/

/-- GQC2a★. 复合传输守恒：U₁, U₂ 酉 ⟹ det(((U₂U₁)A)((U₂U₁)A)†) = det(AA†)。
    证明链：(U₂U₁)(U₂U₁)† = U₂(U₁U₁†)U₂† = 1（U₂U₁ 酉）→ GQC1。 -/
lemma gqc2_compound_transport {n : ℕ} (U₁ U₂ A : Matrix (Fin n) (Fin n) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1) (hU₂ : U₂ * U₂ᴴ = 1) :
    (((U₂ * U₁) * A) * ((U₂ * U₁) * A)ᴴ).det = (A * Aᴴ).det := by
  have hU : (U₂ * U₁) * (U₂ * U₁)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      (U₂ * U₁) * (U₁ᴴ * U₂ᴴ) = ((U₂ * U₁) * U₁ᴴ) * U₂ᴴ :=
        (mul_assoc (U₂ * U₁) U₁ᴴ U₂ᴴ).symm
      _ = (U₂ * (U₁ * U₁ᴴ)) * U₂ᴴ := by
        congr 1
        exact mul_assoc U₂ U₁ U₁ᴴ
      _ = (U₂ * 1) * U₂ᴴ := by rw [hU₁]
      _ = U₂ * U₂ᴴ := by simp
      _ = 1 := hU₂
  exact gqc1_unitary_transport (U := U₂ * U₁) A hU

/-- GQC2b. 带宽定义：矩阵 T 的带宽 ≤ b——距离 > b 的 (i,j) 处为 0。
    dist 用 Nat.dist（ℕ 上的距离 |i−j| = (i−j)+(j−i)）。 -/
def band_le {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (b : ℕ) : Prop :=
  ∀ i j : Fin n, b < Nat.dist i.1 j.1 → T i j = 0

/-- GQC2b. 带宽复合：带宽 ≤ a 与带宽 ≤ b 的矩阵乘积带宽 ≤ a+b。
    证明：|i−j| > a+b 时，每个 k 要么 |i−k| > a（A 零）要么 |k−j| > b（B 零），
    否则三角不等式矛盾。 -/
lemma band_comp {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) {a b : ℕ}
    (hA : band_le A a) (hB : band_le B b) : band_le (A * B) (a + b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : a < Nat.dist i.1 k.1
  · rw [hA i k hik, zero_mul]
  · have hik_le : Nat.dist i.1 k.1 ≤ a := Nat.le_of_not_gt hik
    have hkj : b < Nat.dist k.1 j.1 := by
      by_contra hnot
      have hkj_le : Nat.dist k.1 j.1 ≤ b := Nat.le_of_not_gt hnot
      have htri := Nat.dist.triangle_inequality i.1 k.1 j.1
      have : Nat.dist i.1 j.1 ≤ a + b :=
        le_trans htri (Nat.add_le_add hik_le hkj_le)
      omega
    rw [hB k j hkj, mul_zero]

/-- GQC2b. 带宽幂：带宽 ≤ b 的矩阵，t+1 步后带宽 ≤ (t+1)·b。
    证明链：归纳 + band_comp + 结合律 ((t+1)·b + b = (t+2)·b)。 -/
lemma band_pow {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) {b : ℕ}
    (hT : band_le T b) (t : ℕ) : band_le (T ^ (t + 1)) ((t + 1) * b) := by
  induction t with
  | zero =>
      simpa using hT
  | succ t ih =>
      have hband : band_le (T ^ (t + 1) * T) ((t + 1) * b + b) :=
        band_comp (T ^ (t + 1)) T ih hT
      have hb : (t + 1) * b + b = (t + 2) * b := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_mul (t + 1) b).symm
      simpa [pow_succ, ← hb] using hband

/-- 一维链最近邻跳跃矩阵：只在 |i−j| = 1 处为 1（流动格点化的局域传播）。 -/
def chainJump {n : ℕ} : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if Nat.dist i.1 j.1 = 1 then 1 else 0

lemma chainJump_band {n : ℕ} : band_le (chainJump (n := n)) 1 := by
  intro i j hij
  have hne : Nat.dist i.1 j.1 ≠ 1 := Nat.ne_of_gt hij
  simp [chainJump, hne]

/-- GQC2★. 链跳跃光锥：t+1 步后带宽 ≤ t+1——传播核只在 |i−j| ≤ t+1 处非零。
    证明链：band_pow（b=1，归纳带宽传播）+ (t+1)·1 = t+1。 -/
lemma chainJump_causal {n : ℕ} (t : ℕ) :
    band_le (chainJump (n := n) ^ (t + 1)) (t + 1) := by
  simpa using band_pow (T := chainJump (n := n)) (b := 1) (t := t) (chainJump_band)

/-- GQC2★. 光锥外为零：t+1 步后，距离 > t+1 的格点之间传播核为零——
    格点 j 在时刻 t 只能感知 t 步内可达的格点（信息速度 ≤ 1 格/步）。 -/
lemma chainJump_outside_lightcone {n : ℕ} (t : ℕ) (i j : Fin n)
    (h : t + 1 < Nat.dist i.1 j.1) : (chainJump (n := n) ^ (t + 1)) i j = 0 := by
  exact chainJump_causal t i j h

/-! ### GQC3★. 非均匀流动 ⟹ 倾斜光锥 ⟹ 等效超光速（几何描述，非物质描述）

leo（2026-08-16）假设推进第三跳（信息传递：因果 → 等效速度）：
- ★ 关键物理观点：**空间本身的等效流动速度就是光速**；在不均匀空间里
  （流动速度逐点不同，如黑洞视界内 Painlevé-Gullstrand 雨速 > c、
  Alcubierre 泡的拖曳坐标），**等效速度完全可以超光速**。
- 这是**几何描述**不是**物质描述**：信号相对流动仍 ≤ 1 格/步（局部因果，
  GQC2 在流动坐标系中成立），但流动把信号拖曳到更远——静止坐标系的
  等效速度 = 信号速度 + 流动速度，可 > 1（光锥被流动倾斜）。
- ★ GQC3a：坐标拖曳——流动位形 φ（格点 k 被拖曳位移 φ_k），
  流动坐标 ξ_k = k − φ_k 中信号 ≤ t 步可达 ⟹ 静止坐标距离
  |j − i| ≤ t + |φ_j − φ_i|（三角不等式：等效距离 = 信号位移 + 流动位移）
- ★ GQC3b：等效超光速——信号随流（流动坐标中静止，被流动携带）时，
  流动梯度 > 1 格/步 ⟹ 1 步内静止位移 > 1（等效速度 > 1 = 超光速），
  而信号相对流动从未超过 1（局部因果保持）。
- 物理含义：**因果性（信号 ≤ 局部光速）与等效超光速（几何拖曳）不矛盾**
  ——这是曲率飞船（Alcubierre）的数学结构：泡内信号 ≤ c，泡移动等效 > c。
- 诚实：坐标变换 + 三角不等式（真但平凡）；框架贡献 = 把 GQC2 的光锥
  明确为"流动坐标系光锥"，静止坐标系中等效超光速是几何倾斜（解释层）。 -/

/-- 流动坐标：格点 k 的流动坐标 ξ_k = k − φ_k（φ_k = 流动拖曳位移）。
    信号在流动坐标中速度 ≤ 1（局部因果，GQC2 的均匀光锥在流动系成立）。 -/
def flowCoord {n : ℕ} (φ : Fin n → ℤ) (k : Fin n) : ℤ :=
  (k.1 : ℤ) - φ k

/-- GQC3a★. 坐标拖曳：流动坐标中信号 t 步可达（|ξ_j − ξ_i| ≤ t）
    ⟹ 静止坐标距离 |j − i| ≤ t + |φ_j − φ_i|——等效距离 = 信号位移 + 流动位移。
    证明链：j − i = (ξ_j+φ_j) − (ξ_i+φ_i) = (ξ_j−ξ_i) + (φ_j−φ_i) → 三角不等式。 -/
lemma gqc3_equivalent_speed {n : ℕ} (φ : Fin n → ℤ) (t : ℕ) (i j : Fin n)
    (hξ : |flowCoord φ j - flowCoord φ i| ≤ (t : ℤ)) :
    |(j.1 : ℤ) - (i.1 : ℤ)| ≤ (t : ℤ) + |φ j - φ i| := by
  have hsplit : (j.1 : ℤ) - (i.1 : ℤ) =
      (flowCoord φ j - flowCoord φ i) + (φ j - φ i) := by
    simp [flowCoord]
    ring
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add hξ (le_rfl))

/-- GQC3b★. 等效超光速（几何）：信号随流（流动坐标中静止，被流动携带）
    且流动梯度 > 1 格/步 ⟹ 1 步内静止位移 > 1——等效速度超光速，
    而信号相对流动从未超过局部光速（因果保持）。
    证明链：ξ_i = ξ_j ⟹ j − i = φ_j − φ_i（omega）→ abs_of_pos（梯度正）→ hflow。 -/
lemma gqc3_superluminal_geometric {n : ℕ} (φ : Fin n → ℤ) (i j : Fin n)
    (hcarry : flowCoord φ i = flowCoord φ j)
    (hflow : 1 < φ j - φ i) :
    (1 : ℤ) < |(j.1 : ℤ) - (i.1 : ℤ)| := by
  have hsplit : (j.1 : ℤ) - (i.1 : ℤ) = φ j - φ i := by
    unfold flowCoord at hcarry
    omega
  rw [hsplit]
  have hpos : 0 < φ j - φ i := by omega
  rw [abs_of_pos hpos]
  exact hflow

/-- GQC3★ 一致性：均匀流动特例——φ_k = v·k（线性位形，均匀拖曳）时，
    等效超光速判据直接套用 GQC3b（v > 1 步的均匀流动 ⟹ 等效速度 > 1）。 -/
lemma gqc3_uniform_flow {n : ℕ} (v : ℤ) (i j : Fin n)
    (hcarry : flowCoord (fun k => v * (k.1 : ℤ)) i = flowCoord (fun k => v * (k.1 : ℤ)) j)
    (hflow : 1 < v * (j.1 : ℤ) - v * (i.1 : ℤ)) :
    (1 : ℤ) < |(j.1 : ℤ) - (i.1 : ℤ)| := by
  exact gqc3_superluminal_geometric (fun k => v * (k.1 : ℤ)) i j hcarry hflow

end ProjectionPhysics.QFTFlow

end
