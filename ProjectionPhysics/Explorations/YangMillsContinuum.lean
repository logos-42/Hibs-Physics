-- ProjectionPhysics — YangMillsContinuum：连续是流动空间自带的
--
-- leo（2026-10-08）：「我们本来就是流动空间自带的」。
--
-- 方向：连续不是格点极限的产物，而是流动空间的原生基底。格点是连续
-- 流上的采样结构（计数/条数），不是连续场的来源。这翻转了审稿人
-- "连续极限未形式化"的批评：不是没做，而是方向错了会被永远困住；
-- 方向对了，连续就是框架的结构本身，格点是它的计数视角。
--
-- 本模块落地（零 sorry 零 warning）：
--   CC1 ★  连续是基底：连续场 A : (ℝ⁴) → Mat3C 是原生的；格点场
--          A_Λ : (ℤ⁴) → Mat3C 是 A 的采样（restriction），不是来源。
--   CC2 ★★ 四维连续规范场：A x μ = A_μ(x)（每个时空方向一个矩阵值
--          分量）；场强非交换项 F_μν ⊃ [A_μ, A_ν] 需要两个独立方向
--          μ≠ν（回应审稿人 M1 的一维缺陷）。存在场使 [A_μ,A_ν]≠0。
--   CC3 ★  两个独立方向交换子非零的显式见证：
--          [cycle3, diag(1,2,3)] ≠ 0（位置 (0,1) 处值 = 1）。
--   CC4 ★★ 采样一致性：格点差分是连续方向导数的代数种子（桥有内容）。
--   CC5 ★★ 路径积分被积函数模为 1：|e^{iS}| = 1（配分函数有限性的
--          关键一步：|Z| ≤ vol(Λ) 由被积函数模 1 + 紧致群给出）。
--   CC6     有限格点路径积分记号与重整化思想：结构登记（注释），
--          无穷格点/连续极限是 Clay 核心，开放。
--
-- 诚实边界（写死）：
--   · CC1 把"连续是基底"形式化为类型与采样关系；「连续场是流动空间
--     的数学实现」仍是框架的语义层（公设），不是从格点推出的。
--   · CC2 的场强只形式化非交换项 [A_μ,A_ν]（矩阵交换子，干净）。
--     导数项 ∂_μ A_ν − ∂_ν A_μ 需要 Fréchet 偏导的完整理论（后续
--     工作），此处以注释登记为结构。
--   · CC4 "差分 = 导数的代数种子"是结构对应（框架既有的连续→离散
--     方法在规范场上的应用），不是分析极限。
--   · CC5 证明被积函数模 1；配分函数本身的有限性还需紧致 SU(3) 的
--     Haar 测度（mathlib 有，暂不展开），此处给关键一步。
--   · CC6 的路径积分是有限格点正则化记号；连续极限未构造。
--   · 死法：若"连续是基底 + 采样一致性"与物理矛盾（连续场无法采样
--     为格点场），或四维路径积分在有限格点上仍发散，相关陈述死。

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.ColorOctetMathlib

noncomputable section
namespace ProjectionPhysics.YangMillsContinuum

open ProjectionPhysics
open ColorOctet
open MeasureTheory
open scoped Matrix
open scoped MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- 色空间矩阵（仓库类型，mathlib 3×3 复矩阵）。 -/
abbrev Mat3C := Matrix (Fin 3) (Fin 3) ℂ

/-- 连续场：ℝ⁴ → Mat3C。流动空间的矢量光速场 C 的色矩阵实现。
    连续是基底：这个类型是原生的，不是从格点极限构造的。 -/
abbrev ContField : Type := (Fin 4 → ℝ) → Mat3C

/-- 格点场：ℤ⁴ → Mat3C。流动空间连续场在格点上的采样（计数视角）。 -/
abbrev LatticeField : Type := (Fin 4 → ℤ) → Mat3C

/-- ★ CC1：连续是基底，格点是采样。
    连续场 A 采样到格点：A_Λ(n) = A(n 的实数嵌入)。
    格点场是连续场的 restriction，不是连续场的来源。 -/
def sample (A : ContField) (n : Fin 4 → ℤ) : Mat3C :=
  A (fun i => (n i : ℝ))

/-- ★ CC1b：采样保持场值（restriction 的定义性恒等式）。
    格点是连续场在整数格上的取值 —— 连续自带的，采样是视角。 -/
theorem sample_is_restriction (A : ContField) (n : Fin 4 → ℤ) :
    sample A n = A (fun i => (n i : ℝ)) := rfl

/-- 矩阵交换子：[X,Y] = X·Y − Y·X（非交换自相互作用的核心）。 -/
def commutatorTerm (X Y : Mat3C) : Mat3C :=
  X * Y - Y * X

/-- ★ CC2a：非交换项 = 矩阵交换子（定义性，rfl）。
    [A_μ, A_ν] 就是两个方向分量 X=A_μ(x), Y=A_ν(x) 的矩阵交换子。 -/
theorem commutator_term_is_matrix_commutator (X Y : Mat3C) :
    commutatorTerm X Y = X * Y - Y * X := rfl

/-- 连续规范场：A x μ = A_μ(x)，每个时空方向一个矩阵值分量。
    四维结构：μ,ν 取 Fin 4 的两个独立方向（回应一维格点缺 ∂∂、
    无非规范协变方向的批评）。 -/
abbrev GaugeField : Type := (Fin 4 → ℝ) → (Fin 4 → Mat3C)

/-- 常规范场：方向 0 处取值 X，其它方向取值 Y。 -/
def gaugeFieldOf (X Y : Mat3C) : GaugeField :=
  fun _ μ => if μ = 0 then X else Y

/-- ★★ CC2b：场强非交换项 F_μν ⊃ [A_μ, A_ν]（两个独立方向）。 -/
def fieldStrength (A : GaugeField) (μ ν : Fin 4) (x : Fin 4 → ℝ) : Mat3C :=
  commutatorTerm (A x μ) (A x ν)

/-- 对角矩阵 diag(1,2,3) 的显式函数形式（避免 vec 记号的展开问题）。 -/
def diag123 : Mat3C :=
  fun i j => if i = j then (match i with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 2 | _ => 3) else 0

/-- ★★ CC3：两个独立方向交换子非零的显式见证。
    取 X = cycle3（C₃ 色循环），Y = diag(1,2,3)。
    在位置 (0,1)：cycle3·diag 的 (0,1) 分量 = 2，diag·cycle3 的
    (0,1) 分量 = 1，故 [X,Y](0,1) = 1 ≠ 0。 -/
theorem cycle3_diag_commutator_ne_zero :
    commutatorTerm cycle3 diag123 ≠ 0 := by
  intro h
  have h01 := congrArg
    (fun M : Mat3C => M ⟨0, by decide⟩ ⟨1, by decide⟩) h
  unfold commutatorTerm cycle3 diag123 at h01
  simp [Matrix.mul_apply, Matrix.vecMul,
    Matrix.cons_val_zero,
    Matrix.vecHead, Matrix.vecTail, Matrix.of_apply] at h01
  norm_num at h01

/-- ★★ CC2c：存在连续规范场，其场强非交换项非零（两个独立方向）。
    见证：方向 0 取值 cycle3，方向 1 取值 diag(1,2,3)（CC3），
    其它方向任意。四维连续场强确实可以非零 —— 与一维格点
    [A(t),A(t+1)] 不同，这里需要两个独立方向 μ≠ν。 -/
theorem continuum_field_strength_can_be_nonzero :
    ∃ A : GaugeField, ∃ x : Fin 4 → ℝ, ∃ μ ν : Fin 4,
      μ ≠ ν ∧ fieldStrength A μ ν x ≠ 0 := by
  refine ⟨gaugeFieldOf cycle3 diag123,
    (fun _ => 0), 0, 1, by decide, ?_⟩
  unfold fieldStrength commutatorTerm gaugeFieldOf
  change cycle3 * diag123 - diag123 * cycle3 ≠ 0
  exact cycle3_diag_commutator_ne_zero

/-- ★★ CC4：采样一致性 —— 格点差分是连续方向导数的代数种子。
    框架既有的连续→离散方法：连续偏导 ∂_μ 用格点前向差分表示。
    对规范场：连续场 A 的采样在格点上的前向差分 = A 的相邻取值之差，
    正是 ∂_μ A 在格点处的代数对应（桥从 'True' 升级为有内容的
    恒等式）。 -/
theorem sample_difference_is_derivative_seed
    (A : ContField) (n : Fin 4 → ℤ) (μ : Fin 4) :
    sample A (Function.update n μ (n μ + 1)) - sample A n =
      A (fun i => (Function.update n μ (n μ + 1) i : ℝ)) -
        A (fun i => (n i : ℝ)) := by
  rfl

/-- ★★ CC5：路径积分被积函数模为 1。
    对任意实数作用量 S，|e^{iS}| = 1（欧拉公式的直接推论）。 -/
theorem exp_iS_has_norm_one (S : ℝ) :
    ‖Complex.exp (Complex.I * S)‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal S

-- ★★ CC6：配分函数有界性的测度论内核。
--   先不偷渡 SU(3) 的 Haar 实例：对任意测度空间，若被积函数模不超过 1，
--   Bochner 积分的 extended norm 不超过总测度。这正是 Haar 完整实例化
--   接入前已经可以严格证明的部分。
theorem enorm_integral_le_measure_univ_of_norm_le_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, f x ∂μ‖ₑ ≤ μ Set.univ := by
  calc
    ‖∫ x, f x ∂μ‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm f
    _ ≤ ∫⁻ x : α, (1 : ENNReal) ∂μ := by
      apply lintegral_mono
      intro x
      change ‖f x‖ₑ ≤ (1 : ENNReal)
      rw [← ofReal_norm_eq_enorm]
      exact le_trans (ENNReal.ofReal_le_ofReal (hf x)) (by simp)
    _ = μ Set.univ := by simp [lintegral_const]

/-- ★★ CC6b：归一化 Haar/概率测度下，单位模被积函数的配分函数有界。
    这里只使用概率测度接口；将有限格点 SU(3) 配置空间实例化为
    有限积归一化 Haar 测度，是剩余的类型级工作，不在此伪装成已完成。 -/
theorem norm_integral_le_one_of_isProbabilityMeasure
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, f x ∂μ‖ₑ ≤ 1 := by
  simpa using enorm_integral_le_measure_univ_of_norm_le_one μ f hf

/-- ★ CC6c：指数作用量直接满足 CC6 的抽象核。 -/
theorem exp_iS_integral_le_measure_univ
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : α → ℝ) :
    ‖∫ x, Complex.exp (Complex.I * S x) ∂μ‖ₑ ≤ μ Set.univ := by
  apply enorm_integral_le_measure_univ_of_norm_le_one μ
  intro x
  rw [exp_iS_has_norm_one]

/-- ★★★ CC8：连续场强的严格形式（含导数项）。
    F_μν = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]。
    这里 ∂_μ A_ν 是沿第 μ 坐标线的方向导数（对可微场 = Fréchet 导数在
    坐标方向上的取值）。**此项是真实加项，不是被定义掉的**：常量场给出 0，
    线性场给出其系数（CC8c/CC8d）。

    这条回应对抗性审稿的 R1（"场强被定义成交换子本身 ⟹ 非交换是假设进定义"）：
    旧 CC2 的 `fieldStrength` 只是本定义的**特殊情形**（导数项为零时）。 -/
noncomputable def dirDeriv (A : (Fin 4 → ℝ) → Mat3C) (μ : Fin 4)
    (x : Fin 4 → ℝ) : Mat3C :=
  deriv (fun t : ℝ => A (Function.update x μ (x μ + t))) 0

/-- ★★★ CC8：严格连续场强（含导数项）。 -/
noncomputable def fieldStrengthStrict (A : GaugeField) (μ ν : Fin 4)
    (x : Fin 4 → ℝ) : Mat3C :=
  dirDeriv (fun y => A y ν) μ x - dirDeriv (fun y => A y μ) ν x +
    commutatorTerm (A x μ) (A x ν)

/-- ★ CC8a：常量场的方向导数为零（导数项在常量场上消失）。 -/
theorem dirDeriv_const_field (X : Mat3C) (μ : Fin 4) (x : Fin 4 → ℝ) :
    dirDeriv (fun _ : Fin 4 → ℝ => X) μ x = 0 := by
  simp [dirDeriv]

/-- ★★ CC8b：常量场的严格场强 = 纯交换子。
    ⟹ 旧 `fieldStrength`（只有交换子）是严格场强在导数项为零时的**特殊情形**；
    非交换项现在是一个**可分离的加项**，不是全部定义。 -/
theorem fieldStrengthStrict_gaugeFieldOf (X Y : Mat3C) (x : Fin 4 → ℝ) :
    fieldStrengthStrict (gaugeFieldOf X Y) 0 1 x = commutatorTerm X Y := by
  unfold fieldStrengthStrict gaugeFieldOf
  simp [dirDeriv]

/-- ★★ CC8c：严格场强可以非零（导数项为零的常量场见证）——
    非交换项不是被导数项抵消掉的空项。 -/
theorem fieldStrengthStrict_can_be_nonzero :
    ∃ A : GaugeField, ∃ x : Fin 4 → ℝ, ∃ μ ν : Fin 4,
      μ ≠ ν ∧ fieldStrengthStrict A μ ν x ≠ 0 := by
  refine ⟨gaugeFieldOf cycle3 diag123, (fun _ => 0), 0, 1, by decide, ?_⟩
  rw [fieldStrengthStrict_gaugeFieldOf]
  exact cycle3_diag_commutator_ne_zero

/-- ★★ CC8d：线性场的方向导数 = 其系数 —— 导数项**非平凡**
    （∂_μ 不是恒零算子；这是"场强含真导数项"的内容见证）。 -/
theorem dirDeriv_linear_field (c : Mat3C) (μ : Fin 4) (x : Fin 4 → ℝ) :
    dirDeriv (fun y : Fin 4 → ℝ => (y μ) • c) μ x = c := by
  rw [dirDeriv]
  have hfun : (fun t : ℝ => (Function.update x μ (x μ + t)) μ • c)
      = fun t => (x μ + t) • c := by
    funext t
    simp
  rw [hfun]
  have h0 : HasDerivAt (fun t : ℝ => t • c) c 0 := by
    simpa [one_smul] using (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) c)
  have h1 : HasDerivAt (fun t : ℝ => (x μ + t) • c) c 0 := by
    simpa [add_smul, add_comm] using (h0.const_add ((x μ) • c))
  exact h1.deriv

/-- ★★ CC8e：非零系数的线性场 ⟹ 方向导数非零（导数项确实能不为零）。 -/
theorem dirDeriv_linear_field_ne_zero (c : Mat3C) (hc : c ≠ 0) (μ : Fin 4)
    (x : Fin 4 → ℝ) :
    dirDeriv (fun y : Fin 4 → ℝ => (y μ) • c) μ x ≠ 0 := by
  rw [dirDeriv_linear_field]
  exact hc

-- ---------------------------------------------------------------------------
-- CC9 ★★★ 配分函数是**真积分**（不是占位符号）
--   Z_Ω(S) = ∫_Ω e^{iS} dμ。CC6 的界直接给出：单位模被积函数 ⟹
--   ‖Z‖ₑ ≤ μ(全空间)；归一化（概率/Haar）测度下 ⟹ ≤ 1。
--   诚实边界：把 Ω 实例化为有限格点上的 SU(3)-值配置空间（归一化 Haar 有限积）
--   仍是开放的类型级构造（mathlib 有 SU(3) 的群结构与紧致群的 Haar 理论，
--   但有限积 + 归一化 + 与格点指标对接未做）；本模块**不留下返回 0 的假定义**。
-- ---------------------------------------------------------------------------

/-- ★★★ CC9：配分函数 = 指数作用量的 Bochner 积分（真积分，非占位）。 -/
noncomputable def partitionFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * S ω) ∂μ

/-- ★★★ CC9a：任意测度空间上，配分函数被总测度控制。 -/
theorem partitionFunction_enorm_le_measure_univ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) :
    ‖partitionFunction μ S‖ₑ ≤ μ Set.univ := by
  unfold partitionFunction
  exact exp_iS_integral_le_measure_univ μ S

/-- ★★★ CC9b：归一化（概率/Haar）测度下 |Z| ≤ 1 —— 即论文里
    |Z_Λ| ≤ vol(Λ) 的**测度论含义**（vol 归一化为 1）。 -/
theorem partitionFunction_enorm_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) :
    ‖partitionFunction μ S‖ₑ ≤ 1 := by
  simpa using enorm_integral_le_measure_univ_of_norm_le_one μ
    (fun ω => Complex.exp (Complex.I * S ω))
    (fun ω => by rw [exp_iS_has_norm_one])

-- ★★★ CC6b：重整化 = 格距依赖的耦合（Wilson 重整化群思想）。
--   g(a) 随格距 a 变化，使物理量在 a→0 时不变。这是格点 QCD 的
--   标准思想；β 函数、渐近自由、连续极限的完整构造是 Clay 问题
--   的开放核心，仓库以注释登记（不设定理，避免空转主张）。
--   诚实边界：本模块不声称完成重整化；它定位"连续是基底"的
--   方向与路径积分的有限格点记号。
--   ★ 2026-10-08：原先此处有一个 `def latticePathIntegral ... := 0` 占位
--   定义（对抗性审稿 R3 指出它会被读成"把对象定义成 0 换零 sorry"）——
--   **已删除**；格点路径积分由 CC9 的 `partitionFunction` 承载（真积分）。

-- ---------------------------------------------------------------------------
-- CC10 ★★★ 四维群实例（"存在性"那一半的可检查版，2026-10-08）
--   leo：「用流动空间本身完成前半部分；格点数是流动空间的描述部分；
--   你可以构造四维群来实现验证存在性。」
--   做法：取**四维紧致群** T⁴ = S¹ × S¹ × S¹ × S¹（S¹ = AddCircle 1，
--   mathlib 的 volume 即 Haar），令有限格点 Λ 上的配置空间为 Λ → T⁴，
--   其乘积 Haar（volume_pi）总测度 = 1 ⟹ 配分函数 |Z| ≤ 1 **无条件成立**
--   （不再有 [IsProbabilityMeasure μ] 这种待填假设）。
--   诚实边界（写死）：
--     · T⁴ 是**阿贝尔**群（U(1)⁴）；Clay 问题要的非阿贝尔紧致单群（SU(3)^Λ）
--       的类型级 Haar 实例仍未给出 —— 本定理验证的是**测度/体积层**（存在性
--       一层的可检查部分），不是 4 维 QFT（Wightman/OS）也不是 Δ>0。
--     · 本框架的质量间隙来自**整数条数**（CA11/MG），不是 4 维动力学的；
--       因此它是"同一结论、两条机制"——若该认定失败，本支**可能被证伪**
--       （leo 2026-10-08 明确："实际上，可能我们也会证伪这个猜想"）。
-- ---------------------------------------------------------------------------

/-- ★★ CC10a：一维紧致群 S¹ = AddCircle 1 的 Haar（volume）总测度 = 1。 -/
theorem circle_haar_univ : volume (Set.univ : Set (AddCircle (1 : ℝ))) = 1 := by
  rw [AddCircle.measure_univ]
  norm_num

/-- ★★★ CC10b：**四维紧致群** T⁴ = S¹×S¹×S¹×S¹ 的 Haar 总测度 = 1。 -/
theorem torus4_haar_univ : volume (Set.univ : Set (Fin 4 → AddCircle (1 : ℝ))) = 1 := by
  rw [volume_pi]
  rw [Measure.pi_univ]
  simp

/-- ★★★ CC10c：有限格点 Λ 上配置空间（Λ → T⁴）的乘积 Haar 总测度 = 1
    （"格点是流动空间的描述部分"的测度层陈述）。 -/
theorem lattice_conf_univ_torus4 (Λ : Type*) [Fintype Λ] :
    volume (Set.univ : Set (Λ → Fin 4 → AddCircle (1 : ℝ))) = 1 := by
  rw [volume_pi]
  rw [Measure.pi_univ]
  simp [torus4_haar_univ]

/-- ★★★ CC10d（本轮兑现的东西）：**四维群 + 有限格点的配分函数有界** ——
    |Z_Λ| ≤ 1 = vol(Λ) 在具体四维紧致群 T⁴ 上**无条件成立**（CC9 + CC10c）。 -/
theorem lattice_partition_bound_torus4 (Λ : Type*) [Fintype Λ]
    (S : (Λ → Fin 4 → AddCircle (1 : ℝ)) → ℝ) :
    ‖partitionFunction (volume : Measure (Λ → Fin 4 → AddCircle (1 : ℝ))) S‖ₑ ≤ 1 := by
  calc
    ‖partitionFunction (volume : Measure (Λ → Fin 4 → AddCircle (1 : ℝ))) S‖ₑ
        ≤ volume (Set.univ : Set (Λ → Fin 4 → AddCircle (1 : ℝ))) :=
      partitionFunction_enorm_le_measure_univ _ S
    _ = 1 := lattice_conf_univ_torus4 Λ

end ProjectionPhysics.YangMillsContinuum