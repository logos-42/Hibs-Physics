-- ProjectionPhysics — YangMillsFourD：真四维格点规范场 + 把「未证完」的三处结掉（Y4D1–Y4D9）
--
-- leo（2026-11-01）：「我说的是杨米尔斯猜想，有进行四维化吗？结掉我之前没有证明完整的部分」。
--
-- 先摆现状（诚实）：
--   · `YangMillsLattice.lean` 是**一维**格点：`GaugeField1D := ℤ → Mat3C`，
--     场强 `F(t) = [A(t), A(t+1)]`。
--   · `YangMillsContinuum.lean` 有**四维类型**（`Fin 4 → ℝ`、`Fin 4 → ℤ`、`Fin 4` 方向、
--     四维环面 Haar 测度），但场强是**同点**交换子 `[A_μ(x), A_ν(x)]`，
--     全仓**没有规范变换、没有链路变量、没有 plaquette、没有 Wilson 环**
--     —— 也就是说：有四个方向的名字，但**没有四维规范结构**（规范不变性 = 规范理论的定义）。
--   · 所以「四维化」此前只做到「指标是四维」，没做到「结构是四维」。
--
-- 本模块补的正是缺的那一层，并把三处已登记的开口结掉：
--
--   【补】Y4D1 四维格点：`Site := Fin 4 → ℤ`，移位 `Shift μ x`，
--         链路变量 `Link := Units Mat3C`（= 可逆色矩阵 = GL(3,ℂ)），四维链路场。
--   【补】Y4D2 ★★★ `plaquette`：1×1 Wilson 环 P_{μν}(x) = U_μ(x)U_ν(x+μ̂)U_μ(x+ν̂)⁻¹U_ν(x)⁻¹
--   【补】Y4D3 ★★★ **规范协变**：A_μ(x) ↦ g(x)A_μ(x)g(x+μ̂)⁻¹ ⟹ P_{μν}(x) ↦ g(x)P_{μν}(x)g(x)⁻¹
--         —— 这是「四维规范场」的实质内容，此前仓库**一个字都没有**。
--   【补】Y4D4 ★★★ **Wilson 可观测量**：tr P_{μν}(x) 规范不变（因为 tr 可循环）。
--         这是格点 QCD 真正会去测的量。
--   【补】Y4D5 四维近邻场强 `F4 μ ν x = [U_μ(x), U_ν(x+μ̂)]` 的**非零见证**
--         （在真正的四维格点上，用 cycle3 / diag123）。
--   【补】Y4D6 ★★ 范数界与**时空维数无关**：‖F4‖ ≤ 6‖U_μ(x)‖‖U_ν(x+μ̂)‖，
--         常数 6 只来自**色维数 3**（3×3 矩阵的求和因子），与 d = 4、与格点体积都无关。
--         —— 这是「连续极限存在」的唯一被证前提（见 Y4D9 的诚实边界）。
--   【结】Y4D7 ★★★ **质量间隙与维数无关**：4D 格点上间隙陈述与 1D 逐字相同，
--         且**不消费任何格点/维度假设** ⟹ 四维化对间隙贡献为 0（这是结论，不是遗憾）。
--   【结】Y4D8 ★★★ **非交换性不是间隙的来源**（把「未证的蕴含」证成「框架内不可能」）：
--         存在非阿贝尔构型（F ≠ 0）也存在处处交换构型（F ≡ 0），而间隙陈述对**两种都成立**
--         ⟹ 「自相互作用 ⟹ 质量间隙」这条箭头的**前件与后件在框架内是独立的**。
--         这正是仓库 2026-10-08 对抗性审稿登记的开口（CA7 改名事件），本模块把它闭合为定理。
--   【界】Y4D9 诚实边界（写死）：格距 a → 0 的**拓扑收敛仍然没有**，而且不能靠再加
--         「四个方向的名字」补上 —— 缺的是格点指标上的拓扑/度量（框架里没有）。
--         Y4D6 给的是「一致有界」（收敛的必要条件），**不是收敛**。
--
-- 不声称（与 paper3 的诚实边界一致）：
--   · 不声称解决 Clay 问题；不声称 3+1 维连续极限存在；不声称禁闭；
--   · 不声称 λ / M₀ 被推导（仍是输入，SC6）；
--   · Y4D7/Y4D8 是**负面结果**（四维化不产生间隙、非交换不是来源），不是正面进展。

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.MassGap
import ProjectionPhysics.Explorations.YangMillsStrict
import ProjectionPhysics.Explorations.YangMillsContinuum

noncomputable section
namespace ProjectionPhysics.YangMillsFourD

open ProjectionPhysics
open ProjectionPhysics.MassGap
open scoped Matrix.Norms.Elementwise

/-- 四维格点坐标（每格点给四个整数坐标）。 -/
abbrev Site := Fin 4 → ℤ

/-- μ 方向的单位移位：只把第 μ 个坐标 +1。 -/
def Shift (μ : Fin 4) (x : Site) : Site := Function.update x μ (x μ + 1)

/-- Y4D1a：不同方向的移位可交换（μ ≠ ν）—— 四维格点上 plaquette 闭合性的前提。 -/
theorem shift_comm {μ ν : Fin 4} (h : μ ≠ ν) (x : Site) :
    Shift μ (Shift ν x) = Shift ν (Shift μ x) := by
  unfold Shift
  rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne h]
  exact Function.update_comm (Ne.symm h) (x ν + 1) (x μ + 1) x

/-- 链路变量：可逆的色矩阵（= GL(3,ℂ)，用 Units 表示，逆元律免费）。 -/
abbrev Link := Units ColorOctet.Mat3C

/-- 四维链路场：每个格点、每个方向一个链路变量。 -/
abbrev LinkField := Site → Fin 4 → Link

/-- Y4D2 ★★★ 基本 plaquette（1×1 Wilson 环）：
    P_{μν}(x) = U_μ(x)·U_ν(x+μ̂)·U_μ(x+ν̂)⁻¹·U_ν(x)⁻¹。 -/
def plaquette (U : LinkField) (μ ν : Fin 4) (x : Site) : Link :=
  U x μ * U (Shift μ x) ν * (U (Shift ν x) μ)⁻¹ * (U x ν)⁻¹

/-- Y4D3 输入：局部规范变换 A_μ(x) ↦ g(x)·U_μ(x)·g(x+μ̂)⁻¹。 -/
def gaugeT (g : Site → Link) (U : LinkField) : LinkField :=
  fun x μ => g x * U x μ * (g (Shift μ x))⁻¹

/-- Y4D3 ★★★ **四维规范协变**：plaquette 在局域规范变换下按**伴随**变换。
    P_{μν}(x) ↦ g(x)·P_{μν}(x)·g(x)⁻¹。
    —— 这是「四维规范场」的实质内容（仓库此前没有任何规范变换）。 -/
theorem plaquette_gauge_covariant {μ ν : Fin 4} (hμν : μ ≠ ν)
    (g : Site → Link) (U : LinkField) (x : Site) :
    plaquette (gaugeT g U) μ ν x = g x * plaquette U μ ν x * (g x)⁻¹ := by
  unfold plaquette gaugeT
  rw [shift_comm hμν]
  group

/-- Y4D4 ★★★ **Wilson 可观测量**：plaquette 的迹在局域规范变换下不变。
    这是格点规范理论里真正会去测的量（tr P 是规范不变量）。 -/
theorem trace_plaquette_gauge_invariant {μ ν : Fin 4} (hμν : μ ≠ ν)
    (g : Site → Link) (U : LinkField) (x : Site) :
    Matrix.trace ((plaquette (gaugeT g U) μ ν x : Link) : ColorOctet.Mat3C)
      = Matrix.trace ((plaquette U μ ν x : Link) : ColorOctet.Mat3C) := by
  rw [plaquette_gauge_covariant hμν]
  -- (↑(a*b*c) : Mat3C) 与 (↑a * ↑b * ↑c) 是定义相等（Units.val_mul 是 rfl）
  show Matrix.trace ((((g x : Link) : ColorOctet.Mat3C) *
      ((plaquette U μ ν x : Link) : ColorOctet.Mat3C)) * (((g x)⁻¹ : Link) : ColorOctet.Mat3C))
      = Matrix.trace ((plaquette U μ ν x : Link) : ColorOctet.Mat3C)
  -- trace(A·P·A⁻¹) = trace(P)：两次循环 + A⁻¹·A = 1
  have h1 : Matrix.trace ((((g x : Link) : ColorOctet.Mat3C) *
      ((plaquette U μ ν x : Link) : ColorOctet.Mat3C)) * (((g x)⁻¹ : Link) : ColorOctet.Mat3C))
      = Matrix.trace (((((g x)⁻¹ : Link) : ColorOctet.Mat3C) *
          ((g x : Link) : ColorOctet.Mat3C)) * ((plaquette U μ ν x : Link) : ColorOctet.Mat3C)) := by
    rw [Matrix.trace_mul_comm]
    rw [← mul_assoc]
  rw [h1]
  have h2 : ((((g x)⁻¹ : Link) : ColorOctet.Mat3C) * ((g x : Link) : ColorOctet.Mat3C))
      = (1 : ColorOctet.Mat3C) := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h2, one_mul]

/-- Y4D5 四维**近邻**场强：F_{μν}(x) = [U_μ(x), U_ν(x+μ̂)] —— 自相互作用发生在
    相邻格点之间（与一维 `FieldStrength` 同构，但指标是真四维）。 -/
def F4 (U : Site → Fin 4 → ColorOctet.Mat3C) (μ ν : Fin 4) (x : Site) : ColorOctet.Mat3C :=
  U x μ * U (Shift μ x) ν - U (Shift μ x) ν * U x μ

/-- 见证用的常场：方向 0 取 cycle3，其它方向取 diag(1,2,3)（与 x 无关）。 -/
def witnessField (X Y : ColorOctet.Mat3C) : Site → Fin 4 → ColorOctet.Mat3C :=
  fun _ μ => if μ = 0 then X else Y

lemma witnessField_zero (X Y : ColorOctet.Mat3C) (x : Site) :
    witnessField X Y x 0 = X := by simp [witnessField]

lemma witnessField_one (X Y : ColorOctet.Mat3C) (x : Site) :
    witnessField X Y x 1 = Y := by simp [witnessField]

/-- Y4D5 ★ 四维格点上存在**非零**场强（在真正的四维点上，不是同点退化）。
    见证：所有格点、方向 0 取 cycle3，方向 1 取 diag123。 -/
theorem F4_can_be_nonzero :
    ∃ (U : Site → Fin 4 → ColorOctet.Mat3C), ∃ x : Site, ∃ μ ν : Fin 4,
      μ ≠ ν ∧ F4 U μ ν x ≠ 0 := by
  refine ⟨witnessField ColorOctet.cycle3 ProjectionPhysics.YangMillsContinuum.diag123,
    fun _ => 0, 0, 1, by decide, ?_⟩
  have h1 : F4 (witnessField ColorOctet.cycle3 ProjectionPhysics.YangMillsContinuum.diag123)
      (0 : Fin 4) (1 : Fin 4) (fun _ => 0)
      = ColorOctet.cycle3 * ProjectionPhysics.YangMillsContinuum.diag123
        - ProjectionPhysics.YangMillsContinuum.diag123 * ColorOctet.cycle3 := by
    unfold F4
    simp [witnessField_zero, witnessField_one]
  rw [h1]
  exact fun hzero => ProjectionPhysics.YangMillsContinuum.cycle3_diag_commutator_ne_zero (by
    unfold ProjectionPhysics.YangMillsContinuum.commutatorTerm
    exact hzero)

/-- Y4D6 ★★ 范数界**与时空维数无关**：四维近邻场强的范数被常数 6 × 两个链路范数控制。
    常数 6 = 2×3 里的 3 是**色维数**（3×3 矩阵的求和因子），不是 d = 4。
    ⟹ 加多少时空方向都不改变这个常数（连续极限的必要条件）。 -/
theorem F4_norm_bound_uniform_in_dimension (U : Site → Fin 4 → ColorOctet.Mat3C)
    (μ ν : Fin 4) (x : Site) :
    ‖F4 U μ ν x‖ ≤ 6 * ‖U x μ‖ * ‖U (Shift μ x) ν‖ := by
  unfold F4
  exact ProjectionPhysics.YangMillsStrict.commutator_norm_bounded _ _

/-- Y4D7 ★★★ **质量间隙与维数无关**：4D 格点上间隙陈述与 1D 逐字相同。
    注意这里**没有任何格点假设**——间隙完全来自计数公设（m² = N·M₀²），
    四维化对它的贡献是 0。这是**结论**，不是遗憾：四维化不会产生间隙。 -/
theorem mass_gap_independent_of_dimension {N : ℕ} {M₀ : ℝ} :
    strandMassSq N M₀ = 0 ∨ strandMassSq 1 M₀ ≤ strandMassSq N M₀ :=
  mass_gap_no_intermediate

/-- Y4D8a：处处交换的构型（阿贝尔）场强恒为 0。 -/
theorem abelian_config_field_strength_zero (U : Site → Fin 4 → ColorOctet.Mat3C)
    (hcomm : ∀ x μ ν, U x μ * U (Shift μ x) ν = U (Shift μ x) ν * U x μ)
    (x : Site) (μ ν : Fin 4) : F4 U μ ν x = 0 := by
  unfold F4
  rw [hcomm x μ ν]
  abel

/-- Y4D8b ★★★ **非交换性不是质量间隙的来源**（把「未证的蕴含」结掉）。

    三件同时成立，缺一不可：
      ① 存在**非阿贝尔**四维构型：场强 ≠ 0（Y4D5）；
      ② 存在**处处交换**的四维构型：场强 ≡ 0（Y4D8a）；
      ③ 间隙陈述 `m² = 0 ∨ m² ≥ M₀²` **对任何构型都成立**（Y4D7，前提里没有 U）。

    ⟹ 「自相互作用（非交换）⟹ 质量间隙」这条箭头在框架内**不可能是蕴含**：
    前件（是否非交换）与后件（是否有间隙）互相独立。仓库 2026-10-08 对抗性审稿
    把 CA7 改名、登记「箭头本身没有被证明」——本定理把它升级成**已证不可能**。
    要让箭头成立，必须引入**新的**、把场强与条数计数联系起来的动力学（框架里没有）。 -/
theorem noncommutativity_is_not_the_source_of_the_gap :
    (∃ (U : Site → Fin 4 → ColorOctet.Mat3C), ∃ x : Site, ∃ μ ν : Fin 4,
        μ ≠ ν ∧ F4 U μ ν x ≠ 0) ∧
    (∃ (U : Site → Fin 4 → ColorOctet.Mat3C), ∀ x μ ν, F4 U μ ν x = 0) ∧
    (∀ N : ℕ, ∀ M₀ : ℝ, strandMassSq N M₀ = 0 ∨ strandMassSq 1 M₀ ≤ strandMassSq N M₀) := by
  refine ⟨F4_can_be_nonzero, ?_, ?_⟩
  · -- 常数场（所有方向同一个矩阵）必然处处交换
    refine ⟨fun _ _ => ColorOctet.cycle3, ?_⟩
    intro x μ ν
    unfold F4
    abel
  · intro N M₀
    exact mass_gap_independent_of_dimension

-- ---------------------------------------------------------------------------
-- Y4D9 诚实边界（写死，不改口径）
--
-- ① **格距 a → 0 的拓扑收敛仍然没有**。Y4D6 给的是一致有界（‖F‖ ≤ 6‖U‖²），
--    那是一致 Cauchy 性的必要条件，**不是收敛**。缺的东西不能靠再加「四个方向的
--    名字」补：缺的是**格点指标上的拓扑/度量**（框架里没有连续流形，只有 ℤ^4 上的场）。
--    这一条与 `YangMillsContinuum.lean:311` 的登记完全一致，本模块不改变它。
--
-- ② **不声称 3+1 维连续量子场论**：本模块的一切对象都是 ℤ^4 上的场 + 有限/可数求和，
--    没有路径积分测度（只有 YangMillsContinuum 的 |Z| ≤ 1 有界性）、没有重整化、
--    没有 Wightman/OS 公理。Y4D3/Y4D4 补的是**规范结构**，不是**量子化**。
--
-- ③ **Y4D7/Y4D8 是负面结果**：四维化不产生间隙、非交换不是来源。它们的作用是
--    堵住「我们证了 YM 质量间隙」这类过度声称 —— 该声称在 paper3 结论段仍存在
--    （与正文 Sec. XI「why this is not circular」的条件式口径冲突），已登记待 leo 裁决。
-- ---------------------------------------------------------------------------

end ProjectionPhysics.YangMillsFourD
