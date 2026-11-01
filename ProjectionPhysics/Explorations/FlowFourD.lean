-- ProjectionPhysics — FlowFourD：以**流动空间**为前提的四维化（F4D1–F4D7）
--
-- leo（2026-11-01）：「用流动空间做前提来四维化」。
--
-- 与昨天 `YangMillsFourD.lean` 的分工（重要）：
--   · `YangMillsFourD` 补的是**通用格点规范结构**（链路/plaquette/规范变换/Wilson 环）
--     —— 那是对**任何**格点规范理论都成立的东西，**不依赖**「空间在流动」这个前提。
--   · 本模块换前提：**空间流动**（C 是流势，电荷 = 流散度，汇不交换 ⟹ 非阿贝尔）。
--     于是四维化的**来源**变了，规范自由度不再是「公设」而是**流动前提的推论**：
--
--   ① **流势** C_μ(x)：空间流动在每个格点、每个方向上的势（标量版 ℂ / 色版 Mat3C）。
--   ② **可观测量 = 流势的差**：能测的只有「流变了多少」，不是「流势本身取多少」。
--      ⟹ **规范自由 = 流势可以整体重标一个梯度**（C_μ ↦ C_μ + ∂_μχ）而物理不变。
--      —— 这就是流动空间里「规范变换」的**物理来源**（不是从 QFT 借来的公设）。
--   ③ **场强 = 流势的旋度** F_μν = ∂_μC_ν − ∂_νC_μ（色版加交换子 [C_μ,C_ν]，
--      因为「汇不交换」= 非阿贝尔性，来自 YM2/CA3，不是额外假设）。
--
-- 本模块证明（全部零 sorry）：
--   F4D1 ★★ `d_comm`：二阶差分可交换（∂_μ∂_ν = ∂_ν∂_μ 的格点版）= 移位可交换。
--        —— 这是全部内容的**唯一来源**：四维格点上「两个方向先后走」不改变终点。
--   F4D2 ★★★ `Fstr_gauge_invariant`：**规范不变性** —— C_μ ↦ C_μ + d_μχ ⟹ F 不变。
--        证明只用到 F4D1。⟹ 「规范自由度」在流动空间里是**梯度重标**，不是公设。
--   F4D3 ★★★ `bianchi_4d`：**四维 Bianchi 恒等式** d_μF_νρ + d_νF_ρμ + d_ρF_μν = 0。
--        在 3+1 维里这就是齐次麦克斯韦方程（法拉第 + 无磁单极）。
--        ⟹ 仓库的 MaxwellSpace（1+1 维）与 SpaceField3D（静态 3 维）在**含时四维**里的合法化。
--   F4D4 ★★ `Fmat_adjoint_covariant`：色版（非阿贝尔）场强在**整体**伴随变换
--        C_μ ↦ g C_μ g⁻¹ 下协变：F ↦ g F g⁻¹（用到汇不交换 ⟹ 交换子项）。
--   F4D5 ★ `flow_field_strength_nonzero`：流动空间里 F ≠ 0 的显式见证（真四维点）。
--   F4D6 ★ 间隙与「流动前提」无关：接 `MassGap`，四维流动不改变间隙（负面结果照登）。
--   F4D7 诚实边界（写死）：**局部**（依赖格点）规范变换需要链路/plaquette
--        （= `YangMillsFourD.Y4D3`），本模块的 F4D4 只到整体变换；
--        格距 a→0 的连续极限仍然没有（缺格点指标上的拓扑）。
--
-- 不声称：不解决 Clay；不声称禁闭；不声称 λ/M₀ 被推导；
--   不声称「规范自由度是四维化的副产品」之外的任何新物理。

import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing
import ProjectionPhysics.Explorations.MassGap
import ProjectionPhysics.Explorations.YangMillsFourD

noncomputable section
namespace ProjectionPhysics.FlowFourD

open ProjectionPhysics
open ProjectionPhysics.MassGap
open ProjectionPhysics.YangMillsFourD (Site Shift shift_comm)

/-! ### F4D1 流动空间的四维格点：差分与移位 -/

/-- 格点前向差分（∂_μ 的代数种子）：d_μ f(x) = f(x+μ̂) − f(x)。 -/
def d (μ : Fin 4) (f : Site → ℂ) (x : Site) : ℂ := f (Shift μ x) - f x

/-- 差分的函数版（便于把「先走 μ 再走 ν」写成一串）。 -/
def dF (μ : Fin 4) (f : Site → ℂ) : Site → ℂ := fun x => d μ f x

/-- 取流势的第 ρ 个分量（视为 Site → ℂ 的函数）。 -/
def slice (C : Site → Fin 4 → ℂ) (ρ : Fin 4) : Site → ℂ := fun y => C y ρ

/-- F4D1a：差分保减法。 -/
theorem dF_sub (μ : Fin 4) (f g : Site → ℂ) : dF μ (f - g) = dF μ f - dF μ g := by
  funext x
  simp only [dF, d, Pi.sub_apply]
  ring

/-- F4D1b：差分保加法。 -/
theorem dF_add (μ : Fin 4) (f g : Site → ℂ) : dF μ (f + g) = dF μ f + dF μ g := by
  funext x
  simp only [dF, d, Pi.add_apply]
  ring

/-- F4D1 ★★ **二阶差分可交换**（∂_μ∂_ν = ∂_ν∂_μ 的格点版）。
    「先走 μ 再走 ν」与「先走 ν 再走 μ」到同一个格点（F4D1 的移位可交换）
    ⟹ 二阶差分与顺序无关。**这是本模块全部内容的唯一来源。** -/
theorem d_comm {μ ν : Fin 4} (h : μ ≠ ν) (f : Site → ℂ) :
    dF μ (dF ν f) = dF ν (dF μ f) := by
  funext x
  simp only [dF, d]
  rw [← shift_comm h]
  ring

/-! ### F4D2 场强（流势的旋度）与规范不变性 -/

/-- 场强（流动空间的可观测量）：F_μν = ∂_μC_ν − ∂_νC_μ（流势的旋度）。 -/
def Fstr (C : Site → Fin 4 → ℂ) (μ ν : Fin 4) : Site → ℂ :=
  dF μ (slice C ν) - dF ν (slice C μ)

/-- 规范变换（流动空间版）：把流势整体重标一个梯度 C_μ ↦ C_μ + ∂_μχ。
    物理读法：能测的只有「流变了多少」，流势本身取多少不可测。 -/
def gaugeShift (C : Site → Fin 4 → ℂ) (χ : Site → ℂ) : Site → Fin 4 → ℂ :=
  fun y ρ => C y ρ + d ρ χ y

/-- F4D2 ★★★ **规范不变性**：流势加一个梯度 ⟹ 场强逐点不变。
    ⟹ 在流动空间里，「规范自由度」不是公设，而是「势只有差可测」的直接推论；
       证明只用到 F4D1（二阶差分可交换）。 -/
theorem Fstr_apply (C : Site → Fin 4 → ℂ) (μ ν : Fin 4) (x : Site) :
    Fstr C μ ν x = d μ (slice C ν) x - d ν (slice C μ) x := rfl

theorem Fstr_gauge_invariant {μ ν : Fin 4} (h : μ ≠ ν)
    (C : Site → Fin 4 → ℂ) (χ : Site → ℂ) :
    Fstr (gaugeShift C χ) μ ν = Fstr C μ ν := by
  funext x
  rw [Fstr_apply, Fstr_apply]
  simp only [gaugeShift, slice, d]
  rw [← shift_comm h]
  ring

/-! ### F4D3 四维 Bianchi 恒等式（= 齐次麦克斯韦方程） -/

/-- F4D3 ★★★ **四维 Bianchi 恒等式**：d_μF_νρ + d_νF_ρμ + d_ρF_μν = 0。
    在 3+1 维里这就是 **法拉第定律 + 无磁单极**（齐次麦克斯韦方程），
    而在流动空间里它**不是公设**：它是 F4D1（移位可交换）的三行推论。
    ⟹ 仓库 MaxwellSpace（1+1 维）与 SpaceField3D（静态 3 维）在**含时四维**里合法。 -/
theorem bianchi_4d {μ ν ρ : Fin 4} (hμν : μ ≠ ν) (hμρ : μ ≠ ρ) (hνρ : ν ≠ ρ)
    (C : Site → Fin 4 → ℂ) :
    dF μ (Fstr C ν ρ) + dF ν (Fstr C ρ μ) + dF ρ (Fstr C μ ν) = 0 := by
  unfold Fstr
  rw [dF_sub, dF_sub, dF_sub]
  rw [← d_comm hμν (slice C ρ), d_comm hμρ (slice C ν), d_comm hνρ (slice C μ)]
  abel

/-! ### F4D4 色版（非阿贝尔）：汇不交换 ⟹ 交换子项 -/

/-- 色矩阵流势（每个格点、每个方向一个色矩阵）。 -/
abbrev MatField := Site → Fin 4 → ColorOctet.Mat3C

/-- 矩阵版差分。 -/
def dM (μ : Fin 4) (f : Site → ColorOctet.Mat3C) (x : Site) : ColorOctet.Mat3C :=
  f (Shift μ x) - f x

/-- F4D4a：矩阵差分与整体共轭可交换：d(gAg⁻¹) = g(dA)g⁻¹。 -/
theorem dM_conj (μ : Fin 4) (g : ColorOctet.Mat3C) (C : MatField) (ν : Fin 4) (x : Site) :
    dM μ (fun y => g * C y ν * g⁻¹) x = g * dM μ (fun y => C y ν) x * g⁻¹ := by
  unfold dM
  simp only [mul_sub, sub_mul]

/-- 色版场强（流动空间的非阿贝尔场强）：
    F_μν = ∂_μC_ν − ∂_νC_μ + [C_μ, C_ν]。
    交换子项不是假设 —— 「汇不交换」（YM2/CA3）就是它。 -/
def Fmat (C : MatField) (μ ν : Fin 4) (x : Site) : ColorOctet.Mat3C :=
  dM μ (fun y => C y ν) x - dM ν (fun y => C y μ) x
    + (C x μ * C x ν - C x ν * C x μ)

/-- 整体共轭作用后的流势场。 -/
def conjField (g : ColorOctet.Mat3C) (C : MatField) : MatField :=
  fun y ρ => g * C y ρ * g⁻¹

/-- F4D4b：共轭下乘积可分解（需 g⁻¹g = 1）。 -/
theorem conj_mul (g A B : ColorOctet.Mat3C) (hg' : g⁻¹ * g = 1) :
    (g * A * g⁻¹) * (g * B * g⁻¹) = g * (A * B) * g⁻¹ := by
  rw [show g * A * g⁻¹ * (g * B * g⁻¹) = g * A * (g⁻¹ * g) * B * g⁻¹ by
    noncomm_ring, hg']
  noncomm_ring

/-- F4D4 ★★ **非阿贝尔协变**：流势整体共轭 C_μ ↦ g C_μ g⁻¹ ⟹ F ↦ g F g⁻¹。
    （**局部**变换需链路/plaquette —— 见 `YangMillsFourD.Y4D3`；本定理只到整体。） -/
theorem Fmat_adjoint_covariant (g : ColorOctet.Mat3C) (hg' : g⁻¹ * g = 1)
    (C : MatField) (μ ν : Fin 4) (x : Site) :
    Fmat (conjField g C) μ ν x = g * Fmat C μ ν x * g⁻¹ := by
  change dM μ (fun y => g * C y ν * g⁻¹) x - dM ν (fun y => g * C y μ * g⁻¹) x
      + ((g * C x μ * g⁻¹) * (g * C x ν * g⁻¹) - (g * C x ν * g⁻¹) * (g * C x μ * g⁻¹))
    = g * (dM μ (fun y => C y ν) x - dM ν (fun y => C y μ) x
        + (C x μ * C x ν - C x ν * C x μ)) * g⁻¹
  rw [dM_conj, dM_conj, conj_mul g (C x μ) (C x ν) hg', conj_mul g (C x ν) (C x μ) hg']
  noncomm_ring

/-! ### F4D5 流动空间里的非零场强见证 -/

/-- F4D5 ★ 流动空间里存在非零场强（真四维点上的见证）：
    方向 0 的流势取 cycle3、方向 1 取 diag123（常流），则 F_01 ≠ 0。 -/
theorem flow_field_strength_nonzero :
    ∃ (C : MatField) (μ ν : Fin 4) (x : Site), μ ≠ ν ∧ Fmat C μ ν x ≠ 0 := by
  refine ⟨fun _ ρ => if ρ = 0 then ColorOctet.cycle3
      else ProjectionPhysics.YangMillsContinuum.diag123, 0, 1, fun _ => 0, by decide, ?_⟩
  have hconst : Fmat (fun _ ρ => if ρ = 0 then ColorOctet.cycle3
      else ProjectionPhysics.YangMillsContinuum.diag123) (0 : Fin 4) (1 : Fin 4) (fun _ => 0)
      = ColorOctet.cycle3 * ProjectionPhysics.YangMillsContinuum.diag123
        - ProjectionPhysics.YangMillsContinuum.diag123 * ColorOctet.cycle3 := by
    unfold Fmat dM
    simp
  rw [hconst]
  exact fun hzero =>
    ProjectionPhysics.YangMillsContinuum.cycle3_diag_commutator_ne_zero (by
      unfold ProjectionPhysics.YangMillsContinuum.commutatorTerm
      exact hzero)

/-! ### F4D6 间隙与流动前提无关（负面结果照登） -/

/-- F4D6 ★ 四维流动**不改变**质量间隙：间隙陈述与流动场无关（只依赖计数公设）。
    与 `YangMillsFourD.mass_gap_independent_of_dimension` 同一条，此处以「流动前提」
    的语境重述 —— 提醒：加上「空间在流动」这个前提，也不会生出间隙。 -/
theorem flow_gap_independent {N : ℕ} {M₀ : ℝ} :
    strandMassSq N M₀ = 0 ∨ strandMassSq 1 M₀ ≤ strandMassSq N M₀ :=
  mass_gap_no_intermediate

-- ---------------------------------------------------------------------------
-- F4D7 诚实边界（写死）
--
-- ① **只到整体共轭**：F4D4 的协变是 C_μ ↦ g C_μ g⁻¹（g 与格点无关）。
--    依赖格点的局部变换会额外产生 ∂_μ g 项，必须用链路变量吸收 —— 那是
--    `YangMillsFourD.Y4D3`（plaquette 协变）。两条合起来才是完整的局部规范结构。
--
-- ② **连续极限仍然没有**：本模块全部对象是 ℤ⁴ 上的差分；d_μ → ∂_μ 的极限需要
--    格点指标上的拓扑/度量（框架里没有），与 `YangMillsContinuum:311` 的登记一致。
--
-- ③ **「规范自由度」的物理来源是本模块的实质主张**：流动空间里势只有差可测
--    （电荷 = 流散度，场强 = 流的旋度），所以「加一个梯度看不见」是**流动前提的推论**
--    （F4D2）。这与标准 QFT 把规范不变性当公设不同 —— 这是本模块唯一的新内容，
--    也是唯一可能被反驳的地方：若有人指出流动空间的**可观测量不止于流的变化率**
--    （即存在直接测流势本身的量），F4D2 的物理读法即失效（数学定理仍成立）。
--
-- ④ **不声称**：不解决 Clay；不声称禁闭；不声称 λ/M₀ 被推导；不声称新数值预言。
-- ---------------------------------------------------------------------------

end ProjectionPhysics.FlowFourD
