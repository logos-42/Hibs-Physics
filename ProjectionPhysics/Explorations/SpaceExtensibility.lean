-- ProjectionPhysics — 空间延拓性：空间折叠/压缩域/边界维持（探索）
--
-- leo（2026-08-19）新假设启动：空间的延拓性（空间域差值 / 折叠）。
--   空间是"可伸展、可压缩的橡皮泥"——局部空间密度 ρ 可偏离基线 ρ₀。
--   折叠空间 ⟹ 产生两种势差（空间域差）：边界内部空间比外部大（r>1）。
--   要维持这样的折叠域需要：
--     ① 一个边界（维持内部空间能差）；
--     ② 空间可被局部压缩（压缩流动空间需要能量）；
--     ③ 动态效应：空间一直运动，但可被压缩密度。
--   本模块（v1，最小可运行，空间密度 ρ 锚点）形式化能量预算：
--     SE1  压缩能密度非负；为 0 ⟺ 无折叠（r = 1）
--     SE2  内部空间更大 ⟺ 域差 δ>0 ⟺ 压缩能为正
--     SE3  总压缩能随折叠比、随体积（体积可加 / 单调）
--     SE4  整体统一系统：E_total = 压缩 + 边界 + 旋转；总能 ≥ 每项
--     SE5  ★ 螺旋旋转大场作维持器：旋转能 ≥ 压缩维持成本
--            ⟺ 边界由螺旋场撑住（B = |curl C|，接 SpaceField3D SF5）
--
-- 诚实边界（仓库惯例，概念层）：
--   - 这是"空间密度 / 压缩能"的代数外壳（真但平凡的恒等 + 序关系），
--     不是连续场论、不是拓扑 / 交换闭合、不是能量守恒的动力学方程。
--   - 数值（折叠比扫描 + 能量预算 + 螺旋场维持上限）见
--     scripts/verify_space_extensibility.py。
--   - 势差（空间势 Φ）语言与 3D 离散格点模型是 v2（见本轮计划），
--     不在本模块；本模块只做密度 ρ + 弹性压缩能的最小可运行版。
--
-- 优先级：v1（本模块）→ v2（Φ 势 + 格点数值）。

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.SpaceField3D

namespace ProjectionPhysics.SpaceExtensibility

open ProjectionPhysics.SpaceField3D

noncomputable section

/-! ### 定义：空间延拓性与折叠域的能量预算 -/

/-- 局域压缩能密度：把空间从基线压缩/拉伸到折叠比 r 的成本
    （橡皮泥弹性模型）。w(κ,r) = ½·κ·(r−1)²。
    κ = 空间刚度（正，原材料属性，输入）；r = 折叠比 ρ/ρ₀。 -/
def compressEnergyDensity (κ r : ℝ) : ℝ := (1 / 2) * κ * (r - 1)^2

/-- 域差（折叠超额）：内部空间比外部大的量。δ = r − 1。 -/
def foldExcess (r : ℝ) : ℝ := r - 1

/-- 均匀折叠域的总压缩能：折叠比 r、体积 V。 -/
def totalCompression (κ r V : ℝ) : ℝ := compressEnergyDensity κ r * V

/-- 扩散边界（梯度过渡层）的维持能：正比边界面积 S、界面张力 σ。 -/
def boundaryEnergy (σ S : ℝ) : ℝ := σ * S

/-- 螺旋旋转维持器的旋转能：旋转强度 B（=|curl C|）平方，旋转顺应度 ν。 -/
def rotationEnergy (ν B : ℝ) : ℝ := (1 / 2) * ν * B^2

/-- 整体统一系统总能：压缩 + 边界 + 螺旋旋转。 -/
def totalSystemEnergy (κ r V σ S ν B : ℝ) : ℝ :=
  totalCompression κ r V + boundaryEnergy σ S + rotationEnergy ν B

/-! ### SE1. 压缩能密度非负，且为 0 ⟺ 无折叠 -/

/-- SE1a. 压缩能密度非负：折叠（无论压或拉）都不可能是负成本。 -/
theorem compress_energy_nonneg (κ r : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ compressEnergyDensity κ r := by
  unfold compressEnergyDensity
  positivity

/-- SE1b. 压缩能密度为 0 ⟺ 无折叠（r = 1）：
    折叠比回到基线 ⟺ 不需要花压缩能。 -/
theorem compress_energy_zero_iff_trivial_fold (κ r : ℝ) (hκ : κ ≠ 0) :
    compressEnergyDensity κ r = 0 ↔ r = 1 := by
  unfold compressEnergyDensity
  constructor
  · intro h
    have hhalfk : (1 / 2 : ℝ) * κ ≠ 0 := by
      exact mul_ne_zero (by norm_num) hκ
    have hsq : (r - 1)^2 = 0 := by
      exact (mul_eq_zero.mp h).resolve_left hhalfk
    have hr : r - 1 = 0 := sq_eq_zero_iff.mp hsq
    linarith
  · intro hr
    rw [hr]
    norm_num

/-! ### SE2. 域差：内部空间更大 ⟺ δ>0 ⟺ 压缩能为正 -/

/-- SE2a. 内部空间更大 ⟺ 域差为正：r > 1 ⟺ δ = r−1 > 0。 -/
theorem more_space_iff_positive_excess (r : ℝ) :
    1 < r ↔ 0 < foldExcess r := by
  unfold foldExcess
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- SE2b. 内部空间更大 ⟹ 压缩能为正：折叠域要花正能量维持。 -/
theorem internal_larger_gives_positive_energy (κ r : ℝ) (hκ : 0 < κ) (hr : 1 < r) :
    0 < compressEnergyDensity κ r := by
  unfold compressEnergyDensity
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hsq : 0 < (r - 1)^2 := sq_pos_of_ne_zero (by linarith)
  exact mul_pos (mul_pos hhalf hκ) hsq

/-! ### SE3. 总压缩能：体积可加、随折叠比/体积单调 -/

/-- SE3a. 压缩能对体积可加：两段空间折叠的能量 = 各自之和
    （折叠密度沿体积线性累积——橡皮泥拉得越长成本越高）。 -/
theorem total_compression_additive (κ r V₁ V₂ : ℝ) :
    totalCompression κ r (V₁ + V₂) =
      totalCompression κ r V₁ + totalCompression κ r V₂ := by
  unfold totalCompression compressEnergyDensity
  ring

/-- SE3b. 压缩能随体积单调（κ ≥ 0 时）；外部空间 → 内部折叠域越大，总成本越高。 -/
theorem total_compression_mono_volume (κ r : ℝ) (hκ : 0 ≤ κ)
    (V₁ V₂ : ℝ) (hV : V₁ ≤ V₂) :
    totalCompression κ r V₁ ≤ totalCompression κ r V₂ := by
  unfold totalCompression compressEnergyDensity
  have hw : 0 ≤ (1 / 2) * κ * (r - 1)^2 := by positivity
  exact mul_le_mul_of_nonneg_left hV hw

/-- SE3c. 压缩能密度随折叠比单调（κ ≥ 0，r ≥ 1 时）：
    折叠得越狠（内部空间越大）单价越高。 -/
theorem compress_energy_mono_fold (κ : ℝ) (hκ : 0 ≤ κ) (r₁ r₂ : ℝ)
    (h₁ : 1 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    compressEnergyDensity κ r₁ ≤ compressEnergyDensity κ r₂ := by
  unfold compressEnergyDensity
  have hd : 0 ≤ r₁ - 1 := by linarith
  have hd₂ : r₁ - 1 ≤ r₂ - 1 := by linarith
  have habs : |r₁ - 1| ≤ |r₂ - 1| := by
    rw [abs_of_nonneg hd, abs_of_nonneg (by linarith)]
    exact hd₂
  have hsq : (r₁ - 1)^2 ≤ (r₂ - 1)^2 := sq_le_sq.mpr habs
  have hhalf : 0 ≤ (1 / 2) * κ := by positivity
  exact mul_le_mul_of_nonneg_left hsq hhalf

/-! ### SE4. 整体统一系统：总能 = 压缩 + 边界 + 旋转，总能 ≥ 每项 -/

/-- SE4. 把整个内部空间看成一个统一系统：
    E_total = 压缩 + 边界 + 螺旋旋转；总能 ≥ 每一项
    （能量预算可分解，边界只是其中一块）。 -/
theorem total_ge_each_component (κ r V σ S ν B : ℝ)
    (hcomp : 0 ≤ totalCompression κ r V)
    (hbdry : 0 ≤ boundaryEnergy σ S)
    (hrot : 0 ≤ rotationEnergy ν B) :
    totalCompression κ r V ≤ totalSystemEnergy κ r V σ S ν B ∧
    boundaryEnergy σ S ≤ totalSystemEnergy κ r V σ S ν B ∧
    rotationEnergy ν B ≤ totalSystemEnergy κ r V σ S ν B := by
  unfold totalSystemEnergy
  constructor
  · linarith
  · constructor
    · linarith
    · linarith

/-! ### SE5. 螺旋旋转大场作维持器（平衡态） -/

/-- SE5. ★ 螺旋旋转场维持折叠域：
    若旋转强度 B 足够大（κ(r−1)²V ≤ νB²），则旋转能足以覆盖压缩域差的
    维持成本——边界由螺旋大场撑住，内部空间能差得以保持。
    （这是"维持边界需要多少能量"的答案：至少 = 压缩维持成本，
     由旋转场提供；B 是空间场涡旋强度。） -/
theorem spiral_field_balances_boundary (ν B κ r V : ℝ)
    (h : κ * (r - 1)^2 * V ≤ ν * B^2) :
    totalCompression κ r V ≤ rotationEnergy ν B := by
  unfold totalCompression compressEnergyDensity rotationEnergy
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have h2 : (1 / 2) * (κ * (r - 1)^2 * V) ≤ (1 / 2) * (ν * B^2) :=
    mul_le_mul_of_nonneg_left h hhalf
  simpa [mul_assoc, mul_left_comm, mul_comm] using h2

/-- SE5b. 螺旋场旋转强度 = 空间场涡旋强度 |curl C|（接 SpaceField3D SF5：
    B = curl C = 自旋 = 涡旋）。旋转维持器的代数内核复用磁场恒等。 -/
theorem rotation_strength_is_curl (C : VecField4) (t i j k : ℤ) :
    (B_of C).x t i j k = CurlX C t i j k :=
  magnetic_field_is_curl C t i j k

/-! ### 结论注释 -/

-- SE1–SE5 合读（v1 最小可运行，空间密度 ρ 锚点）：
--   候选 1 ✓（能量预算代数壳）：压缩能密度 ≥ 0、0 ⟺ 无折叠（SE1）；
--             内部更大 ⟺ 域差 > 0 ⟺ 正能量（SE2）；总成本随体积/折叠比
--             单调且可加（SE3）；统一系统总能 = 压缩+边界+旋转（SE4）。
--   候选 2 ✓（螺旋维持器）：旋转能 ≥ 压缩维持成本 ⟺ 边界由螺旋场撑住
--             （SE5），旋转强度 = |curl C|（SE5b 复用 SF5）。
--   候选 3 ✗（诚实缺口，v2）：连续场论 / 拓扑 / 能量守恒动力学 / 势 Φ
--             语言未形式化；κ、ν、σ 是输入参数（第二输入缺口同源）；
--             "边界不明确（弥散梯度层）"在 SE 层由 boundaryEnergy ≥ 0
--             的存在性表述，未建梯度层积分模型（v2 用 ∫|∇ρ|²）。
--   诚实 4 层判定：① 数学恒等/序关系——真但平凡；② 结构对应——弹性
--             介质压缩能（经典连续介质力学重述）；③ 数值匹配——见脚本；
--             ④ 概念重构——"空间可压缩密度 ⟹ 折叠域 = 质量锚定的几何
--             来源"在解释层（接 MinimalCore：质量 = 锚定），不可证伪。
--   框架贡献（解释层）：给"空间延拓性"一个可计算的能量预算语言，
--             与 空间流动（SLS/SM）、自旋涡旋（SF5）、质量锚定（MC）同体系。

end  -- noncomputable section

end ProjectionPhysics.SpaceExtensibility

