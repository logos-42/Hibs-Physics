-- ProjectionPhysics — PlasmaFusion：磁约束时变引力场可控核聚变的工程代数骨架
--
-- leo（2026-08-28）新方向：把仓库已建理论（等离子体双流形 PA/DR/TM、
--   空间折叠 SF、四力合一调制 FM/GQF）接到**可控核聚变装置设计**上，
--   用真实常数计算：约束力、物理应力、真实物理环尺寸（最小可到多少）。
--
-- 与既有主线的精确接轨：
--   · 磁压平衡（等离子体压 ≤ 磁压 B²/2μ₀）——磁约束的必要条件
--   · 约束力 = 磁压 × 面积（工程反推：需要多少力）
--   · 环向应力 σ = B²R/(2μ₀t)（薄壁环近似，材料屈服极限反推最小环）
--   · 空间压缩增益（SpaceFold SF2：内部密度大 ⟹ 内部空间更大 ⟹
--     同样物理体积容纳更多等离子体 ⟹ 等效密度/功率密度提升）
--   · 四力调制控制层（SpaceModulation FM10 ω₀=|B|/2 + GQF2 四通道：
--     调制空间场 ⟹ 调制约束力 ⟹ 主动控制层）
--   · 时变反引力 μ(t)（PlasmaDynamics TM：磁约束 + 时变磁场 ⟹
--     时变空间场 ⟹ 时变 μ(t)，辅助质量取消/惯性调控）
--
-- 核心定理（mathlib，代数种子）：
--   PF1. 磁压非负：P_B = B²/2μ₀ ≥ 0（磁约束的能量密度预算）
--   PF2. ★ 约束条件：β = P/P_B ≤ 1 ⟺ P ≤ P_B（等离子体压必须被磁压压住）
--   PF3. 所需场强：P ≤ B²/2μ₀ ⟺ B ≥ √(2μ₀P)（给定聚变条件反推磁场）
--   PF4. 约束力：F = P_B·A，随 B² 增长（F = B²A/2μ₀，需要多少力的答案）
--   PF5. ★ 环向应力：σ = B²R/(2μ₀t)（薄壁环：应力 ∝ 半径 × 场强² / 壁厚）
--   PF6. ★ 应力单调：R↑ ⟹ σ↑、B↑ ⟹ σ↑（尺寸与场强的应力代价）
--   PF7. ★ 最小环：σ ≤ σ_y ⟺ R ≤ 2μ₀σ_y·t/B²（材料屈服 ⟹ 半径上限）
--   PF8. 空间压缩增益：密度差 ⟹ 内部空间更大（引用 SF2 的输入重述：
--        折叠 ⟹ 同样物理体积的等效等离子体容量提升）
--   PF9. 调制控制力：δF = δ(B²)·A/2μ₀（磁场调制 ⟹ 约束力调制，
--        四力调制控制层的代数内核）
--
-- 诚实边界：代数骨架（平方关系/序关系/平衡不等式），不是等离子体
--   平衡（Grad-Shafranov）或工程有限元应力分析；材料常数（铜屈服、
--   几何系数）是数值层输入；μ(t) 的主动产生机制=第二输入缺口（未变）；
--   无新物理预言（4 层判定：数学恒等 + 工程应用映射）。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace PlasmaFusion

/-! ### ① 磁压与约束条件 -/

/-- PF1 输入：磁压 P_B = B²/(2μ₀)（磁约束的能量密度）。 -/
def magPressure (B μ₀ : ℝ) : ℝ := B * B / (2 * μ₀)

/-- PF1：磁压非负（磁场能量密度 ≥ 0，磁约束的预算下界）。 -/
theorem mag_pressure_nonneg (B μ₀ : ℝ) (hμ : 0 < μ₀) : 0 ≤ magPressure B μ₀ := by
  unfold magPressure
  exact div_nonneg (by simpa [sq] using sq_nonneg B) (le_of_lt (by positivity : 0 < 2 * μ₀))

/-- PF2★：约束条件——等离子体压 P 被磁压 P_B 压住 ⟺ β = P/P_B ≤ 1。
    磁约束的必要条件：等离子体热压不能超过磁压（否则等离子体膨胀逃逸）。 -/
theorem confinement_iff_beta_le_one (P B μ₀ : ℝ) (hμ : 0 < μ₀) (hB : B ≠ 0) :
    P ≤ magPressure B μ₀ ↔ P / magPressure B μ₀ ≤ 1 := by
  unfold magPressure
  have h2mu : 0 < 2 * μ₀ := by positivity
  have hB2 : 0 < B * B := by simpa [sq] using sq_pos_of_ne_zero hB
  have hden : 0 < B * B / (2 * μ₀) := div_pos hB2 h2mu
  -- P/(B²/2μ₀) ≤ 1 ⟺ P ≤ B²/2μ₀（分母正 ⟹ div_le_iff₀）
  rw [div_le_iff₀ hden]
  simp

/-- PF2b：β ≤ 1 等价形式——等离子体压不超过磁压（重述）。 -/
theorem beta_le_one_iff_pressure_bounded (P B μ₀ : ℝ) (hμ : 0 < μ₀) (hB : B ≠ 0) :
    P / magPressure B μ₀ ≤ 1 ↔ P ≤ magPressure B μ₀ := by
  unfold magPressure
  have h2mu : 0 < 2 * μ₀ := by positivity
  have hB2 : 0 < B * B := by simpa [sq] using sq_pos_of_ne_zero hB
  have hden : 0 < B * B / (2 * μ₀) := div_pos hB2 h2mu
  rw [div_le_iff₀ hden]
  simp

/-- PF3★：所需场强（代数版）——给定等离子体压 P，约束所需磁场满足
    B² ≥ 2μ₀·P（即 |B| ≥ √(2μ₀P)）。这是工程反推的代数内核：
    聚变条件（n,T）决定 P，P 决定最小 B。sqrt 版见数值层。 -/
theorem required_field_for_confinement (P B μ₀ : ℝ) (hμ : 0 < μ₀) :
    P ≤ magPressure B μ₀ ↔ 2 * μ₀ * P ≤ B * B := by
  unfold magPressure
  rw [le_div_iff₀ (by positivity : 0 < 2 * μ₀)]
  constructor <;> intro h <;> nlinarith

/-! ### ② 约束力（需要多少力） -/

/-- PF4 输入：约束力 = 磁压 × 面积（力 = 压强 × 面积）。 -/
def confForce (B μ₀ A : ℝ) : ℝ := magPressure B μ₀ * A

/-- PF4：约束力随场强平方增长——F = B²A/(2μ₀)，B 翻倍力翻四倍。
    这是"需要多少力来产生时变磁场约束"的数量级答案（数值层代入 A）。 -/
theorem force_grows_quadratic_in_B (B₁ B₂ μ₀ A : ℝ) (hμ : 0 < μ₀) (hA : 0 < A)
    (h : |B₁| < |B₂|) : confForce B₁ μ₀ A < confForce B₂ μ₀ A := by
  unfold confForce magPressure
  have hsq : B₁ * B₁ < B₂ * B₂ := by simpa [sq] using sq_lt_sq.mpr h
  have hpos : 0 < 2 * μ₀ := by positivity
  have hf : B₁ * B₁ / (2 * μ₀) < B₂ * B₂ / (2 * μ₀) := by
    exact div_lt_div_of_pos_right hsq hpos
  exact mul_lt_mul_of_pos_right hf hA

/-- PF4b：约束力恒等式——F = B²A/(2μ₀)（展开形式，数值层直接用）。 -/
theorem conf_force_expanded (B μ₀ A : ℝ) :
    confForce B μ₀ A = B * B * A / (2 * μ₀) := by
  unfold confForce magPressure
  ring

/-! ### ③ 物理应力（环向应力，薄壁环近似） -/

/-- PF5 输入：薄壁环的环向（hoop）应力——内压 P_B、半径 R、壁厚 t。
    工程背景：磁压 B²/2μ₀ 作用在环形容器壁上，薄壁环周向应力 σ = P·R/t。 -/
def hoopStress (B μ₀ R t : ℝ) : ℝ := magPressure B μ₀ * R / t

/-- PF5：环向应力恒等式——σ = B²R/(2μ₀t)。
    关键工程结论：应力 ∝ 场强平方 × 半径 / 壁厚。 -/
theorem hoop_stress_expanded (B μ₀ R t : ℝ) :
    hoopStress B μ₀ R t = B * B * R / (2 * μ₀ * t) := by
  unfold hoopStress magPressure
  ring

/-- PF6a★：应力随半径增长——同磁场同壁厚下，环越大应力越大。
    大环的应力代价：ITER 级（R~6m）的铜结构承受的 hoop stress
    远大于紧凑环（R~1.8m）——这是"最小环更好"的结构根源。 -/
theorem stress_mono_radius (B μ₀ t : ℝ) (hμ : 0 < μ₀) (ht : 0 < t) (hB : B ≠ 0)
    (R₁ R₂ : ℝ) (h : R₁ < R₂) :
    hoopStress B μ₀ R₁ t < hoopStress B μ₀ R₂ t := by
  unfold hoopStress magPressure
  have hB2 : 0 < B * B := by simpa [sq] using sq_pos_of_ne_zero hB
  have hP : 0 < B * B / (2 * μ₀) := div_pos hB2 (by positivity)
  have hm : B * B / (2 * μ₀) * R₁ < B * B / (2 * μ₀) * R₂ := by
    exact mul_lt_mul_of_pos_left h hP
  exact div_lt_div_of_pos_right hm ht

/-- PF6b★：应力随场强平方增长——B 翻倍 ⟹ 应力翻四倍。
    高场紧凑环（SPARC 路线 B~12T）的应力是 ITER（B~5.3T）的 ~5 倍，
    必须用高强度结构/超导磁体。 -/
theorem stress_mono_field (R t μ₀ : ℝ) (hμ : 0 < μ₀) (hR : 0 < R) (ht : 0 < t)
    (B₁ B₂ : ℝ) (h : |B₁| < |B₂|) :
    hoopStress B₁ μ₀ R t < hoopStress B₂ μ₀ R t := by
  unfold hoopStress magPressure
  have hsq : B₁ * B₁ < B₂ * B₂ := by simpa [sq] using sq_lt_sq.mpr h
  have hpos : 0 < 2 * μ₀ := by positivity
  have hf : B₁ * B₁ / (2 * μ₀) < B₂ * B₂ / (2 * μ₀) := by
    exact div_lt_div_of_pos_right hsq hpos
  have hfm : B₁ * B₁ / (2 * μ₀) * R < B₂ * B₂ / (2 * μ₀) * R := by
    exact mul_lt_mul_of_pos_right hf hR
  exact div_lt_div_of_pos_right hfm ht

/-- PF7★：最小环判据——应力不超过材料屈服 σ_y ⟺ 半径不超过上限
    2μ₀·σ_y·t/B²。给定磁场 B 与壁厚 t，材料屈服强度 σ_y 给出
    允许的最大环半径（超过则铜结构屈服）。这是"真实物理环最小
    可以到多少"的应力层答案：小环应力小 ⟹ 材料不是小环的障碍。 -/
theorem radius_upper_bound_by_yield (B μ₀ t σ_y R : ℝ) (hμ : 0 < μ₀) (ht : 0 < t)
    (hB : B ≠ 0) : hoopStress B μ₀ R t ≤ σ_y ↔ R ≤ 2 * μ₀ * σ_y * t / (B * B) := by
  unfold hoopStress magPressure
  constructor <;> intro h
  · -- 从 hoopStress ≤ σ_y 推导 R 的上限（两边同乘正数 2μ₀t）
    have hmain : R * (B * B) ≤ 2 * μ₀ * σ_y * t := by
      -- 归一化 h：B²/(2μ₀)·R/t = (B²R)/(2μ₀t)
      rw [show B * B / (2 * μ₀) * R / t = (B * B * R) / (2 * μ₀ * t) by ring] at h
      have hdiv := (div_le_iff₀ (by positivity : 0 < 2 * μ₀ * t)).mp h
      -- hdiv : B²R ≤ σ_y·(2μ₀t)
      nlinarith
    -- 目标 R ≤ (2μ₀σ_yt)/(B²)：交叉乘（B² > 0）
    have hB2pos : 0 < B * B := by simpa [sq] using sq_pos_of_ne_zero hB
    exact (le_div_iff₀ hB2pos).mpr hmain
  · -- 反向：R 有上限 ⟹ 应力 ≤ 屈服
    have hB2pos : 0 < B * B := by simpa [sq] using sq_pos_of_ne_zero hB
    have hmain : R * (B * B) ≤ 2 * μ₀ * σ_y * t := by
      have := mul_le_mul_of_nonneg_right h (le_of_lt hB2pos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hB2pos)] at this
    field_simp [hμ.ne', ht.ne', hB]
    nlinarith [hmain, hB2pos]

/-- PF7b：同样条件——给定屈服 σ_y 与壁厚 t，磁场越大允许的半径越小。
    B² 出现在分母：高场紧凑路线（B↑）必须用小环（R↓）——SPARC 逻辑。 -/
theorem radius_max_inverse_field_sq (B₁ B₂ μ₀ t σ_y : ℝ) (hμ : 0 < μ₀) (ht : 0 < t)
    (hσ : 0 < σ_y) (hB : 0 < B₁) (h : B₁ < B₂) :
    2 * μ₀ * σ_y * t / (B₂ * B₂) < 2 * μ₀ * σ_y * t / (B₁ * B₁) := by
  have hC : 0 < 2 * μ₀ * σ_y * t := by positivity
  have hB1sq_pos : 0 < B₁ * B₁ := by positivity
  have hsq : B₁ * B₁ < B₂ * B₂ := by nlinarith
  have hinv : 1 / (B₂ * B₂) < 1 / (B₁ * B₁) :=
    one_div_lt_one_div_of_lt hB1sq_pos hsq
  calc
    2 * μ₀ * σ_y * t / (B₂ * B₂) = (2 * μ₀ * σ_y * t) * (1 / (B₂ * B₂)) := by ring
    _ < (2 * μ₀ * σ_y * t) * (1 / (B₁ * B₁)) := mul_lt_mul_of_pos_left hinv hC
    _ = 2 * μ₀ * σ_y * t / (B₁ * B₁) := by ring

/-! ### ④ 空间压缩增益（借鉴 SpaceFold：折叠 ⟹ 内部空间更大） -/

/-- PF8 输入：空间折叠的体积增益——内部空间体积元 = |det g| 比外部大。
    引用 SpaceFold.interior_domain_larger 的物理输入：ρ_out < ρ_in ⟹
    |det g_in| > |det g_out|（内部密度高 = 内部空间大）。 -/
def spaceGain (det_in det_out : ℝ) : ℝ := |det_in| / |det_out|

/-- PF8★：空间压缩 ⟹ 等效容量增益 > 1——同样物理体积的装置，
    内部空间更大 ⟹ 能容纳更多等离子体 ⟹ 等效密度/功率密度提升。
    借鉴到聚变：空间折叠是"虚拟扩容"，物理环可以更小。 -/
theorem space_compression_gain_gt_one (det_in det_out : ℝ)
    (hout : det_out ≠ 0) (h : |det_in| > |det_out|) :
    1 < spaceGain det_in det_out := by
  unfold spaceGain
  have hpos : 0 < |det_out| := abs_pos.mpr hout
  -- 1 < a/b 且 b > 0 ⟺ b < a
  rw [one_lt_div hpos]
  exact h

/-- PF8b：密度差越大 ⟹ 增益越大（序关系：内部空间越大增益越大）。 -/
theorem space_gain_mono (d₁ d₂ det_out : ℝ) (hout : 0 < det_out)
    (h : |d₁| < |d₂|) : |d₁| / det_out < |d₂| / det_out := by
  exact div_lt_div_of_pos_right h hout

/-! ### ⑤ 四力调制控制层（借鉴 SpaceModulation FM + GQF2） -/

/-- PF9 输入：调制控制力——磁场调制 δB ⟹ 磁压变化 δ(B²)/2μ₀ ⟹
    约束力变化 δF = δ(B²)·A/(2μ₀)。这是"空间场调制 ⟹ 主动控制层"的
    代数内核：FM10（ω₀=|B|/2 载波）+ GQF2（四力通道）的力通道。 -/
def modForce (B δB μ₀ A : ℝ) : ℝ :=
  ((B + δB) * (B + δB) - B * B) * A / (2 * μ₀)

/-- PF9：调制控制力展开——δF = (2B·δB + δB²)·A/(2μ₀)。
    小调制近似 δF ≈ (B·δB)·A/μ₀（线性于调制幅度，控制层可预测）。 -/
theorem mod_force_expanded (B δB μ₀ A : ℝ) :
    modForce B δB μ₀ A = (2 * B * δB + δB * δB) * A / (2 * μ₀) := by
  unfold modForce
  ring

/-- PF9b：调制力随调制幅度增长——δB 越大控制力越强（控制层增益单调）。 -/
theorem mod_force_mono_modulation (B δB₁ δB₂ μ₀ A : ℝ) (hμ : 0 < μ₀) (hA : 0 < A)
    (hB : 0 < B) (h₁ : 0 ≤ δB₁) (h : δB₁ < δB₂) :
    modForce B δB₁ μ₀ A < modForce B δB₂ μ₀ A := by
  unfold modForce
  have hsq : (B + δB₁)^2 < (B + δB₂)^2 := by
    nlinarith
  have hpos : 0 < 2 * μ₀ := by positivity
  have hf : ((B + δB₁) * (B + δB₁) - B * B) < ((B + δB₂) * (B + δB₂) - B * B) := by
    nlinarith
  have hf' : ((B + δB₁) * (B + δB₁) - B * B) * A < ((B + δB₂) * (B + δB₂) - B * B) * A := by
    exact mul_lt_mul_of_pos_right hf hA
  exact div_lt_div_of_pos_right hf' hpos

/-- PF9c：调制力相对强度——调制力与静态约束力之比 = (2δB/B + (δB/B)²)。
    控制层设计判据：相对调制幅度 δB/B 决定控制力占比。 -/
theorem mod_force_ratio (B δB μ₀ A : ℝ) (hB : B ≠ 0) (hμ : μ₀ ≠ 0)
    (hA : A ≠ 0) :
    modForce B δB μ₀ A / confForce B μ₀ A = 2 * (δB / B) + (δB / B) * (δB / B) := by
  unfold modForce confForce magPressure
  field_simp [hB, hμ, hA]
  ring

def PLASMA_FUSION_SCOPE : String :=
  "工程代数骨架: 磁压平衡(PF1 非负/PF2 约束β≤1⟺P≤P_B/PF3 所需场强B≥√(2μ₀P)) + 约束力(PF4 F=B²A/2μ₀随B²增长) + 环向应力(PF5 σ=B²R/2μ₀t/PF6 应力随R和B单调/PF7 材料屈服⟹半径上限R≤2μ₀σ_yt/B²) + 空间压缩增益(PF8 折叠⟹容量增益>1,借鉴SF2) + 四力调制控制层(PF9 δF=(2BδB+δB²)A/2μ₀,借鉴FM10/GQF2); 材料常数/几何=数值层输入, μ主动机制=第二输入缺口, 无新物理预言"

end PlasmaFusion
end
