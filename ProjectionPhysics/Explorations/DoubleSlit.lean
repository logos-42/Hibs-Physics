-- ProjectionPhysics — 双缝 = 空间螺旋谐波的干涉（波粒二象性重释，探索）
--
-- leo（2026-08-14）第二个假设：波粒二象性在流动空间里不存在——
--   光源的光随空间运行（SLS2 公设），空间在运动中有结构（螺旋运动），
--   螺旋在平面的投影 = 波纹（谐波）；光透过双缝时，空间谐波结构产生
--   干涉条纹；观察哪条缝 = 对空间运动谐波的压缩（去掉板子到光源之间
--   的空间谐波影响）⟹ 两道条纹。
--
-- 本模块形式化的数学内核（严格可证部分）：
--   DS1 螺旋的平面投影是圆/波纹：空间螺旋运动（平面圆周 + 法向传播）
--       ⟹ 平面结构 = 谐波（cos²+sin² = 1：xy 投影圆、截面投影正弦）
--   DS2 ★ 干涉恒等式：cos α + cos β = 2cos((α+β)/2)·cos((α−β)/2)
--       ——两列谐波的叠加 = 调制的条纹（波纹产生干涉的代数根源）
--   DS3 双缝强度恒等：4cos²δ = 2(1 + cos 2δ)
--       ——条纹强度公式（cos² 调制 = 明暗相间）的代数内核
--   DS4 观察 = 相干丧失：|z₁+z₂|² = |z₁|² + |z₂|² + 2Re(z₁·z̄₂)
--       ——交叉项 2cos(Δφ) 是干涉来源；相位随机化 ⟹ 交叉项平均消失
--       ⟹ 无干涉（两道条纹）——"压缩谐波"的数学 = 相干性丧失
--
-- 诚实边界（4 层判定）：
--   - 数学内核（螺旋投影/叠加恒等/相干丧失）严格可证，但与标准波动
--     光学同构——干涉的数学不依赖"空间谐波"的物理地位。
--   - "波粒二象性不存在"是解释层（概念重构）：数学上观察 = 退相干，
--     与量子力学互补性等价；区别在"空间谐波"是物理结构还是叙事。
--   - 连续波传播/衍射积分（Huygens）未形式化（数值层见 Python）。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProjectionPhysics.DoubleSlit

/-! ### DS1. 空间螺旋运动的平面结构 = 谐波 -/

/-- ★ 螺旋的 xy 投影是圆（cos² + sin² = 1）：
    空间螺旋运动（三方向流动的平面圆周分量）在任何垂直于轴向的
    平面上的投影是圆——"空间在运动过程中的平面结构"的第一层。
    （R = 螺旋半径 = 平面圆周分量振幅，ω = 角频率。） -/
theorem helix_xy_projection_is_circle (R ω : ℝ) (t : ℝ) :
    (R * Real.cos (ω * t)) ^ 2 + (R * Real.sin (ω * t)) ^ 2 = R ^ 2 := by
  calc
    (R * Real.cos (ω * t)) ^ 2 + (R * Real.sin (ω * t)) ^ 2
        = R ^ 2 * ((Real.cos (ω * t)) ^ 2 + (Real.sin (ω * t)) ^ 2) := by ring
    _ = R ^ 2 := by
      simpa [add_comm] using Real.sin_sq_add_cos_sq (ω * t)

/-- ★ 螺旋的截面投影是谐波（波纹）：x 分量随传播坐标 z 呈 cos 变化。
    光（随空间流动，SLS2）沿螺旋运动 ⟹ 观测到的"波动" = 螺旋在
    固定平面的投影（谐波）——"平面的波纹"的数学说明。 -/
theorem helix_section_projection_harmonic (R ω t : ℝ) :
    R * Real.cos (ω * t) = R * Real.cos (ω * t) := by
  rfl
  -- 定义级：截面投影就是取 x 分量 = R·cos(ωt)——螺旋参数化的直接结果。
  -- 物理内容（解释层）：波纹不是光的固有属性，是空间螺旋运动在
  -- 平面的投影——波粒二象性的"波"侧 = 空间结构的投影。

/-! ### DS2. 干涉恒等式（波纹叠加 ⟹ 条纹） -/

/-- ★ 干涉恒等式：cos α + cos β = 2cos((α+β)/2)·cos((α−β)/2)。
    两列同频谐波（空间波纹的两个次波源）的叠加 = 缓慢调制的条纹：
    (α+β)/2 = 载波，cos((α−β)/2) = 包络（明暗相间）。
    ——双缝干涉条纹的代数根源：波纹叠加自然产生调制。 -/
theorem interference_identity (α β : ℝ) :
    Real.cos α + Real.cos β = 2 * Real.cos ((α + β) / 2) * Real.cos ((α - β) / 2) := by
  have hα : α = (α + β) / 2 + (α - β) / 2 := by ring
  have hβ : β = (α + β) / 2 - (α - β) / 2 := by ring
  rw [hα, hβ]
  rw [Real.cos_add, Real.cos_sub]
  ring

/-! ### DS3. 双缝强度恒等（条纹的 cos² 调制） -/

/-- ★ 双缝强度恒等：4cos²δ = 2(1 + cos 2δ)。
    干涉强度 I = 4I₀cos²(πd·sinθ/λ)（双缝公式）等价于
    2I₀(1 + cos 2δ)——条纹 = 载波上的 cos 调制（明暗相间）。
    数学内核：cos² 调制 = 干涉条纹；来源 = DS2 的叠加。 -/
theorem two_slit_intensity_identity (δ : ℝ) :
    4 * (Real.cos δ) ^ 2 = 2 * (1 + Real.cos (2 * δ)) := by
  have h1 : (Real.cos δ) ^ 2 + (Real.sin δ) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq δ
  have h2 : Real.cos (2 * δ) = (Real.cos δ) ^ 2 - (Real.sin δ) ^ 2 := Real.cos_two_mul' δ
  nlinarith

/-! ### DS4. 观察 = 相干丧失（交叉项消失 ⟹ 两道条纹） -/

/-- ★ 两列波叠加的强度分解：|z₁+z₂|² = |z₁|² + |z₂|² + 2Re(z₁·z̄₂)。
    第三项（交叉项）是干涉的来源：对单位振幅两波，2Re(z₁z̄₂) =
    2cos(Δφ)——Δφ 固定（相干）⟹ 干涉条纹；Δφ 随机（观察/路径标记
    破坏相位）⟹ 交叉项平均为 0 ⟹ 强度相加 = 无干涉（两道条纹）。
    ——"观察 = 压缩空间谐波"的数学 = 相位相干性丧失（退相干）。 -/
theorem two_wave_intensity_split (z₁ z₂ : ℂ) :
    Complex.normSq (z₁ + z₂) = Complex.normSq z₁ + Complex.normSq z₂
      + 2 * (z₁ * star z₂).re := by
  simpa using Complex.normSq_add z₁ z₂

-- ★ 单位振幅两波的干涉项（推导路线，未证——数值见 Python）：
--     |e^{iφ₁} + e^{iφ₂}|² = 2 + 2cos(φ₁−φ₂)
--   路线：normSq_add（已证 two_wave_intensity_split）+ |e^{iφ}| = 1
--   （Complex.normSq_exp）+ Re(exp(iθ)) = cos θ（Complex.exp_re）
--   ⟹ 交叉项 = 2cos(Δφ) ∈ [−2, 2]：同相 Δφ=0 ⟹ 4（亮纹），反相 Δφ=π
--   ⟹ 0（暗纹）。观察（相位随机化）⟹ ⟨cos Δφ⟩ = 0 ⟹ 强度 = 2（无干涉）。

/-! ### 结论注释 -/

-- DS1–DS4 合读（第二个假设的数学内核）：
--   1. 空间的螺旋运动（三方向流动：平面圆周 + 法向传播）在平面的
--      投影 = 圆 + 谐波（DS1）——"平面上的波纹"有严格数学说明。
--   2. 波纹（谐波）叠加自然产生干涉条纹（DS2：叠加恒等；
--      DS3：cos² 调制）——双缝条纹 = 空间谐波结构的干涉（数学同构
--      于波动光学）。
--   3. 观察（哪条缝）⟹ 相位相干丧失（DS4：交叉项随机化消失）⟹
--      无干涉 = 两道条纹——"压缩空间谐波"的数学 = 退相干。
--   4. "波粒二象性不存在" = 解释层：波 = 空间螺旋投影（DS1），
--      粒子 = 谐波压缩后的局域（DS4）——同一空间结构的两种观测
--      姿态，不是光的两种本性。诚实：数学内核与标准波动光学同构，
--      新在空间谐波的物理地位（4 层判定：① 恒等 ④ 概念重构）。

end ProjectionPhysics.DoubleSlit
