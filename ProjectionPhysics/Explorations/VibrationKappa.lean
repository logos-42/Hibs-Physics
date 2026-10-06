-- ProjectionPhysics — VibrationKappa：振动本体给出的 κ 候选不能自动唯一化
--
-- 本模块只做形式化证明，不使用 Python 数值作为证明：
--   VK1  色散缺陷 Δ(c,k,ω) = c²k² − ω²；光锥 ω=c·k ⟹ Δ=0
--   VK2  sech² 包络曲率候选 K(c_env)=c_env/2；c_env>0 ⟹ K>0
--   VK3  在同一光锥振动上 Δ=0 而 K>0 ⟹ 两个候选不能由现有结构自动等同
--   VK4  若把 κ 选为 Δ，则光锥上 κ=0；若选为 K，则 κ>0
--        ⟹ 现有振动本体尚未选择唯一 κ 映射
--
-- 诚实边界：这是候选映射的形式化否定/分叉证明，不是质量定理；
-- 没有新增公设，没有证明哪一个候选才是物理 κ。

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProjectionPhysics.VibrationKappa

noncomputable section

/-- 色散缺陷：线性波动方程的壳外偏离量。 -/
def dispersionDefect (c k omega : ℝ) : ℝ :=
  c ^ 2 * k ^ 2 - omega ^ 2

/-- sech² 包络族的曲率候选：K_shape = c_env / 2。 -/
def envelopeCurvature (cEnv : ℝ) : ℝ :=
  cEnv / 2

/-- VK1：光锥色散关系 ω=c·k 使色散缺陷严格为零。 -/
theorem dispersionDefect_on_lightcone (c k : ℝ) :
    dispersionDefect c k (c * k) = 0 := by
  unfold dispersionDefect
  ring

/-- VK2：正包络参数给出严格正的曲率候选。 -/
theorem envelopeCurvature_pos {cEnv : ℝ} (hc : 0 < cEnv) :
    0 < envelopeCurvature cEnv := by
  unfold envelopeCurvature
  linarith

/-- VK3：同一光锥振动上，两个 κ 候选可以严格分离：Δ=0 而 K>0。 -/
theorem candidates_separate {c k cEnv : ℝ} (hcEnv : 0 < cEnv) :
    dispersionDefect c k (c * k) ≠ envelopeCurvature cEnv := by
  have hzero : dispersionDefect c k (c * k) = 0 :=
    dispersionDefect_on_lightcone c k
  have hpos : 0 < envelopeCurvature cEnv :=
    envelopeCurvature_pos hcEnv
  rw [hzero]
  exact (ne_of_gt hpos).symm

/-- VK4：若 κ 选色散缺陷，光锥上为零；若 κ 选包络曲率，则为正。 -/
theorem candidate_value_split {c k cEnv : ℝ} (hcEnv : 0 < cEnv) :
    dispersionDefect c k (c * k) = 0 ∧
      0 < envelopeCurvature cEnv := by
  exact ⟨dispersionDefect_on_lightcone c k,
    envelopeCurvature_pos hcEnv⟩

/-- VK5：不可能在现有定义下证明两个候选恒等，因为存在显式分离实例。 -/
theorem no_candidate_identity :
    ¬ (∀ c k cEnv : ℝ,
      dispersionDefect c k (c * k) = envelopeCurvature cEnv) := by
  intro h
  have hEq := h 1 1 2
  have hD : dispersionDefect 1 1 (1 * 1) = 0 :=
    dispersionDefect_on_lightcone 1 1
  have hK : envelopeCurvature 2 = 1 := by
    unfold envelopeCurvature
    norm_num
  rw [hD, hK] at hEq
  norm_num at hEq

end
end ProjectionPhysics.VibrationKappa
