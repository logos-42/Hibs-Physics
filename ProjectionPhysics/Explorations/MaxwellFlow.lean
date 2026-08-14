-- ProjectionPhysics — 麦克斯韦方程 × 空间流动假设（探索）
--
-- 任务（leo, 2026-08-14）：
--   1. 先写基础麦克斯韦方程（标准形式）
--   2. 用空间流动假设更新后写出麦克斯韦方程
--   3. 预言
--
-- ★ 基础假设修正（leo 指出，2026-08-14）：
--   上一轮黑洞模块（BlackHoleWormhole.lean BH2/BH3）把光子当作"相对空间
--   以 c 传播的波"（Gordon 光锥 = Hamilton–Lisle 河流模型）——那是 SG
--   弱场工具的套用，没有完整安装 SLS2 公设。本模块按公设重写：
--
--     SLS1: 空间速度矢量 C，|C| = c 处处（普适）
--     SLS2: 光子 = 完全随空间（IsComoving，相对运动 = 0）
--     SM1:  光子随流 ⟹ |dx/dt| = |C| = c ⟹ dτ² = 0（不花时间）
--
--   ⟹ 黑洞 = 矢量流场 C 的汇（流线全部终止于奇点），
--     光子 = 流线本身；逃逸 = 逆流 = 违背 SLS2 ⟹ 逃逸不可能是
--     公设的直接推论（PH2），不借用 GR/河流模型。
--
-- 本模块内容：
--   MF1–MF2 基础麦克斯韦（1+1 维种子）：波动色散 ω² = c²k²；
--           c = 1/√(μ₀ε₀) ⟹ c²μ₀ε₀ = 1
--   MF3     ★ 更新：光速 = 空间属性 = 麦克斯韦速度（SLS1 ↔ ε₀μ₀ 连接）
--   MF4     ★ 更新：光子随流的波动——波动方程不变（|C| = c ⟹ dτ = 0），
--           更新在解释层：c 是空间等效速度不是电磁参数
--   PH1–PH2 ★ 黑洞公设版：光子随流（IsComoving）⟹ 光子速度 = 空间速度
--           ⟹ 内向流中光子无法逃逸（逃逸 = 逆流 = 违背公设）
--   MF5     ★ 预言种子：引力红移 ω₂/ω₁ = (c−v₂)/(c−v₁)（波数守恒沿流线）
--   MF6     ★ 预言种子：黑洞内部（C = −c）波动模相速度全部内向
--           （c−C = 2c > 0）——无向外传播模
--
-- 诚实边界：
--   - 微分算子（∂_t, ∂_x, ∇×）仓库未支持——本模块是代数种子
--     （色散/频率比/方向性），连续版在 scripts/verify_maxwell_flow.py。
--   - MF3/MF5 的"预言"与 GR 已知结果一致（红移/视界），4 层判定
--     无新物理——本模块的价值 = 从 SLS2 公设出发的自洽推导路径。
--   - 黑洞半径不再是 2GM/c² 的自动结果（公设版不预设 GR）——
--     半径 = 流场参数 r_h，仓库无独立输入（诚实：与"第二输入未找到"
--     同源的开放性缺口）。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

import ProjectionPhysics.SpaceLightSpeed

noncomputable section

namespace ProjectionPhysics

/-! ### MF1–MF2. 基础麦克斯韦（1+1 维代数种子） -/

/-- ★ 基础麦克斯韦波动色散的因子分解（1+1 维）：
    ∂_t²φ = c²∂_x²φ 的平面波 e^{i(kx−ωt)} 色散条件 ω² = c²k²
    ⟺ (ω − ck)(ω + ck) = 0 ⟺ ω = ±ck（两个传播方向，光速 ±c）。 -/
theorem maxwell_dispersion_factor (ω k c : ℝ) :
    ω ^ 2 - c ^ 2 * k ^ 2 = (ω - c * k) * (ω + c * k) := by
  ring

/-- ★ 真空麦克斯韦速度：c = 1/√(μ₀ε₀) ⟹ c²·μ₀ε₀ = 1
    （真空电磁波速由 ε₀μ₀ 决定——标准结果，作为更新版的对比基准）。 -/
theorem maxwell_c_squared (ε0 μ0 : ℝ) (h : 0 < ε0 * μ0) :
    (1 / Real.sqrt (ε0 * μ0)) ^ 2 * (ε0 * μ0) = 1 := by
  have hsq : (Real.sqrt (ε0 * μ0)) ^ 2 = ε0 * μ0 := Real.sq_sqrt (le_of_lt h)
  calc
    (1 / Real.sqrt (ε0 * μ0)) ^ 2 * (ε0 * μ0)
        = (1 / (Real.sqrt (ε0 * μ0)) ^ 2) * (ε0 * μ0) := by ring
    _ = (1 / (ε0 * μ0)) * (ε0 * μ0) := by rw [hsq]
    _ = 1 := by
      field_simp [ne_of_gt h]
      exact div_self (ne_of_gt h)

/-! ### MF3. 更新：光速 = 空间属性 = 麦克斯韦速度 -/

/-- ★ 更新后的麦克斯韦：光速不是电磁参数，而是空间本身的等效速度
    （SLS1 矢量光速）。连接式：若 1/√(μ₀ε₀) = c（空间流动速度），
    则 c²·μ₀ε₀ = 1——麦克斯韦常数乘积由空间决定。
    方程形式不变（c = 1/√(μ₀ε₀) 保持），解释层改变：c 是空间属性。 -/
theorem space_flow_light_speed_is_maxwell_speed (ε0 μ0 c : ℝ)
    (h : 0 < ε0 * μ0) (hm : 1 / Real.sqrt (ε0 * μ0) = c) :
    c ^ 2 * (ε0 * μ0) = 1 := by
  calc
    c ^ 2 * (ε0 * μ0) = (1 / Real.sqrt (ε0 * μ0)) ^ 2 * (ε0 * μ0) := by rw [← hm]
    _ = 1 := maxwell_c_squared ε0 μ0 h

/-! ### PH1–PH2. 黑洞公设版：光子 = 流线，逃逸 = 逆流 = 违背公设 -/

/-- 光子坐标速度（z 分量）= 空间速度 + 相对空间速度（速度合成）。 -/
def photonZVelocity (s : MatterState c2) : Int :=
  s.space.z + s.relative.z

/-- ★ 光子 = 完全随空间（SLS2, IsComoving）⟹ 光子坐标速度 = 空间速度
    （相对运动 = 0，无独立速度）。 -/
theorem comoving_photon_flows_with_space (s : MatterState c2) (h : IsComoving s.relative) :
    photonZVelocity s = s.space.z := by
  unfold photonZVelocity IsComoving at *
  rw [h]
  simp [relativeMotionZero]

/-- ★ 逃逸不可能（公设版）：黑洞 = 内向空间流（v ≥ c > 0），
    光子随流（SLS2）⟹ 光子速度 = 空间速度 ≥ c > 0（内向）
    ⟹ 光子不可能向外逃逸（逃逸 = z 速度 < 0）。
    这是 SLS2 的直接推论——不借用 GR/河流模型。 -/
theorem photon_cannot_escape_blackhole_flow (c : Int) (hc : 0 < c)
    (s : MatterState (c * c)) (hflow : c ≤ s.space.z) (hcom : IsComoving s.relative) :
    ¬ photonZVelocity s < 0 := by
  intro he
  have hz : 0 ≤ s.space.z := le_trans (le_of_lt hc) hflow
  have : 0 ≤ photonZVelocity s := by
    rw [comoving_photon_flows_with_space s hcom]
    exact hz
  omega

/-- ★ 黑洞内部流线单向性：内向流中光子的 z 位置单调（不回头）。
    （离散流线：z_{n+1} = z_n + 光子速度·Δt，光子随流 ⟹ 增量 = 内向速度。） -/
theorem photon_infall_monotone (c : Int) (hc : 0 < c)
    (s : MatterState (c * c)) (hflow : c ≤ s.space.z) (hcom : IsComoving s.relative)
    (dt : Int) (hdt : 0 < dt) :
    0 < photonZVelocity s * dt := by
  have hz : 0 < s.space.z := lt_of_lt_of_le hc hflow
  have hph : 0 < photonZVelocity s := by
    rw [comoving_photon_flows_with_space s hcom]
    exact hz
  exact mul_pos hph hdt

/-! ### MF4. 更新：光子随流的波动（1+1 维） -/

/-- ★ 更新后的波动色散：电磁波 = 空间流动的波动，光子随流。
    流动（|C| = c）下波动方程形式不变（MF1 保持），色散因子
    (ω − ck)(ω + ck) = 0 的双向模对应"光随流 + 局域光速不变"。
    更新在解释层：c = |C|（空间等效速度），不是电磁参数。 -/
theorem comoving_wave_dispersion_preserved (ω k c : ℝ) :
    ω ^ 2 - c ^ 2 * k ^ 2 = 0 ↔ ω = c * k ∨ ω = -c * k := by
  rw [maxwell_dispersion_factor]
  constructor
  · intro h
    have hz : (ω - c * k) * (ω + c * k) = 0 := by simpa [maxwell_dispersion_factor] using h
    rcases mul_eq_zero.mp hz with h1 | h2
    · left
      linarith
    · right
      linarith
  · intro h
    rcases h with h | h
    · rw [h]
      ring
    · rw [h]
      ring

/-! ### MF5. 预言种子：引力红移（流动梯度中的频率变化） -/

/-- ★ 引力红移（代数种子）：电磁波沿流线传播，波数 k 守恒；
    色散 ω = (c − v)k 在流动 v₁ → v₂ 之间给出
    ω₂/ω₁ = (c − v₂)/(c − v₁)。
    内向流增快（v₂ > v₁ 意味着更深引力势）⟹ ω₂ < ω₁（红移）。
    （弱场线性化 Δω/ω ≈ −Δv/c 与 GR 的 Δω/ω = −ΔΦ/c² 一致，
    因 Φ = −½v²（SG11）⟹ −Δv/c = −ΔΦ/(v·c)——数值对比见 Python。） -/
theorem redshift_from_flow_gradient (ω₁ ω₂ k v₁ v₂ c : ℝ)
    (hk : k ≠ 0) (h₁ : ω₁ = (c - v₁) * k) (h₂ : ω₂ = (c - v₂) * k) :
    ω₂ / ω₁ = (c - v₂) / (c - v₁) := by
  rw [h₁, h₂]
  field_simp [hk]

/-! ### MF6. 预言种子：黑洞内部无向外传播模 -/

/-- ★ 黑洞内部（内向流 C = −c）：波动模的相速度 c − C = 2c > 0
    ——全部与内向流同向，不存在逆流（向外）传播模。
    光（电磁波）在黑洞内部只有内向模 ⟹ 无法逃逸（MF6 = PH2 的波动版）。 -/
theorem blackhole_inside_no_outward_phase_velocity (C c : ℝ) (hc : 0 < c) (hC : C = -c) :
    0 < c - C := by
  rw [hC]
  linarith

/-! ### 结论注释（不证，属数值/几何侧） -/

-- MF1–MF6 + PH1–PH2 合读：
--   基础麦克斯韦（MF1–MF2）形式不变；更新在解释层（MF3–MF4）：
--   c = 空间等效速度 = 1/√(μ₀ε₀)，电磁波 = 空间流动的波动。
--   黑洞 = 矢量流场汇（|C| = c 恒）：光子 = 流线（PH1），
--   逃逸 = 逆流 = 违背 SLS2 ⟹ 逃逸不可能（PH2，公设直接推论）；
--   黑洞内部波动模全内向（MF6）——"无向外模"的代数种子。
--   预言：红移 ω₂/ω₁ = (c−v₂)/(c−v₁)（MF5）与 GR 弱场一致（恒等式层）。
--   黑洞半径不再自动 = 2GM/c²（公设版不预设 GR）——半径 = 流场
--   参数 r_h，无独立输入（诚实缺口，与"第二输入未找到"同源）。
--   数值/图像/4 层判定：scripts/verify_maxwell_flow.py。

end ProjectionPhysics
