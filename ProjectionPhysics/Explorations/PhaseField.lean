-- ProjectionPhysics — PhaseField：相位场 ↔ 空间场 C 的接口代数（PF1–PF5）
--
-- leo（2026-10-01，/loop）：「把波的形状、波本身、相位场、空间场放在一起考虑。
--   相位场在波动过程中的形状如何？本体 = 空间本身在运动，这个运动因为相位场的波形
--   产生了变化。需要从振动本体上开始推导。」
--
-- ── 本轮定位（诚实，写最前面） ────────────────────────────────────────────
--   这不是「KdV 就是空间的动力学方程」——那是断言，需要新公设（本轮没有加）。
--   本模块只做**接口代数**：把「相位场 θ、波形状 sech²、空间场 C」之间那些
--   纯代数的关系钉下来（PF1–PF5）。连续/数值内容（孤子演化、守恒量、形状谱）
--   在数值层 scripts/verify_phase_wave_shape.py（KV1–KV6），Lean 不碰。
--   仓库的波动方程根基 = MS3（∂²C = c²∂²C；theory-maxwell-space.md），
--   相位场 θ 以相速度 c（current-status.md:454）。
--
-- ── 本模块的形式化内容（全部可证，不含新物理） ─────────────────────────────
--   PF1  相位可加：e^{i(θ₁+θ₂)} = e^{iθ₁}·e^{iθ₂}（复指数加法）
--        ⟹ 相位场的「形状叠加」在复平面上 = 乘法（振动本体的合成律）
--   PF2  ★ 线性叠加封闭：满足 d'Alembert 行波分解 f = g(x) + h(−x) 的波形
--        之和仍是同族（MS3 波动方程的线性性，写成谓词不用导数）
--   PF3  形状恒等式：sech² x = 1 − tanh² x（形状函数的代数根基）
--   PF4  sech 偶函数：sech(−x) = sech x（形状对称性；相位场振动形状无方向偏好）
--   PF5  tanh 奇函数：tanh(−x) = −tanh x（形状的反对称分量）
--
--   ⟹ 接口结论（PF1+PF3–PF5）：相位场的振动形状 = 偶函数×复相位，
--     叠加按乘法合成 —— 这正是「波形状当标尺」需要的最小代数接口。
--       · 偶形状 ⟹ 峰对称（孤子形状族）
--       · 复相位可加 ⟹ 两个振动合成 = 相位相乘（与 VBS 闭包因子同一代数结构）
--
--   —— 本轮没有做的事 ——
--   · 没有把 KdV 立为空间场的动力学（需要新公设，未做）
--   · 没有从形状推导出 N = {3,6,7}（数值层 KV5 给的是**否定**结果）
--   · 没有碰连续导数/积分（形状谱在数值层）

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Basic

namespace ProjectionPhysics.PhaseField

open Complex

-- PF1 相位可加：e^{i(θ₁+θ₂)} = e^{iθ₁}·e^{iθ₂}
theorem phase_additivity (θ₁ θ₂ : ℝ) :
    Complex.exp (I * (θ₁ + θ₂)) = Complex.exp (I * θ₁) * Complex.exp (I * θ₂) := by
  rw [mul_add]
  exact Complex.exp_add (I * θ₁) (I * θ₂)

-- PF2 线性叠加封闭（行波分解族）：
--     f = g(x) + h(−x) 形式的波形，两个之和仍是同族（波动方程线性性，谓词版）
def WaveSoln (f : ℝ → ℝ) : Prop :=
  ∃ g h : ℝ → ℝ, ∀ x : ℝ, f x = g x + h (-x)

theorem wave_solution_add {f g : ℝ → ℝ} (hf : WaveSoln f) (hg : WaveSoln g) :
    WaveSoln (fun x => f x + g x) := by
  rcases hf with ⟨gf, hf', hf_eq⟩
  rcases hg with ⟨gg, hg', hg_eq⟩
  refine ⟨fun x => gf x + gg x, fun x => hf' x + hg' x, ?_⟩
  intro x
  change f x + g x = (gf x + gg x) + (hf' (-x) + hg' (-x))
  rw [hf_eq, hg_eq]
  ring

-- PF3 形状恒等式（sech² 形式的代数内容）：(1/cosh x)² = 1 − tanh² x
--   （KdV 孤子形状 = (c/2)·sech²(kx)；本引理是它在 ℝ 上的代数根基）
theorem sech_sq_eq_one_sub_tanh_sq (x : ℝ) :
    (1 / Real.cosh x) ^ 2 = 1 - (Real.tanh x) ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [div_pow, div_pow]
  have h := Real.cosh_sq_sub_sinh_sq x
  -- cosh²x − sinh²x = 1 ⟹ 1/cosh² = 1 − (sinh/cosh)²
  field_simp [Real.cosh_pos]
  nlinarith

-- PF4 形状偶性：1/cosh(−x) = 1/cosh x（形状无方向偏好）
theorem sech_neg (x : ℝ) : (1 / Real.cosh (-x)) = (1 / Real.cosh x) := by
  rw [Real.cosh_neg]

-- PF5 形状奇分量：tanh(−x) = −tanh x
theorem tanh_neg (x : ℝ) : Real.tanh (-x) = -Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  rw [Real.sinh_neg, Real.cosh_neg]
  ring

end ProjectionPhysics.PhaseField
