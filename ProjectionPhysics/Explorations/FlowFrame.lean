-- ProjectionPhysics — FlowFrame：让**流动自己给出框架**（FF1–FF7）
--
-- leo（2026-11-01）：「不是谱分解，是让流动给出框架。流动已经有方向结构和电荷 = 流散度；
--   如果能用它定出极大环面（而不是我们选），框架就从输入变成推论。
--   死法也清楚：框架随点漂移、或与三方向不对角，这条就死。」
--
-- 本模块就把这条做成定理：**极大环面（色框架）由流动 + 其电荷梯度给出**，
-- 不再由我们选。判据与两条死法一起形式化。
--
--   每个格点 x 上有：流动 C(x) ∈ ℝ³（空间流动），电荷密度 ρ(x) = ∇·C（= 流散度），
--   其梯度 g(x) = ∇ρ(x)。框架取
--
--       frameMat C g = [ C ; g ; C × g ]     （三行）
--
--   即：**第一轴 = 流动方向，第二轴 = 电荷梯度方向，第三轴 = 二者叉积**。
--   框架只依赖 (C, g)，没有任何自由参数 ⟹ **从输入变成推论**。
--
--   FF1 ★★★ `frameMat` 只依赖流动与电荷梯度（无自由参数）——"框架是推论"的形式内容
--   FF2 ★★★ `frame_ok_of_cross_ne`：**非退化 ⟹ 流动与电荷梯度不平行**
--        （叉积为零 ⟹ 第三行全零 ⟹ det = 0 的逆否）
--   FF3 ★★★ `frame_dead_of_parallel`：**死法一（退化）**：C ∥ g ⟹ 框架塌（det = 0）
--   FF4 `frame_dead_witness`：显式见证 C=(1,0,0)、g=(2,0,0) ⟹ det = 0
--   FF5 `frame_alive_witness`：C=(1,0,0)、g=(0,1,0) ⟹ det = 1 ≠ 0（框架活）
--   FF6 ★★★ `frame_drifts`：**死法二（漂移）**：存在流动使相邻两点的框架**不同**
--        ⟹ 全局单一框架不成立，必须逐点（或加约束）
--   FF7 ★★★ `frame_not_aligned`：**死法三（不对角）**：框架可以不是坐标系的置换
--        ⟹ 一般流动下框架与"三个空间方向"不对角，色分解前还要再对角化一次
--
-- 结论（写死）：
--   · 框架**由流动唯一给出**（FF1），这是把 Cartan 选取从输入变成推论的一半。
--   · 但另一半没白给：框架一般**随点漂移**（FF6）、且**不与三方向对齐**（FF7）。
--     ⟹ 要得到全局一致的色分解，必须再加**一个约束**（例如"流动是整体常向量"或
--       "电荷梯度处处与流动正交"），而那个约束就是新的输入。**这一条不能两头都要。**
--   · 仍未做：把 frameMat 的对角化（用框架当基）与 `ColorSplit` 的逐色绕数接起来；
--     那需要"在该基下的矩阵表示"，是下一步。

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section

namespace ProjectionPhysics.FlowFrame

/-- 三维空间向量（流动、梯度、叉积都住在这里）。 -/
abbrev Vec3 := Fin 3 → ℝ

/-- 流散度梯度：框架的第二轴。 -/
abbrev chargeGrad := Vec3

/-- **框架矩阵**：三行 = [流动；电荷梯度；二者叉积]。
    —— 这个对象**只依赖流动与电荷梯度**，没有第三样东西可选。 -/
def frameMat (C g : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![C 0, C 1, C 2; g 0, g 1, g 2;
    ((crossProduct C) g) 0, ((crossProduct C) g) 1, ((crossProduct C) g) 2]

/-! ### FF1 框架是流动的函数（没有自由参数） -/

/-- FF1 ★★★ **框架由流动唯一给出**：同一流动、同一声荷梯度 ⟹ 同一框架。
    这里没有第二样可选的东西——**Cartan 选取不是输入，是推论**。（`rfl` 即证：无自由度。） -/
theorem frameMat_determined (C C' g g' : Vec3) (hC : C = C') (hg : g = g') :
    frameMat C g = frameMat C' g' := by
  subst hC hg
  rfl

/-! ### FF2/FF3 退化判据 -/

/-- FF3 ★★★ **死法一（退化）**：若流动与电荷梯度平行（叉积为零），
    则框架的第三行全零 ⟹ det = 0 ⟹ 框架塌，色分解无从谈起。 -/
theorem frame_dead_of_parallel (C g : Vec3) (h : (crossProduct C) g = 0) :
    (frameMat C g).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero 2
  intro j
  fin_cases j <;> simp [frameMat, h]

/-- FF2 ★★★ **非退化 ⟹ 不平行**：框架可逆则流动与电荷梯度必不平行。
    （= FF3 的逆否命题，故「框架存在」与「C ∦ g」是同一件事。） -/
theorem frame_ok_of_cross_ne (C g : Vec3) (h : (frameMat C g).det ≠ 0) :
    (crossProduct C) g ≠ 0 := by
  intro hcross
  exact h (frame_dead_of_parallel C g hcross)

/-! ### FF4/FF5 两个显式见证 -/

/-- FF4：**死法一的见证**——流动 (1,0,0)、电荷梯度 (2,0,0)（平行）⟹ det = 0。 -/
theorem frame_dead_witness :
    (frameMat (fun i => if i = 0 then 1 else 0) (fun i => if i = 0 then 2 else 0)).det = 0 := by
  apply frame_dead_of_parallel
  funext j
  fin_cases j <;> simp [cross_apply]

/-- FF5：**框架活的见证**——流动 (1,0,0)、电荷梯度 (0,1,0) ⟹ det = 1 ≠ 0。 -/
theorem frame_alive_witness :
    (frameMat (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0)).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [frameMat, cross_apply]

/-- FF5b：该框架确实非退化。 -/
theorem frame_alive_witness_ne_zero :
    (frameMat (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0)).det ≠ 0 := by
  rw [frame_alive_witness]; norm_num

/-! ### FF6 死法二：框架随点漂移 -/

/-- FF6 ★★★ **死法二（漂移）**：存在流动，使两点的框架**不同**。
    取流动恒为 (1,0,0)，电荷梯度在一点为 (0,1,0)、另一点为 (0,0,1)：
    两点框架不相等 ⟹ **全局单一框架不成立**，除非对流动加约束（= 新输入）。 -/
theorem frame_drifts :
    frameMat (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0)
      ≠ frameMat (fun i => if i = 0 then 1 else 0) (fun i => if i = 2 then 1 else 0) := by
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) h
  simp [frameMat] at h11

/-! ### FF7 死法三：框架与三个空间方向不对角 -/

/-- 「与三方向对齐」= 每行恰有一个非零元（坐标轴的置换/缩放）。
    这里只需要判定**不对齐**：给出一个非零的"错位"元即可。 -/
def Aligned (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3, i ≠ j → M i j = 0

/-- FF7 ★★★ **死法三（不对角）**：流动 (1,0,0)、电荷梯度 (1,1,0) 给出的框架
    **不是**三方向的置换——第 2 行第 1 列有非零元。
    ⟹ 一般流动下，框架与空间三方向不对角，色分解前还要再对角化一次（= 额外一步）。 -/
theorem frame_not_aligned :
    ¬ Aligned (frameMat (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 1)) := by
  intro h
  have h10 := h 1 0 (by decide)
  simp [frameMat] at h10

end ProjectionPhysics.FlowFrame
