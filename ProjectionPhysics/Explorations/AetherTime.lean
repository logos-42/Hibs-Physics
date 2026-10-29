-- ProjectionPhysics — AetherTime：接上 YM 方程接口 —— 顺序（时间的代数影子）⟺ 非对易
--
-- leo（2026-10-29 续）：「结 ym 方程接口，瞬时是因为时间在人类世界上线性的，
--   在无质量空间，不存在当前的线性时间观。」
--
-- ⚠ 更正（leo 2026-10-29，同日）：「**无质量和平坦无关**，无质量只是没有对周围空间
--   产生扭曲，证伪一下就行，平坦反而是局部特殊情况。」
--   ⟹ 本文件下半部（AT11–AT14）就是这条更正的形式化：
--     · 「无质量」= 无散度（不对周围空间产生扭曲）= **源的属性**；「平坦」= 场为常值
--       = **场的属性**。两者作用在不同对象上，AT9 把二者并置是**类型层面的错**。
--     · **平坦 ⟹ 无散（AT11）** ⟹ 平坦是无质量的特例（局部特殊情形）；
--     · **涡旋：无散但非平坦（AT12）** ⟹ 无质量 ⇏ 平坦，包含是**严格**的（AT14）。
--     · 于是 **AT9 的读法撤回**：顺序盲的来源是**平坦**（AT4），不是无质量；
--       无质量并不破坏时间序（AT13：涡旋场上交换差仍非零）。
--     · 保留的仍然有效部分：AT8 作为纯数学陈述（若**整层**间隔全零则无严格先后）
--       只在「整层没有时钟」时成立——探针自身 dτ=0 **不足以**推出这一点。
--
-- 读法（本模块只把这句话写成命题，不做新公设）：
--   · 时间的**代数影子**是「先 / 后」这个顺序。两个算子作用在同一状态上，
--     若 `T(S v) = S(T v)` 对一切场成立，则先后**不可观测** —— 顺序在这对操作上
--     没有内容（AT1/AT2 把它写成定义 + 否定见证）。
--   · 于是「线性时间」在本框架里不是先验的坐标，而是**非交换性的记录**：
--     有起伏（有质量）⟹ 汇算子不交换（复用 YM3：交换差 = λ²(v_q − v_p)）⟹ 必须
--     外部指定顺序 ⟹ 时间序可观测（AT5）；平坦（无起伏、μ=1、质量已取消）⟹
--     汇算子全等 ⟹ 顺序盲 ⟹ 时间序无内容（AT3/AT4）。
--   · 无质量态不花固有时（SM1：dx = c·dt ⟹ dτ² = 0）。若一层里**所有间隔为 0**，
--     则不存在严格先后（AT8）——「更快 / 瞬时」这类比较的**前提**（正的间隔）
--     在那里不存在。
--
-- 结论的形状（AT9）：平坦 ∧ 无质量 ⟹ 顺序盲 ∧ 无严格时间序。
--   ⟹ 在无质量层，「瞬时」不是「比光速更快」，而是**快慢这个比较没有定义**；
--     要谈「更快」，必须先有质量（有起伏）把时间序生出来。
--
-- 诚实边界（写死，防后续 session 过度声称）：
--   1. 本模块**没有**证明「时间 = 非对易性」。它证明的是两者的**结构同位**：
--      顺序可观测 ⟺ 非交换 ⟺ 有梯度（AT4/AT5/AT6）。把时间「等同于」非交换性的记录
--      是**解释层**（框架读法），不是定理。
--   2. 「无质量 ⟹ 平坦」**没有**证明。框架里有两条独立链：
--      质量=锚定（MC1）与 平坦 ⟹ μ=1 ⟹ m_eff=0（GCA2 + AMC1，仓库已证）。
--      本模块把「平坦」与「无质量（dτ=0）」并置成 AT9 的两个前提，**不主张二者等价**。
--   3. 标准物理里光子没有固有时但有坐标时间；「无质量空间没有线性时间观」是
--      **本框架的读法**（时间单位 = 闭包次数，见 VibrationClosure VBC4/VBC5、
--      Archive/HiddenEventClocks），不是标准 QFT 的结论。
--   4. AT1–AT8 全是初等代数/序关系（真但平凡）；无新可检验预言。
--
-- 死法（写死）：
--   ① 若在**平坦**场（无起伏）上找到两个汇算子不交换，则 AT3/AT4/AT6 死
--      （时间序不需要质量）。
--   ② 若找到**无质量但非平坦**的构型，其中时间序仍可观测，则 AT9 那条读法死
--      （因为「平坦 ⟺ 无质量」没有证，只被并置）。
--   ③ 若「时间 = 非交换性的记录」被当成物理定律使用（而不是解释层），则需补一条
--      把时间从解释提升为定理的推导——本轮没做，登记为缺口。

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.YangMillsSeed
import ProjectionPhysics.SpaceMetric

namespace ProjectionPhysics.AetherTime

open ProjectionPhysics.YangMillsSeed
open SpaceMetric

variable {ι : Type}

/-- 算子：把一个场（格点上的流场）映成另一个场。 -/
def Op (ι : Type*) : Type _ := (ι → ℝ) → (ι → ℝ)

/-- 平坦：全场取同一个值（无起伏 = Q_A = 0 = 引力关闭 = μ=1 的几何形态）。 -/
def Flat (v : ι → ℝ) : Prop := ∃ c, ∀ i, v i = c

/-- 顺序盲（限定在子区域 P 上）：在该区域的场上，T 与 S 的先后不可区分。
    ⟹ 线性时间在这对操作上没有内容（不是「时间不存在」，是「时间序不可观测」）。 -/
def OrderBlindOn {ι : Type} (T S : Op ι) (P : (ι → ℝ) → Prop) : Prop :=
  ∀ v, P v → T (S v) = S (T v)

/-- 顺序可观测：在第 i 个位置上，两种顺序给出不同值（= 有一个刻度能报告先后）。 -/
def OrderVisibleAt (T S : Op ι) (v : ι → ℝ) (i : ι) : Prop :=
  T (S v) i ≠ S (T v) i

-- ---------------------------------------------------------------------------
-- AT1/AT2 顺序盲 ⇔ 没有观察量能报告先后
-- ---------------------------------------------------------------------------

/-- AT1 定义等价：顺序盲 ⟺ 对该区域内一切场，两种顺序给同一条场。 -/
theorem orderBlindOn_iff (T S : Op ι) (P : (ι → ℝ) → Prop) :
    OrderBlindOn T S P ↔ ∀ v, P v → T (S v) = S (T v) := Iff.rfl

/-- AT2 ★ 顺序盲的否定 ⟺ 存在一个场使两种顺序给出**不同的场**
    ⟹ 「顺序（时间）可观测」的机器可检形式。 -/
theorem not_orderBlindOn_iff (T S : Op ι) (P : (ι → ℝ) → Prop) :
    ¬ OrderBlindOn T S P ↔ ∃ v, P v ∧ T (S v) ≠ S (T v) := by
  simp only [OrderBlindOn]
  constructor
  · rintro hv
    -- ¬∀v, P v → ... ⟹ 取见证
    by_contra hcon
    exact hv (fun v hP => by
      by_contra hne
      exact hcon ⟨v, hP, hne⟩)
  · rintro ⟨v, hP, hne⟩ hblind
    exact hne (hblind v hP)

-- ---------------------------------------------------------------------------
-- AT3/AT4 平坦 ⟹ 顺序盲（无质量层没有时间序）
-- ---------------------------------------------------------------------------

/-- AT3 ★ 平坦场在任何单点收缩下仍是同一条常值场（汇无所抹：全值相等）。 -/
theorem flat_stays_flat {p : ι} {lam c : ℝ} {v : ι → ℝ}
    (hv : ∀ i, v i = c) : ∀ i, sinkToPoint p lam v i = c := by
  intro i
  simp only [sinkToPoint, hv i, hv p]
  ring

/-- AT4 ★★ 平坦 ⟹ 顺序盲：常值场上两个不同汇点的复合给出同一条场，
    先后不可区分 ⟹ 该区域里「先 / 后」没有内容。 -/
theorem orderBlind_on_flat {p q : ι} {lam c : ℝ} {v : ι → ℝ} (hv : ∀ i, v i = c) :
    sinkToPoint p lam (sinkToPoint q lam v) = sinkToPoint q lam (sinkToPoint p lam v) := by
  have hP : ∀ i, sinkToPoint p lam (sinkToPoint q lam v) i = c :=
    flat_stays_flat (p := p) (lam := lam) (v := sinkToPoint q lam v)
      (flat_stays_flat (p := q) (lam := lam) (v := v) hv)
  have hQ : ∀ i, sinkToPoint q lam (sinkToPoint p lam v) i = c :=
    flat_stays_flat (p := q) (lam := lam) (v := sinkToPoint p lam v)
      (flat_stays_flat (p := p) (lam := lam) (v := v) hv)
  funext i
  rw [hP i, hQ i]

/-- AT4b 形式版：`OrderBlindOn` 在平坦类上成立。 -/
theorem orderBlindOn_flat (p q : ι) (lam : ℝ) :
    OrderBlindOn (sinkToPoint p lam) (sinkToPoint q lam) (Flat (ι := ι)) := by
  intro v hv
  obtain ⟨c, hc⟩ := hv
  exact orderBlind_on_flat (p := p) (q := q) (lam := lam) hc

-- ---------------------------------------------------------------------------
-- AT5/AT6 有梯度 ⟹ 顺序可观测（接 YM3）
-- ---------------------------------------------------------------------------

/-- AT5 ★★★ 顺序可观测 ⟺ 有梯度：若两汇点的场值不同且 λ ≠ 0，
    则交换差在 p 处 = λ²(v_q − v_p) ≠ 0
    ⟹ 先后**可以被一个刻度报告** ⟹ 时间序在该处有内容。
    证明：直接复用 YM3 的交换差公式。 -/
theorem order_visible_of_gradient {p q : ι} {lam : ℝ} {v : ι → ℝ}
    (hgrad : v q ≠ v p) (hlam : lam ≠ 0) :
    OrderVisibleAt (sinkToPoint p lam) (sinkToPoint q lam) v p := by
  simp only [OrderVisibleAt]
  intro hzero
  have hz : lam ^ 2 * (v q - v p) = 0 := by
    rw [← sinkToPoint_commutator_formula, hzero, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact hlam (sq_eq_zero_iff.mp h)
  · exact hgrad (sub_eq_zero.mp h)

/-- AT6 ★★ 非平坦 ⟺ 存在梯度：不是常值场 ⟹ 存在两点场值不同
    （AT5 的准入前提；`Nonempty` 只用来取一个参考点）。 -/
theorem gradient_of_not_flat [Nonempty ι] {v : ι → ℝ} (h : ¬ Flat v) :
    ∃ i j, v j ≠ v i := by
  by_contra hcon
  apply h
  push Not at hcon
  -- hcon : ∀ i j, v j = v i ⟹ 取任一点的值作为常数
  refine ⟨v (Classical.arbitrary ι), fun i => ?_⟩
  exact (hcon i (Classical.arbitrary ι)).symm

-- ---------------------------------------------------------------------------
-- AT7/AT8 无质量 ⟹ 无固有时 ⟹ 无严格先后
-- ---------------------------------------------------------------------------

/-- AT7 ★★ 无质量态不花固有时：dx = c·dt ⟹ dτ² = 0（复用 SM1）。 -/
theorem massless_interval_zero (c dt dx : ℝ) (hc : c ≠ 0) (h : dx = c * dt) :
    properTimeSq c dt dx = 0 :=
  photon_proper_time_zero c dt dx hc h

/-- AT8 ★★★ 若一层里所有间隔都是 0，则不存在严格先后：
    「更快 / 瞬时」这类比较需要**正的**间隔，那里没有这个前提。
    （证明：任何「严格先后」都要 0 < 0。） -/
theorem no_strict_order_of_zero_intervals {τ : ι → ι → ℝ}
    (h : ∀ x y, τ x y = 0) : ¬ ∃ x y, τ x y < τ y x := by
  rintro ⟨x, y, hxy⟩
  rw [h x y, h y x] at hxy
  exact absurd hxy (lt_irrefl (0 : ℝ))

-- ---------------------------------------------------------------------------
-- AT9 合成：平坦 ∧ 无质量 ⟹ 顺序盲 ∧ 无严格时间序
-- ---------------------------------------------------------------------------

/-- AT9 ★★★ 合成（**读法已更正**）：在平坦（无起伏）且所有间隔为零的区域里，
    ① 汇算子复合先后不可区分，② 不存在严格先后。

    ⚠ 更正（leo 2026-10-29）：这两个前提**不是同一件事**，本定理不再被读作
    「无质量 ⟹ 没有时间序」。有效的部分是 ①（来源 = 平坦，AT4）；
    ② 只在「整层所有间隔全为零」时成立，而**探针自身 dτ=0 不足以**给出这一点
    （无质量的场不必平坦：AT12 给涡旋见证；且涡旋场里顺序照样可观测：AT13）。 -/
theorem flat_massless_no_time {p q : ι} {lam c : ℝ} {v : ι → ℝ} (hv : ∀ i, v i = c)
    {τ : ι → ι → ℝ} (hτ : ∀ x y, τ x y = 0) :
    sinkToPoint p lam (sinkToPoint q lam v) = sinkToPoint q lam (sinkToPoint p lam v) ∧
      ¬ ∃ x y, τ x y < τ y x :=
  ⟨orderBlind_on_flat (p := p) (q := q) (lam := lam) hv,
   no_strict_order_of_zero_intervals hτ⟩

-- ---------------------------------------------------------------------------
-- AT10 对照：有质量侧（时间序被生出来）
-- ---------------------------------------------------------------------------

/-- AT10 ★★★ 对照定理（同一模块里把两侧并排）：
    存在梯度 ⟹ 存在一个位置使先后可分辨 ⟹ 时间序**被生出来**。
    与 AT4 合起来即是：**平坦 ⟺ 顺序盲**、**有梯度 ⟹ 顺序可观测**。 -/
theorem mass_creates_time_order {p q : ι} {lam : ℝ} {v : ι → ℝ}
    (hgrad : v q ≠ v p) (hlam : lam ≠ 0) :
    ∃ i, OrderVisibleAt (sinkToPoint p lam) (sinkToPoint q lam) v i :=
  ⟨p, order_visible_of_gradient (p := p) (q := q) hgrad hlam⟩

-- ---------------------------------------------------------------------------
-- 更正（leo 2026-10-29）：「无质量和平坦无关」—— 证伪 AT9 的并置
--
--   区分两个对象：
--     无质量  = 没有对周围空间产生扭曲 = **源**的属性（无散度：无源无汇）
--     平坦    = 场为常值             = **场**的属性（Q_A = 0）
--   以下四条把二者分开：
--     AT11 平坦 ⟹ 无散（平坦是无质量的特例 = 局部特殊情形）
--     AT12 **涡旋：无散 ∧ 非平坦**（无质量 ⇏ 平坦）—— 见证：v = (0,1,1,0)
--     AT13 涡旋场里顺序照样可观测（无质量**不**破坏时间序）
--     AT14 平坦 ⊊ 无质量（严格包含）
-- ---------------------------------------------------------------------------

/-- 4 点回路上的离散散度：divV v = (v₁ − v₀) + (v₃ − v₂)（源/汇的净流出）。
    「不对周围空间产生扭曲」的离散形式 = divV = 0。 -/
def divV (v : Fin 4 → ℝ) : ℝ := (v 1 - v 0) + (v 3 - v 2)

/-- 同一回路上的离散旋度（反对称组合）：curlV v = (v₂ − v₀) − (v₃ − v₁)。 -/
def curlV (v : Fin 4 → ℝ) : ℝ := (v 2 - v 0) - (v 3 - v 1)

/-- 涡旋见证场：v = (0, 1, 1, 0)。 -/
def vortex : Fin 4 → ℝ := ![0, 1, 1, 0]

/-- AT11 ★ 平坦 ⟹ 无散：常值场不产生源汇 ⟹ 不对周围空间产生扭曲。
    ⟹ **平坦是无质量的特例**（「平坦反而是局部特殊情况」的前一半）。 -/
theorem flat_implies_divFree {c : ℝ} {v : Fin 4 → ℝ} (hv : ∀ i, v i = c) : divV v = 0 := by
  simp only [divV, hv 1, hv 0, hv 3, hv 2]
  ring

/-- AT12 ★★★ 无质量 **不**蕴含平坦：涡旋场无散（无源无汇、不产生扭曲），
    但它不是常值场（有旋，curlV = 2）。
    ⟹ 无质量与平坦**无关**；AT9 把二者并置是类型层面的错。 -/
theorem vortex_massless_not_flat :
    divV vortex = 0 ∧ ¬ Flat vortex ∧ curlV vortex ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [divV, vortex]
  · rintro ⟨c, hc⟩
    have h0 : vortex 0 = c := hc 0
    have h1 : vortex 1 = c := hc 1
    simp [vortex] at h0 h1
    linarith
  · norm_num [curlV, vortex]

/-- AT13 ★★★ 无质量**不**破坏时间序：在涡旋场上取 p = 0、q = 1，
    场值不同（1 ≠ 0）⟹ 交换差 = λ²(v₁ − v₀) ≠ 0 ⟹ 顺序照样可观测。
    ⟹ **顺序（时间的代数影子）的来源是场的梯度，不是源的无质量性**。 -/
theorem vortex_keeps_time_order {lam : ℝ} (hlam : lam ≠ 0) :
    OrderVisibleAt (sinkToPoint (0 : Fin 4) lam) (sinkToPoint (1 : Fin 4) lam) vortex 0 := by
  apply order_visible_of_gradient (p := (0 : Fin 4)) (q := (1 : Fin 4))
  · simp [vortex]
  · exact hlam

/-- AT14 ★★★ 严格包含：平坦 ⊊ 无质量。
    ① 一切常值场都无散（平坦 ⟹ 无质量）；
    ② 存在无散但非平坦的场（涡旋）。
    ⟹ **平坦是无质量的局部特殊情形**，反向不成立。 -/
theorem flat_strict_subset_massless :
    (∀ v : Fin 4 → ℝ, Flat v → divV v = 0) ∧ ∃ v : Fin 4 → ℝ, divV v = 0 ∧ ¬ Flat v := by
  refine ⟨?_, ⟨vortex, vortex_massless_not_flat.1, vortex_massless_not_flat.2.1⟩⟩
  intro v hv
  obtain ⟨c, hc⟩ := hv
  exact flat_implies_divFree hc

end ProjectionPhysics.AetherTime
