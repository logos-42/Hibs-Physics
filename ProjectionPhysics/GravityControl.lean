-- ProjectionPhysics — GravityControl：控制引力场的代数系统（GCA0–GCA7）
--
-- leo（2026-09-17）的问题链：
--   ① "如果有布尔代数，我们能不能根据现在推导出的物理学，设计一种控制引力场的
--      代数系统？" —— 答案：能，但真正的对象不是布尔代数。
--   ② "需要 AI 做的是怎么定义基本逻辑——根据数学的什么量化属性来定义计算。"
--      —— 本模块的回答：**基元是二次型（起伏能量），不是真值。**
--
-- ── 逻辑基元的选取（这是全部内容） ──────────────────────────────────
--   引力在这个框架里不是实体，是空间场的泛函：Φ = ½v²（SG11 已证），
--   引力加速度 = −∇Φ。所以"控制引力" ≡ "控制流动的梯度结构"。
--   基元量必须同时满足四件事，仓库里只有**起伏能量**同时满足：
--     (1) 可观测量：Σ_{i∈A}(v_i − v̄_A)²（一个标量，有限次测量可定）
--     (2) 幂等可判定：抹平两次 = 抹平一次（GCA1）⟹ 可作开关，不是能量泵
--     (3) 二值退化：Q_A = 0 ⟺ A 内常值 ⟺ A 内 ∇Φ = 0 ⟺ **引力关闭**（GCA2）
--     (4) 代价共轭：抹平成本 ∝ 被拿走的起伏²（AMC3 的 κg²/2）——即基元量
--         本身就是代价（GCA7）。布尔代数的真值没有权重，这里有。
--
-- ── 从"量化属性"到"计算"的推导链 ────────────────────────────────────
--   二次型 Q_A（GCA2）
--     → 极化恒等式 ⟨u,v⟩_A = ½(Q_A(u+v) − Q_A(u) − Q_A(v))（GCA3）
--     → 内积 ⟹ 正交（两个控制互不干扰 = 内积为 0）（GCA4）
--     → 正交投影族 = 逻辑（P_A, I−P_A 构成互补投影对，GCA5，复用 PA2）
--     → 格运算：∧ = 复合、∨ = 并（可交换时）、¬ = 正交补（**不是**集合补）
--     → **布尔代数 = 全部投影可交换的子格**（GCA6）
--
-- ── 布尔性从哪来、又从哪里坏（GCA6 是核心结论，本轮被数值检查修正过一次） ──
--   能借助布尔代数做化简、综合、验证 ⟺ 控制区域族是**层状**的（laminar：
--   两两不交，或一个包含另一个）。不交与嵌套都给出可交换算子（GCA6a/GCA6b）；
--   只要两个区域**部分重叠**，顺序就进入语义：先抹 A 再抹 B ≠ 先抹 B 再抹 A，
--   最终引力分布不同（GCA6c 有限维见证，数值 N6 扫描一般情形）。
--   物理读法：两个交叠的反引力场，施加次序改变结果 ⟹ 不可交换 ⟹ 分配律失效
--   ⟹ 非布尔（正交模格，即量子逻辑的那种格）。
--   （修正记录：曾以为"嵌套 ⟹ 不可交换"，数值一跑就推翻——嵌套时小区控制被大区
--     控制吸收，反而最安全。设计规则因此是"区域要么不交、要么嵌套"。）
--
-- ── 与仓库已有"锁定定理"的重新解释（诚实标注：解释层，非新定理） ──────
--   FC5（S* 与 τ_E 必须同比例放大）、FC10（Θ = B²/m_eff 是唯一不变量）、
--   TM2（μ≠1 必有正质量）这些分散的"不能独立调"结论，是同一个代数事实的
--   多个指纹：**相应的控制通道不可交换**。锁定 = 交换子不为零。把它们从
--   "一条条经验禁忌"提升成"控制代数里的一条结构定理"是这个视角的收获。
--
-- ── 诚实边界 ───────────────────────────────────────────────────────
--   本模块全部定理是代数恒等 + 序关系 + 有限维见证（真但平凡）；
--   "引力 = 流动非均匀 ⟹ 抹平 = 引力关闭"是解释层（与 GR 数值不可区分）；
--   本模块给的是**控制语言的语法**，不是控制器的物理实现——μ 的主动产生
--   （第二输入缺口）未变；无新物理预言。

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import ProjectionPhysics.Archive.ProjectionAlgebra
import ProjectionPhysics.Explorations.SpaceField3D

set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators
namespace ProjectionPhysics.GravityControl
open ProjectionPhysics (IsProjection ComplementaryProjection)

variable {ι : Type} [DecidableEq ι]

/-! ### 0. 场、区域、控制操作 -/

/-- 区域 A 上的平均流动（零阶矩）。这是抹平操作的**目标值**：
    把 A 内的流动替换成这个平均值 = 抹掉 A 内的梯度、保留 A 的总流率。 -/
def regionMean (A : Finset ι) (v : ι → ℝ) : ℝ :=
  A.sum v / (A.card : ℝ)

/-- ★ 控制操作 P_A（抹平算子）：A 内流动替换为区域平均，A 外逐点不动。
    物理：抹平流动梯度（引力来源），不改变区域外的场，也不改变区域的总流率。 -/
def flatten (A : Finset ι) (v : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ A then regionMean A v else v i

/-- 起伏 = 被控制"拿走"的那部分：Q_A v = v − P_A v（A 内为 v − 均值，A 外为 0）。
    物理：起伏正是引力的来源，也是抹平代价的来源（GCA7）。 -/
def fluctuation (A : Finset ι) (v : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ A then v i - regionMean A v else 0

/-- ★★ 判定泛函（逻辑基元）：起伏能量 Q_A(v) = Σ_{i∈A} (v_i − v̄_A)²。
    这是"逻辑值"的载体——命题 p_A(v) := "A 内引力关闭" ⟺ Q_A(v) = 0。
    与非负性（GCA2a）、唯一零点判据（GCA2b）、代价共轭（GCA7）一起，
    使它满足一个逻辑基元所需的全部条件（见文件头 (1)–(4)）。 -/
def fluctuationEnergy (A : Finset ι) (v : ι → ℝ) : ℝ :=
  A.sum (fun i => (v i - regionMean A v) ^ 2)

/-- 区域 A 上带均值扣除的内积（由 Q_A 经极化恒等式给出，GCA3）。
    正交 = 两个控制互不干扰（GCA4）。 -/
def regionInner (A : Finset ι) (u v : ι → ℝ) : ℝ :=
  A.sum (fun i => (u i - regionMean A u) * (v i - regionMean A v))

/-- 两个控制算子的交换性：∀v, P(Q v) = Q(P v)。
    可交换 ⟹ 两个控制可以独立设定（布尔子代数的入口，GCA6）。 -/
def commutes (P Q : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ∀ v : ι → ℝ, P (Q v) = Q (P v)

/-! ### GCA1. 抹平是幂等的：控制是"设定"，不是"累计" -/

/-- 单点展开（属于 A）。 -/
lemma flatten_apply_mem {A : Finset ι} {v : ι → ℝ} {i : ι} (h : i ∈ A) :
    flatten A v i = regionMean A v := if_pos h

/-- 单点展开（不属于 A）。 -/
lemma flatten_apply_not_mem {A : Finset ι} {v : ι → ℝ} {i : ι} (h : i ∉ A) :
    flatten A v i = v i := if_neg h

/-- 区域非空 ⟹ 基数（作为实数）非零。 -/
lemma card_cast_ne_zero {A : Finset ι} (hA : A.Nonempty) : (A.card : ℝ) ≠ 0 := by
  have hpos : 0 < A.card := Finset.card_pos.mpr hA
  exact_mod_cast (ne_of_gt hpos)

/-- 均值对区域上逐点相等的场一致。 -/
lemma regionMean_congr {A : Finset ι} {u w : ι → ℝ} (h : ∀ j ∈ A, u j = w j) :
    regionMean A u = regionMean A w := by
  unfold regionMean
  rw [Finset.sum_congr rfl h]

/-- 区域上恒等于 c 的场，其区域均值 = c。 -/
lemma regionMean_eq_of_const {B : Finset ι} (hB : B.Nonempty) {u : ι → ℝ} {c : ℝ}
    (hu : ∀ i ∈ B, u i = c) : regionMean B u = c := by
  unfold regionMean
  rw [Finset.sum_congr rfl hu, Finset.sum_const, nsmul_eq_mul]
  field_simp [card_cast_ne_zero hB]

/-- ★ GCA1（幂等）：P_A(P_A v) = P_A v——做一次和做两次结果相同。
    物理：控制是状态设定（开关），不是能量累加。这是投影代数 PA1（P²=P）
    的物理读法，也是"控制程序可以像逻辑式一样化简"的前提。 -/
theorem flatten_idempotent (A : Finset ι) (hA : A.Nonempty) (v : ι → ℝ) :
    flatten A (flatten A v) = flatten A v := by
  funext i
  by_cases hi : i ∈ A
  · rw [flatten_apply_mem hi, flatten_apply_mem hi]
    exact regionMean_eq_of_const hA (fun j hj => flatten_apply_mem hj)
  · rw [flatten_apply_not_mem hi, flatten_apply_not_mem hi]

/-- ★ GCA1b（守恒）：被拿走的起伏在区域 A 上求和为零
    Σ_{i∈A}(v_i − v̄_A) = 0——**抹平不改变区域总流率**，只抹掉起伏。
    物理：控制是保守重排，不是注入/抽取流量（与 AMC6 "闭合回绕和=0" 同调）。 -/
theorem fluctuation_sum_zero (A : Finset ι) (v : ι → ℝ) :
    A.sum (fun i => v i - regionMean A v) = 0 := by
  unfold regionMean
  by_cases hcard : A.card = 0
  · rw [Finset.card_eq_zero.mp hcard]
    simp
  · have hcardR : (A.card : ℝ) ≠ 0 := by exact_mod_cast hcard
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcardR]
    ring

/-- 抹平算子的线性：P_A(u+v) = P_A u + P_A v（控制叠加在代数上闭合）。 -/
lemma flatten_add (A : Finset ι) (u v : ι → ℝ) :
    flatten A (u + v) = flatten A u + flatten A v := by
  have hmean : regionMean A (u + v) = regionMean A u + regionMean A v := by
    change regionMean A (fun i => u i + v i) = regionMean A u + regionMean A v
    unfold regionMean
    rw [Finset.sum_add_distrib, add_div]
  funext i
  by_cases hi : i ∈ A <;> simp [flatten, hmean, hi, Pi.add_apply]

/-- 抹平算子的线性：P_A(u−v) = P_A u − P_A v。 -/
lemma flatten_sub (A : Finset ι) (u v : ι → ℝ) :
    flatten A (u - v) = flatten A u - flatten A v := by
  have hmean : regionMean A (u - v) = regionMean A u - regionMean A v := by
    change regionMean A (fun i => u i - v i) = regionMean A u - regionMean A v
    unfold regionMean
    rw [Finset.sum_sub_distrib, sub_div]
  funext i
  by_cases hi : i ∈ A <;> simp [flatten, hmean, hi, Pi.sub_apply]

/-! ### GCA2. 判定泛函：引力关闭 ⟺ 起伏能量为零 -/

/-- ★ GCA2a（非负）：Q_A(v) ≥ 0——平方和。逻辑值不会"负"。 -/
theorem fluctuationEnergy_nonneg (A : Finset ι) (v : ι → ℝ) :
    0 ≤ fluctuationEnergy A v := by
  unfold fluctuationEnergy
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- ★★ GCA2b（判定）：Q_A(v) = 0 ⟺ A 内流动处处等于区域平均（常值）
    ⟺ A 内 ∇v = 0 ⟹ A 内 ∇Φ = 0 ⟺ **A 内引力关闭**。
    这就是"逻辑 1/0"的物理判据：命题为真 ⟺ 基元量为零。 -/
theorem fluctuationEnergy_eq_zero_iff (A : Finset ι) (v : ι → ℝ) :
    fluctuationEnergy A v = 0 ↔ ∀ i ∈ A, v i = regionMean A v := by
  constructor
  · intro h i hi
    have hnonneg : ∀ j ∈ A, 0 ≤ (v j - regionMean A v) ^ 2 :=
      fun j _ => sq_nonneg _
    have hzero : (v i - regionMean A v) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h i hi
    have hroot : v i - regionMean A v = 0 := sq_eq_zero_iff.mp hzero
    linarith
  · intro h
    unfold fluctuationEnergy
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i hi]
    ring

/-- ★★ GCA2c（控制达成目标）：抹平之后起伏能量归零——
    P_A 一次施加就把 A 内的引力（梯度）关掉。 -/
theorem flatten_kills_energy (A : Finset ι) (hA : A.Nonempty) (v : ι → ℝ) :
    fluctuationEnergy A (flatten A v) = 0 := by
  rw [fluctuationEnergy_eq_zero_iff]
  intro i hi
  rw [flatten_apply_mem hi]
  exact (regionMean_eq_of_const hA (fun j hj => flatten_apply_mem hj)).symm

/-- ★ GCA2d（抹平 ⟹ ∇Φ = 0：与主线引力的接缝）。
    Φ = ½v²（SG11），区域的流动常值 ⟹ Φ 的离散梯度为零 ⟹ 引力加速度为零。
    把控制代数挂到 SpaceGravity/Spacefield3D 的引力定义上。 -/
theorem flat_flow_zero_potential_gradient (v : ℤ → ℝ) (c : ℝ)
    (h : ∀ i : ℤ, v i = c) (i : ℤ) :
    SpaceField3D.Dx (fun _ x _ _ => (v x) ^ 2 / 2) 0 i 0 0 = 0 := by
  unfold SpaceField3D.Dx
  simp [h]

/-! ### GCA3. 极化恒等式：从二次型（量化属性）升到内积（结构性计算） -/

/-- ★ GCA3（极化）：Q_A(u+v) = Q_A(u) + Q_A(v) + 2⟨u,v⟩_A。
    这是"根据什么量化属性定义计算"的数学枢纽：一个非负二次型（能量）经极化
    给出内积，内积给出正交，正交给出投影，投影族给出逻辑运算。 -/
theorem polarization (A : Finset ι) (u v : ι → ℝ) :
    fluctuationEnergy A (u + v) =
      fluctuationEnergy A u + fluctuationEnergy A v + 2 * regionInner A u v := by
  have hmean : regionMean A (u + v) = regionMean A u + regionMean A v := by
    change regionMean A (fun i => u i + v i) = regionMean A u + regionMean A v
    unfold regionMean
    rw [Finset.sum_add_distrib, add_div]
  unfold fluctuationEnergy regionInner
  rw [hmean]
  have hterm : ∀ i, ((u + v) i - (regionMean A u + regionMean A v)) ^ 2 =
      (u i - regionMean A u) ^ 2 + (v i - regionMean A v) ^ 2 +
        2 * ((u i - regionMean A u) * (v i - regionMean A v)) := by
    intro i
    simp only [Pi.add_apply]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Q_A(v) = ⟨v,v⟩_A——二次型是内积的对角线（自内积非负）。 -/
theorem energy_eq_inner_self (A : Finset ι) (v : ι → ℝ) :
    fluctuationEnergy A v = regionInner A v v := by
  unfold fluctuationEnergy regionInner
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ### GCA4. 正交分解：控制把场分成"可抹的起伏"与"保流的常值" -/

/-- ★ GCA4（正交）：起伏分量与常值分量内积为零——
    ⟨v − P_A v, c⟩_A = 0。这正是"抹平算子是**正交**投影"的内容，
    也是补元 = 正交补（而非集合补）的来源（GCA5）。 -/
theorem fluctuation_orthogonal_constant (A : Finset ι) (v : ι → ℝ) (c : ℝ) :
    regionInner A v (fun _ => c) = 0 := by
  unfold regionInner
  calc A.sum (fun i => (v i - regionMean A v) * ((fun _ : ι => c) i - regionMean A (fun _ => c)))
      = A.sum (fun i => (v i - regionMean A v) * 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [regionMean_eq_of_const ⟨i, hi⟩ (fun j hj => rfl)]
        simp
    _ = 0 := by simp

/-! ### GCA5. 互补投影对：补元 = 正交补（"不做这个控制" ≠ "做相反的控制"） -/

/-- 抹平已经平坦的场 ⟹ 零（正交性内核）：P_A(I − P_A) = 0。 -/
lemma flatten_sub_eq_zero (A : Finset ι) (hA : A.Nonempty) (v : ι → ℝ) :
    flatten A (v - flatten A v) = 0 := by
  rw [flatten_sub, flatten_idempotent A hA]
  exact sub_self _

/-- ★ GCA5：(P_A, I − P_A) 是互补投影对（幂等 + 正交 + 完备）——
    直接复用投影代数 PA2 的 `ComplementaryProjection` 结构。
    物理读法：一个控制的补元是**同一个区域内被保留的部分**（正交补），
    不是"在区域外做相反的控制"。所以"取消一个抹平操作"≠"制造反向引力"。 -/
def flattenComplementary (A : Finset ι) (hA : A.Nonempty) :
    ComplementaryProjection (ι → ℝ) where
  P := flatten A
  Q := fun v => v - flatten A v
  idemP := fun v => flatten_idempotent A hA v
  idemQ := by
    intro v
    have hzero : flatten A (v - flatten A v) = 0 := by
      rw [flatten_sub, flatten_idempotent A hA]
      exact sub_self _
    have : v - flatten A v - flatten A (v - flatten A v) = v - flatten A v - 0 := by
      rw [hzero]
    rw [this, sub_zero]
  ortho := by
    intro v
    constructor
    · exact flatten_sub_eq_zero A hA v
    · have hzero : flatten A v - flatten A (flatten A v) = 0 := by
        rw [flatten_idempotent A hA]
        exact sub_self _
      exact hzero
  complete := by
    intro v
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

/-- 抹平算子是投影（PA1 的 `IsProjection` 结构，物理实例）。 -/
theorem flatten_isProjection (A : Finset ι) (hA : A.Nonempty) :
    IsProjection (flatten A) :=
  fun v => flatten_idempotent A hA v

/-! ### GCA6. 布尔性的边界：可交换 ⟺ 层状区域族（不交 或 嵌套）

**修正记录（本轮自查）**：最初写下的是"真包含 ⟹ 不可交换"，数值检查（N6 扫描）
立刻把它推翻——嵌套的两个抹平算子**是**可交换的（小区控制被大区控制吸收）。
正确刻画是：**不交 或 嵌套（层状族，laminar）⟹ 可交换**；**部分重叠 ⟹ 不可交换**。
这条修正同时改掉了本模块的一处伪定理与 wiki 的对应表述。 -/

/-- ★ 守恒的局部化：B ⊆ A 时，B 上的抹平不改变 A 上的总和（Σ_A P_B v = Σ_A v）。
    理由：抹平只把 B 内的值换成它们自己的均值，而均值保持总和（GCA1b）。 -/
lemma sum_flatten_of_subset {A B : Finset ι} (h : B ⊆ A) (v : ι → ℝ) :
    A.sum (flatten B v) = A.sum v := by
  have hsplit : A.sum (flatten B v) =
      (A \ B).sum (flatten B v) + B.sum (flatten B v) := (Finset.sum_sdiff h).symm
  have hsplitv : A.sum v = (A \ B).sum v + B.sum v := (Finset.sum_sdiff h).symm
  have hout : (A \ B).sum (flatten B v) = (A \ B).sum v := by
    apply Finset.sum_congr rfl
    intro i hi
    exact flatten_apply_not_mem (Finset.mem_sdiff.mp hi).2
  have hB : B.sum (flatten B v) = B.sum v := by
    have hconst : B.sum (flatten B v) = B.sum (fun _ => regionMean B v) :=
      Finset.sum_congr rfl (fun i hi => flatten_apply_mem hi)
    rw [hconst, Finset.sum_const, nsmul_eq_mul]
    have hzero := fluctuation_sum_zero B v
    have hexp : B.sum (fun i => v i - regionMean B v) =
        B.sum v - (B.card : ℝ) * regionMean B v := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [hexp] at hzero
    linarith
  rw [hsplit, hsplitv, hout, hB]

/-- B ⊆ A 时，P_B 不改变 A 上的均值。 -/
lemma regionMean_flatten_of_subset {A B : Finset ι} (h : B ⊆ A) (v : ι → ℝ) :
    regionMean A (flatten B v) = regionMean A v := by
  unfold regionMean
  rw [sum_flatten_of_subset h v]

/-- ★★ GCA6a（布尔那一半·不交）：控制区域不交 ⟹ 可交换 ⟹ 生成布尔子代数。
    A ∩ B = ∅ 时 P_A、P_B 各自只动自己区域内的样本，互不干涉——
    两个控制可以独立设定、任意次序执行，控制程序可以像集合/布尔式一样化简。 -/
theorem flatten_commute_of_disjoint (A B : Finset ι) (h : Disjoint A B) :
    commutes (flatten A) (flatten B) := by
  intro v
  have hB_A : ∀ j ∈ A, flatten B v j = v j := by
    intro j hj
    exact flatten_apply_not_mem (fun hjb => (Finset.disjoint_left.mp h) hj hjb)
  have hA_B : ∀ j ∈ B, flatten A v j = v j := by
    intro j hj
    exact flatten_apply_not_mem (fun hja => (Finset.disjoint_left.mp h) hja hj)
  funext i
  by_cases hiA : i ∈ A
  · have hiB : i ∉ B := fun hb => (Finset.disjoint_left.mp h) hiA hb
    have h1 : flatten A (flatten B v) i = regionMean A v := by
      rw [flatten_apply_mem hiA, regionMean_congr hB_A]
    have h2 : flatten B (flatten A v) i = regionMean A v := by
      rw [flatten_apply_not_mem hiB, flatten_apply_mem hiA]
    rw [h1, h2]
  · by_cases hiB : i ∈ B
    · have h1 : flatten A (flatten B v) i = regionMean B v := by
        rw [flatten_apply_not_mem hiA, flatten_apply_mem hiB]
      have h2 : flatten B (flatten A v) i = regionMean B v := by
        rw [flatten_apply_mem hiB, regionMean_congr hA_B]
      rw [h1, h2]
    · have h1 : flatten A (flatten B v) i = v i := by
        rw [flatten_apply_not_mem hiA, flatten_apply_not_mem hiB]
      have h2 : flatten B (flatten A v) i = v i := by
        rw [flatten_apply_not_mem hiB, flatten_apply_not_mem hiA]
      rw [h1, h2]

/-- ★★ GCA6b（布尔那一半·嵌套）：B ⊆ A ⟹ P_A ∘ P_B = P_B ∘ P_A = P_A。
    小区控制被大区控制**吸收**——大区域已经抹平，小区再抹是同一件事。
    （这就是本轮修正掉的错误：嵌套**不是**非交换的来源。） -/
theorem flatten_commute_of_subset {A B : Finset ι} (h : B ⊆ A) :
    commutes (flatten A) (flatten B) := by
  intro v
  funext i
  by_cases hiA : i ∈ A
  · by_cases hiB : i ∈ B
    · have h1 : flatten A (flatten B v) i = regionMean A v := by
        rw [flatten_apply_mem hiA, regionMean_flatten_of_subset h v]
      have h2 : flatten B (flatten A v) i = regionMean A v := by
        rw [flatten_apply_mem hiB]
        exact regionMean_eq_of_const ⟨i, hiB⟩ (fun j hj => flatten_apply_mem (h hj))
      rw [h1, h2]
    · have h1 : flatten A (flatten B v) i = regionMean A v := by
        rw [flatten_apply_mem hiA, regionMean_flatten_of_subset h v]
      have h2 : flatten B (flatten A v) i = regionMean A v := by
        rw [flatten_apply_not_mem hiB, flatten_apply_mem hiA]
      rw [h1, h2]
  · have hiB : i ∉ B := fun hb => hiA (h hb)
    have h1 : flatten A (flatten B v) i = v i := by
      rw [flatten_apply_not_mem hiA, flatten_apply_not_mem hiB]
    have h2 : flatten B (flatten A v) i = v i := by
      rw [flatten_apply_not_mem hiB, flatten_apply_not_mem hiA]
    rw [h1, h2]

/-- GCA6b 的算子形式：嵌套时的复合 = 大区域的控制（吸收律）。 -/
theorem flatten_absorb_of_subset {A B : Finset ι} (h : B ⊆ A) (v : ι → ℝ) :
    flatten A (flatten B v) = flatten A v := by
  funext i
  by_cases hiA : i ∈ A
  · rw [flatten_apply_mem hiA, regionMean_flatten_of_subset h v, flatten_apply_mem hiA]
  · have hiB : i ∉ B := fun hb => hiA (h hb)
    rw [flatten_apply_not_mem hiA, flatten_apply_not_mem hiA, flatten_apply_not_mem hiB]

/-- 同一个控制与自己可交换（平凡情形）。 -/
theorem flatten_commute_self (A : Finset ι) :
    commutes (flatten A) (flatten A) :=
  fun _ => rfl

/-- ★★ GCA6c（非布尔见证：部分重叠）：A = {0,1}、B = {1,2}（Fin 3）两个区域
    部分重叠——既不交又互不包含。此时 P_A 与 P_B **不可交换**：
    先抹 A 再抹 B 得 [0.5, 0.5, 0]，先抹 B 再抹 A 得 [0.5, 0.25, 0.25]
    （i=1 处 1/2 vs 1/4）。
    物理读法：两个交叠的反引力场，施加次序改变最终引力分布——可测的顺序效应。
    （一般的"部分重叠 ⟹ 不可交换"由数值扫描 N6 覆盖；此处给有限维见证。） -/
theorem flatten_not_commute_overlap :
    ¬ commutes (flatten ({0, 1} : Finset (Fin 3))) (flatten ({1, 2} : Finset (Fin 3))) := by
  intro h
  have h1 := congrFun (h ![1, 0, 0]) 1
  have hL : flatten ({0, 1} : Finset (Fin 3))
      (flatten ({1, 2} : Finset (Fin 3)) ![1, 0, 0]) 1 = 1 / 2 := by
    simp (config := { decide := true }) [flatten, regionMean]
  have hR : flatten ({1, 2} : Finset (Fin 3))
      (flatten ({0, 1} : Finset (Fin 3)) ![1, 0, 0]) 1 = 1 / 4 := by
    simp (config := { decide := true }) [flatten, regionMean]
    norm_num
  rw [hL, hR] at h1
  have hbad : (1 : ℝ) / 2 ≠ 1 / 4 := by norm_num
  exact hbad h1

/-! ### GCA7. 代价 = 二次型：基元量同时是"真值"和"价格" -/

/-- 抹平代价（AMC3 的 κg²/2 形式）：把 A 内的起伏拿掉要付的功 ∝ 起伏能量。
    ⟹ 逻辑基元自带权重（布尔真值没有）——这是"带代价的逻辑"的来源。 -/
def flattenCost (A : Finset ι) (v : ι → ℝ) (κ : ℝ) : ℝ :=
  κ * fluctuationEnergy A v / 2

/-- ★ GCA7a（代价非负）：κ > 0 ⟹ 代价 ≥ 0。 -/
theorem flattenCost_nonneg (A : Finset ι) (v : ι → ℝ) (κ : ℝ) (hκ : 0 < κ) :
    0 ≤ flattenCost A v κ := by
  unfold flattenCost
  apply div_nonneg
  · exact mul_nonneg (le_of_lt hκ) (fluctuationEnergy_nonneg A v)
  · norm_num

/-- ★★ GCA7b（零成本判据 = 控制必要性判据）：代价为零 ⟺ A 内已经平坦
    ⟺ 这个控制**不需要做**。与 AMC3b（均匀区零成本）、AMC4（无源区零维持
    成本）接轨：抹平是"把已有起伏归零"，没有起伏的地区无需付出。 -/
theorem flattenCost_eq_zero_iff (A : Finset ι) (v : ι → ℝ) (κ : ℝ) (hκ : κ ≠ 0) :
    flattenCost A v κ = 0 ↔ ∀ i ∈ A, v i = regionMean A v := by
  unfold flattenCost
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · rcases mul_eq_zero.mp h with hk0 | hE
      · exact absurd hk0 hκ
      · exact (fluctuationEnergy_eq_zero_iff A v).mp hE
    · exact absurd h two_ne_zero
  · intro h
    left
    exact mul_eq_zero.mpr (Or.inr ((fluctuationEnergy_eq_zero_iff A v).mpr h))

/-! ### GCA8. 诚实边界 -/

/-- 本模块的边界：全部定理 = 代数恒等 + 序关系 + 有限维不可交换见证（真但平凡）；
    "抹平 = 引力关闭" 是解释层（与弱场 GR 数值不可区分）；逻辑基元 = 起伏能量
    （二次型）是**定义选择**，其正当性由四条判据（可观测量/幂等/二值退化/代价共轭）
    支撑，不是从公理推出的；控制器的物理实现（μ 主动产生）= 第二输入缺口未变；
    无新物理预言。 -/
def GRAVITY_CONTROL_SCOPE : String :=
  "控制代数骨架: 基元=起伏能量二次型(GCA2) + 极化→内积(GCA3) + 正交分解(GCA4) + 互补投影对(GCA5,复用PA2) + 布尔边界=层状族(GCA6a 不交/GCA6b 嵌套吸收) vs 非交换见证(GCA6c 部分重叠) + 代价二次型(GCA7); μ主动产生=第二输入缺口; 无新物理预言"

end ProjectionPhysics.GravityControl
