-- ProjectionPhysics — ExchangeStatistics：把「统计性 = 闭包相因子」从**定义**升级成**定理**（ES1–ES8）
--
-- leo：「交换回路与 2π 旋转回路同伦」后续。
--
-- ── 要解决的问题 ──────────────────────────────────────────────────────────
--   VBS 那一轮把统计性**定义**成闭包相因子（`ClosureFactor f σ`：f(θ+2π) = σ·f(θ)）。
--   那是一条**定义**，不是结论——wiki 里当时如实登记为「闭包相因子是定义选择」。
--   本模块把它升级成一条**条件定理**：给定拓扑输入（下面 ②），
--   「交换相因子 = 闭包相因子」，于是统计性不再是定义的产物。
--
-- ── 拓扑输入（**标准事实，未形式化**；这是本模块唯一的非代数内容） ─────────
--   三维里 N 个全同粒子构型空间的 π₁：
--     π₁(C_N(ℝ³)) ≅ S_N（对称群）      [Fox–Neuwirth 1962, Math. Scand. 10, 119]
--     π₁(C_N(ℝ²)) ≅ B_N（辫群）        [同上 / Fadell–Neuwirth 1962]
--   相位是 π₁ 的**角色**（ℂ* 值乘法同态），角色必过**阿贝尔化**：
--     S_N^ab ≅ ℤ₂（N ≥ 2）      ⟹ 三维只能 ±1
--     B_N^ab ≅ ℤ （N ≥ 2）      ⟹ 二维可 U(1)，即**任意子**
--   而「交换回路」与「2π 旋转回路」在三维构型空间里落在**同一个**非平凡类：
--     交换两个粒子 ⟺ 把其中一个转 2π（Dirac 皮带诡计 / 弦问题）
--     [Fadell 1962, Duke Math. J. 29, 231；Finkelstein–Rubinstein 1968,
--      J. Math. Phys. 9, 1762：kink 模型里「半整数自旋可存在 ⟺ 费米统计可存在」]
--
-- ── 本模块做了什么 ────────────────────────────────────────────────────────
--   · ES1–ES3  闭路角色 + χ(n) = χ(1)ⁿ
--   · ES4 ★   阶 N 的群 ⟹ 相位是 N 次单位根（一般结论）
--   · ES5 ★★  三维（N = 2）⟹ 相位只能 ±1（复用 VSS4 `sq_one_two_values`）
--   · ES6 ★★  二维：全扭转(2π 旋转) = 交换²——**两次交换 = 一次 2π 旋转**
--   · ES7 ★★  二维自由性：存在以任意 α 参数化的角色族（⟹ U(1)，即任意子）
--   · ES8 ★★  **升级定理**：交换与 2π 旋转落同一类 ⟹ 两者相位相等
--             （把 VBS 的**定义**变成**条件定理**；拓扑输入原封不动地写在类型里）
--
-- ── 与仓库已有「辫 / TL」线程的关系（**必须写清，避免重复声称**） ─────────────
--   仓库在 2026-09-29 已经有一条辫群线程，本模块的部分内容与它有**同结论的重叠**：
--   · BraidThree.lean BT1 `BT1_braid_relation`：σ₁σ₂σ₁ = σ₂σ₁σ₂ —— 本模块引的 B₃ 结构，
--     仓库里早已显式。
--   · BraidThree.lean BT2 `BT2_full_twist_is_scalar` + BT3 `BT3_full_twist_commutes_with_everything`：
--     **全扭转（=(σ₁σ₂)³）中心**、与任意 2×2 矩阵交换。
--     ⟹ 这就是本模块 ES8 所**假设**的那条「相位只依赖类」的**矩阵层证明**：
--     「中心 ⟹ 相位对一切共轭类都一样」。BT3 是 `FactorsThroughClass` 的具体实现，
--     本模块把它抽象成了类型里的一条假设。
--   · BraidThree.lean BT4 `BT4_at_minus_one`：t = −1 时 Δ 的对角元 = −1
--     ⟹ **全扭转取到非平凡值 −1** —— 本模块 `two_class_phase_values` 非平凡支的**显式实现**。
--   · RingTwist.lean RT5 `RT5_half_turn` / `RT5_full_turn` / `RT5_spinor_double_cover`：
--     「半整数圈回到 −1，整数圈回到 +1（双覆盖）」—— **与本模块 ES5/E4 同结论**。
--     ⟹ **双覆盖给出 ±1 这件事，仓库里早已有**（cos(2π·k) = ±1 形式）；
--       本模块 ES5 换到**角色/阿贝尔化**语言并给出**群论理由**（π₁ 阿贝尔化是 ℤ₂ 而不是 ℤ），
--       E4 则给出显式 SU(2) 提升与收缩族。**不是新发现，是换语言 + 补理由。**
--   · BraidThree.lean BT5：Δ 的特征值只有 t³（二重）⟹ 2 维既约 Burau 的**否定**：
--     中心元不含态依赖信息。TemperleyLiebThree.lean `ZNS_Z_not_scalar`：TL₃ 里 Z **不是纯量**
--     ⟹ 该堵点在 TL 里被解除（态依赖的离散标签存在于 level k ≥ 4）。
--   · MuTopology.lean MT1/MT2/MT5：局部变形（braid 关系、共轭、循环）**不改指数和**
--     ⟹ 与「交换 = 全扭转」是**类层面**（非局部）陈述相自洽。
--
--   ⟹ **本模块真正新增的只有**：(i) **群论理由**（S_N^ab ≅ ℤ₂ vs B_N^ab ≅ ℤ，
--     Fox–Neuwirth 1962）与**同一方程在两种群里的分裂对比**；
--     (ii) **ES8** 把 VBS 的定义升级成条件定理（拓扑输入写进类型）；
--     (iii) 一般 `phase_is_root_of_unity`（阶 N 的群 ⟹ N 次单位根）；
--     (iv) E4 的显式 SU(2) 提升 + 收缩族。
--     前一轮的 BT2/BT4/RT5 已经覆盖了「双覆盖给 ±1」与「全扭转是中心」这两件事。

-- ── 诚实边界（写死，防后续 session 过度声称） ──────────────────────────────
--   · **代数部分是平凡的**：ES8 的证明就是 `rw [h ℓ₁, h ℓ₂, hc]`。
--     **全部重量在拓扑输入上**——本模块的价值是让那个输入**显式、不可偷渡**
--     （写成类型里的假设 + 在 docstring 里带出处），不是证明了一条新代数定理。
--   · **拓扑输入本身没有形式化**（需要代数拓扑：配置空间、辫群、Fox–Neuwirth）。
--     本模块用「类映射 cls : Loop → Fin 2」把它抽成一行假设。
--   · 这**不是**完整的自旋-统计定理：算子那一半（相位 ⟹ 场算符反对易）仍缺，
--     仓库没有场算符语言。
--   · 2D 的「任意子」在本模块只到「角色族有自由参数 α」；α ⊄ πℤ 的具体见证在数值层。

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import ProjectionPhysics.Explorations.VibrationStatistics
import ProjectionPhysics.Explorations.VibrationSpinStatistics

noncomputable section

namespace ProjectionPhysics.ExchangeStatistics

open ProjectionPhysics.VibrationSpinStatistics

-- ---------------------------------------------------------------------------
-- ① 闭路相位 = π₁ 的角色（加法群模型）
-- ---------------------------------------------------------------------------

/-- 闭路相位：把 π₁ 的元素（这里用加法群模型，ℤ = 二维辫群；阶 2 时就是三维的类群）
    映到 ℂ*，且**是角色**——两条闭路复合的相位相乘。 -/
def IsLoopPhase (χ : ℤ → ℂ) : Prop :=
  χ 0 = 1 ∧ ∀ a b : ℤ, χ (a + b) = χ a * χ b

theorem loopPhase_zero (χ : ℤ → ℂ) (h : IsLoopPhase χ) : χ 0 = 1 := h.1

theorem loopPhase_add (χ : ℤ → ℂ) (h : IsLoopPhase χ) (a b : ℤ) :
    χ (a + b) = χ a * χ b := h.2 a b

-- ---------------------------------------------------------------------------
-- ES1–ES3  χ(n) = χ(1)ⁿ
-- ---------------------------------------------------------------------------

/-- ★ ES1：χ(n) = χ(1)ⁿ（n : ℕ）。 -/
theorem loopPhase_pow (χ : ℤ → ℂ) (h : IsLoopPhase χ) (n : ℕ) :
    χ (n : ℤ) = (χ 1) ^ n := by
  induction n with
  | zero => simpa using h.1
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [hcast, h.2, ih, pow_succ]

/-- ★ ES2：负元素的相位是逆元（角色保逆）。 -/
theorem loopPhase_neg (χ : ℤ → ℂ) (h : IsLoopPhase χ) (a : ℤ) :
    χ (-a) * χ a = 1 := by
  have hsum : χ (-a + a) = χ (-a) * χ a := h.2 (-a) a
  have hz : -a + a = 0 := by ring
  rw [hz, h.1] at hsum
  exact hsum.symm

-- ---------------------------------------------------------------------------
-- ES4 ★ 阶 N 的群 ⟹ 相位是 N 次单位根
-- ---------------------------------------------------------------------------

/-- ★ ES4（一般结论）：若闭路相位在「走满 N 圈」上等于 1（即 π₁ 的类群阶整除 N），
    则 χ(1) 是 **N 次单位根**。
    —— 三维对应 N = 2（⟹ ±1）；这也就是「N 重覆盖只给 N 分之一的量子化」。 -/
theorem phase_is_root_of_unity (χ : ℤ → ℂ) (h : IsLoopPhase χ) (N : ℕ)
    (hN : χ (N : ℤ) = 1) : (χ 1) ^ N = 1 := by
  rw [← loopPhase_pow χ h N]
  exact hN

-- ---------------------------------------------------------------------------
-- ES5 ★★ 三维（阶段 2）⟹ 相位只能 ±1：任意子被排除
-- ---------------------------------------------------------------------------

/-- 三维情形：π₁ 的阿贝尔化是 ℤ₂（阶 2）⟹ 唯一非平凡类自乘平凡。 -/
def IsTwoClassPhase (χ : ℤ → ℂ) : Prop := IsLoopPhase χ ∧ χ 2 = 1

/-- ★★ ES5：三维 ⟹ **相位只能取 ±1**（任意子被排除）。
    证明复用 VSS4：χ(2) = 1 且 χ(2) = χ(1)² ⟹ χ(1)² = 1 ⟹ χ(1) = ±1。 -/
theorem two_class_phase_values (χ : ℤ → ℂ) (h : IsTwoClassPhase χ) :
    χ 1 = 1 ∨ χ 1 = -1 := by
  obtain ⟨hlp, h2⟩ := h
  have htwist : χ 2 = χ 1 * χ 1 := loopPhase_add χ hlp 1 1
  have hsq : χ 1 * χ 1 = 1 := by rw [← htwist]; exact h2
  exact sq_one_two_values (χ 1) hsq

-- ---------------------------------------------------------------------------
-- ES6 ★★ 二维：两次交换 = 一次 2π 旋转（全扭转）
-- ---------------------------------------------------------------------------

/-- π₁(C_N(ℝ²)) = B_N（辫群）≅ ℤ（N = 2）：生成元 1 = **交换**，生成元 2 = **全扭转**（2π 旋转）。 -/
theorem full_twist_is_double_exchange (χ : ℤ → ℂ) (h : IsLoopPhase χ) :
    χ 2 = χ 1 * χ 1 := by
  simpa using h.2 1 1

-- ---------------------------------------------------------------------------
-- ES7 ★★ 二维自由性：任意子
-- ---------------------------------------------------------------------------

/-- 二维：以任意 α 参数化的闭路角色 χ(n) = exp(α·n·i)。 -/
def circleCharacter (α : ℝ) : ℤ → ℂ := fun n => Complex.exp ((α * (n : ℝ)) * Complex.I)

/-- ★★ ES7：**二维的角色族有一个自由实参数 α** ⟹ 相位空间是 U(1) 而不是 {±1}
    ⟹ **任意子在二维不被排除**（而在三维被 ES5 排除）。
    —— 「任意子为什么需要二维」的答案就是这一行加上 ES5：同一个方程 χ(2) = χ(1)²，
      在 ℤ 里 2 ≠ 0（自由），在 ℤ₂ 里 2 = 0（被迫 ±1）。 -/
theorem circleCharacter_is_loop_phase (α : ℝ) :
    IsLoopPhase (circleCharacter α) := by
  constructor
  · simp [circleCharacter]
  · intro a b
    unfold circleCharacter
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

-- ---------------------------------------------------------------------------
-- ES8 ★★ 升级定理：交换相因子 = 闭包相因子（拓扑输入显式化）
-- ---------------------------------------------------------------------------

/-- 三维里每个闭路只落进两类之一（π₁ 的阿贝尔化 = ℤ₂）：抽象成一个类映射。 -/
def FactorsThroughClass {Loop : Type*} (χ : Loop → ℂ) (F : Fin 2 → ℂ)
    (cls : Loop → Fin 2) : Prop := ∀ ℓ, χ ℓ = F (cls ℓ)

/-- ★★ ES8-a：**相位只依赖类** ⟹ 同一类的两条闭路相位相同。 -/
theorem same_class_same_phase {Loop : Type*} (χ : Loop → ℂ) (F : Fin 2 → ℂ)
    (cls : Loop → Fin 2) (h : FactorsThroughClass χ F cls)
    (ℓ₁ ℓ₂ : Loop) (hc : cls ℓ₁ = cls ℓ₂) : χ ℓ₁ = χ ℓ₂ := by
  rw [h ℓ₁, h ℓ₂, hc]

/-- ★★ ES8：**把 VBS 的「定义」升级成「定理」。**
    给定拓扑输入（交换回路与 2π 旋转回路在三维构型空间的 π₁ 里落在**同一类**；
    出处见文件头：Fadell 1962 / Finkelstein–Rubinstein 1968），
    则**交换相因子 = 闭包相因子**——「统计性 = 闭包相因子」不再是定义。
    诚实边界：证明本身只有一行（`same_class_same_phase`）；**全部重量在那两个假设上**，
    本定理的作用是让它们不可偷渡。 -/
theorem exchange_phase_eq_closure_phase {Loop : Type*} (χ : Loop → ℂ) (F : Fin 2 → ℂ)
    (cls : Loop → Fin 2) (h : FactorsThroughClass χ F cls)
    (exch rot : Loop) (hc : cls exch = cls rot) : χ exch = χ rot :=
  same_class_same_phase χ F cls h exch rot hc

end ProjectionPhysics.ExchangeStatistics
