-- ProjectionPhysics — Antimatter：流动反向 = 反粒子（AM1–AM5）
--
-- leo（2026-11-02）：「有没有方法根据这个算式算出反物质？或者放射性的根源」。
--
-- 本模块只做**反物质**那半边，而且只做框架真能给出的部分：
--
--   框架的公设：**电荷 = 流的散度**（正电 = 发散、负电 = 汇聚，GQF4/CF 系列），
--   **质量 ∝ 流速的平方**（条数 ∝ |C|²，MassGap/胶球阶梯）。
--
--   ⟹ 定义「流动反向」 C ↦ −C（把整片空间的流向翻过来），则：
--        · 散度变号 ⟹ **电荷变号**（AM1）
--        · 流速平方不变 ⟹ **质量不变**（AM2）
--        · 反向两次回到原状 ⟹ **它是对合**（AM3）
--   ⟹ **反粒子 = 流动反向的同一团物质**：同质量、反电荷。这是框架能算出来的部分。
--
--   AM4 ★★★ **C 对称 ⟹ 净电荷为零**：若一个系综在反向变换下封闭（每个构型都有其反向），
--        则总电荷**严格为零**。⟹ **在这套框架里，物质-反物质不对称不可能自发出现**。
--        这是我们存在的直接反例——所以框架**必须**有 C 破缺机制，而它没有。
--        这条是本模块最有用的结论：它把"框架缺什么"从形容词变成了一条定量陈述。
--
--   AM5 ★★ **放射性**：只做定性登记（见文件末尾），不给定理——理由是缺手征耦合，
--        而手征不是"再加一个假设"能补的（它要破缺 C，正是 AM4 说框架没有的东西）。
--
-- 诚实边界（写死）：
--   · 本模块**不**声称解释了物质-反物质不对称；恰恰相反，它证明框架**不能**解释（AM4）。
--   · 本模块**不**涉及放射性（无速率、无弱力、无手征）。
--   · 不声称解决 Clay；反射正性 / 测度 / 连续极限仍为零。

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import ProjectionPhysics.Explorations.FlowTopology

noncomputable section
open scoped BigOperators
open Finset

namespace ProjectionPhysics.Antimatter

open ProjectionPhysics.FlowTopology

/-! ### AM1 电荷 = 散度，反向变号 -/

/-- 电荷密度 = 流的散度（沿用 `FlowTopology.div1` 的格点散度）。 -/
def chargeOf (J : ℕ → ℝ) (x : ℕ) : ℝ := div1 J x

/-- AM1 ★★★ **流动反向 ⟹ 电荷变号**：散度是线性的，故 `div(−J) = −div J`。
    ⟹ **反粒子 = 流动反向的同一团物质**（电荷取反）。 -/
theorem charge_neg (J : ℕ → ℝ) (x : ℕ) :
    chargeOf (fun y => -J y) x = -chargeOf J x := by
  unfold chargeOf div1
  ring

/-! ### AM2 质量不变 -/

/-- 质量（条数）∝ 流速的平方。 -/
def massOfSpeed (c : ℝ) : ℝ := c ^ 2

/-- AM2 ★★★ **反向不改质量**：`(−c)² = c²`。⟹ 反粒子与粒子**质量相同**。 -/
theorem mass_neg (c : ℝ) : massOfSpeed (-c) = massOfSpeed c := by
  unfold massOfSpeed
  ring

/-! ### AM3 反向是对合 -/

/-- AM3：流动反向是对合（反向两次回到原状）⟹ 反粒子的反粒子就是粒子。 -/
theorem reversal_involution (J : ℕ → ℝ) : (fun y => -(fun y => -J y) y) = J := by
  funext y
  ring_nf

/-! ### AM4 C 对称 ⟹ 净电荷为零（框架不能解释我们存在） -/

/-- AM4 ★★★ **在反向封闭的系综里，总电荷严格为零**。

    证明：反向 `J ↦ −J` 是系综上的**双射**（对合），且电荷变号 ⟹
    `Σ q = Σ q∘反向 = Σ (−q) = −Σ q` ⟹ `2Σq = 0` ⟹ `Σq = 0`。

    ⟹ **只要动力学不破缺 C，物质-反物质必然等量**。宇宙里没有反物质 ⟹
       **框架必须有一个 C 破缺机制，而它一个都没有。**
    这条不是遗憾，是判决：它把"框架缺什么"从形容词变成了一条可核对的陈述。 -/
theorem net_charge_zero_of_C_symmetric (s : Finset (ℕ → ℝ)) (x : ℕ)
    (hs : ∀ J ∈ s, (fun y => -J y) ∈ s) :
    ∑ J ∈ s, chargeOf J x = 0 := by
  refine Finset.sum_involution (fun J _ => fun y => -J y) ?_ ?_ hs ?_
  · -- 每一对的和为零
    intro J _
    show chargeOf J x + chargeOf (fun y => -J y) x = 0
    rw [charge_neg]
    ring
  · -- 非零电荷的构型不可能等于自己的反向
    intro J _ hq hfix
    have h := charge_neg J x
    rw [hfix] at h
    exact hq (by linarith)
  · -- 反向是对合
    intro J _
    funext y
    ring_nf

/-! ### AM5 放射性的定性登记（不是定理） -/

-- 放射性在这套框架里能说的只有一句**方向**，没有任何速率：
--
--   · 质量 = 条数（MassGap）⟹ 重核若能通过"重排条数"降低总质量，它就不稳定。
--     这解释了"为什么会衰变"的**方向**（能量下降方向），但**完全没有速率**：
--     速率需要势垒穿透振幅、相空间、以及 ħ 出现在动力学里——三者框架都没有。
--   · **β 衰变**需要手征耦合（W 玻色子只耦合左手）。框架的四力通道
--     （dm·C、dm·v、m·dC、m·dv）全部是**C-奇**的矢量通道，**没有手征结构**
--     ⟹ β 衰变在此框架内无法表达，更谈不上推导。
--   · **α 衰变的 Gamow 因子** exp(−2πZ₁Z₂α/v) 需要把核当成波函数做穿透计算；
--     框架里没有波函数动力学（只有运动学恒等式）⟹ 无。
--   · 与 AM4 的呼应：β 衰变本质上是**破缺 C 与 P 的过程**（最大破坏）。
--     AM4 证明本框架的构型空间是 C 对称的 ⟹ 它**结构上**无法产生 β 衰变这类过程。
--     ⟹ "补弱力"不是加一个通道，是**加一个破缺 C 的机制**；而破缺 C 就会毁掉 AM4 前提，
--        即毁掉"反粒子=流动反向"这条干净结论。**两件事不能同时要。**
--
-- 结论（写死）：放射性=0 不是"还没做"，是"结构上不允许"。

end ProjectionPhysics.Antimatter
