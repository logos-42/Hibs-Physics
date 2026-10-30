-- ProjectionPhysics — AetherSync：以太同步的防火墙形式化（候选 a / b）
--
-- leo（2026-10-29，攻防审稿 R4 → 落地）：「候选 (a)(b) 把真空变成防火墙」
--   全库 `simultaneity / Einstein synchronization / preferred foliation` grep 为零，
--   是真空；这里把它补成可机器核查的防火墙条款。
--
-- 读法（本模块只把这句话写成命题，不做新公设）：
--   · 以太（P1）给的是拖曳下的**同一同时面 / 同一相位参考**（branch Ⅰ 共相位，dτ=0），
--     绝不给比特；信号仍受 GQC3 局部光锥约束。
--   · 同时关系 S(i,j) ⟺ xi i = xi j（xi = 静态坐标 − 拖曳 φ）在流动系是良定义的
--     等价关系（传递/对称/自反）；但在静止系里它被拖曳破坏——这正是"它不是信道"的记号。
--   · 关键防火墙：xi 在静止系**非单射** ⟹ 接收端只看 xi（或同 σ 相位）无法恢复静态标号
--     ⟹ 不携带比特。信道需要"可分辨的符号"（AB8），共相位提供不了。
--
-- 诚实边界（写死）：
--   · 本模块用 Fin 2 的具体实例演示"类空间隔落在同一同时面"与"xi 非单射"，
--     是示意性证明，不是一般时空定理；一般情形需接 GQC3 的流动坐标 ξ_k = k − φ_k。
--   · "no-bit" 在这里 = "从 xi 单射恢复标号不可能"，是信息论下界的最弱形式；
--     它不证明超光速信令不可能（那由 AB7–AB9 负责），只证明"同时面本身"不是信道。
--   · 零新可检验预言：本模块是防火墙的拓扑约束，不是新数值。
--
-- 死法（写死）：
--   ① 若在静止系里 xi 变成单射（拖曳被完全消除），则"no-bit"论证失去支点——
--       但那是退化为无拖曳，恰说明同步需要拖曳，不是信道。
--   ② 若有人把 S 重写为"可承载比特的映射"（injectivity 到比特空间），则直接撞
--       paper3 死法 (c)「与已确立物理事实矛盾」——本模块显式不含此类公理。

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

namespace ProjectionPhysics.AetherSync

-- ===========================================================================
-- 候选 (a)：同时面  S(i,j) ⟺ xi i = xi j
-- ===========================================================================

/-- 拖曳下的同时坐标：静态位置 pos 减去拖曳场 φ。 -/
def xi (pos φ : Fin 2 → ℝ) (i : Fin 2) : ℝ := pos i - φ i

/-- 同时关系：两点共享同一拖曳坐标即落在同一同时面。 -/
def S (pos φ : Fin 2 → ℝ) (i j : Fin 2) : Prop := xi pos φ i = xi pos φ j

theorem S_refl (pos φ : Fin 2 → ℝ) (i : Fin 2) : S pos φ i i := rfl
theorem S_symm (pos φ : Fin 2 → ℝ) {i j : Fin 2} (h : S pos φ i j) : S pos φ j i := h.symm
theorem S_trans (pos φ : Fin 2 → ℝ) {i j k : Fin 2}
    (h1 : S pos φ i j) (h2 : S pos φ j k) : S pos φ i k := Eq.trans h1 h2
-- 在流动系，S 是等价关系（传递/对称/自反）。

/-- 具体实例：静态坐标 [0,2]、拖曳 [1,3] ⟹ 两点都落在 xi = -1 的同时面上。 -/
def posEx (i : Fin 2) : ℝ := if i = 0 then 0 else 2
def phiEx (i : Fin 2) : ℝ := if i = 0 then 1 else 3

/-- 两个**类空间隔**（0 ≠ 1）的点落在同一同时面：超广意场把远距离"瞬时"对齐。 -/
theorem simultaneity_spans_distance :
    (0 : Fin 2) ≠ 1 ∧ S posEx phiEx 0 1 := by
  refine ⟨by decide, ?_⟩
  simp [S, xi, posEx, phiEx]; norm_num

/-- 防火墙核心：xi 在静止系非单射 ⟹ 只看 xi 无法恢复静态标号 ⟹ 不携带比特。 -/
theorem no_bit_transmission :
    ¬ Function.Injective (xi posEx phiEx) := by
  intro h
  have eq : (0 : Fin 2) = 1 := h (by simp [xi, posEx, phiEx]; norm_num)
  exact absurd eq (by decide)

-- ===========================================================================
-- 候选 (b)：相位同步  sameσ(i,j) ⟺ 闭包相因子 σ i = σ j
-- ===========================================================================

variable {ι : Type _}
variable (σ : ι → Bool)

/-- 两点的闭包相因子相同（VBS 语言：同一 σ）。 -/
def sameσ (σ : ι → Bool) (i j : ι) : Prop := σ i = σ j

theorem sameσ_equiv (σ : ι → Bool) : Equivalence (sameσ σ) :=
  ⟨ λ (_ : ι) => rfl
  , λ {a b : ι} (h : sameσ σ a b) => Eq.symm h
  , λ {a b c : ι} (h1 : sameσ σ a b) (h2 : sameσ σ b c) => Eq.trans h1 h2 ⟩
-- 同 σ 也是等价关系。

/-- 具体实例：同 xi 类里两点也同 σ ⟹ 接收端从 (xi, σ) 仍无法区分 ⟹ 仍不携带比特。 -/
def sigmaEx : Fin 2 → Bool := fun _ => true

theorem phase_collapse :
    (0 : Fin 2) ≠ 1 ∧ sameσ sigmaEx 0 1 ∧ S posEx phiEx 0 1 := by
  have h0 : (0 : Fin 2) ≠ 1 := by decide
  have h1 : sameσ sigmaEx 0 1 := by simp [sameσ, sigmaEx]
  have h2 : S posEx phiEx 0 1 := by simp [S, xi, posEx, phiEx]; norm_num
  exact ⟨h0, ⟨h1, h2⟩⟩
