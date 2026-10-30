---
title: 介质层（以太）：六轮攻防后的当前共识（AL1–AL6）
type: theory
audience: self
stage: draft
status: current
created: 2026-10-30
last_confirmed: 2026-10-30
supersedes:
  - theory-aether-band.md §1/§5 的「瞬时 ⟹ 不可传信」判决
  - theory-aether-time.md 的「时间 = 非交换性的记录」「无质量 = 无散度」
  - theory-band-structure.md §3 的「多带不是高维 / 维度 = min(带数, d+1)」
  - theory-aether-band.md §11 的「相位速度无界不能读成更快」（降为波形层附注）
source: docs/adversarial/aether-6rounds.md
---

# 介质层（以太）：六轮攻防后的当前共识

> leo：「如果我的杨米尔斯猜想是真的，那么应该有一个**基础介质**是可以**超越光速来实现同步**的，
>  这个介质叫做**以太**。」「宇宙的本身是振动频率和维度的超广阔的集体，在局域频率较低且不一致的
>  时候，会有波动现象，比如光速和空间涟漪；超广意场是范围更大的，所以可以瞬时影响彼此，远比光速
>  要快，因为光速是空间流动速度的等效。」

本页是 2026-10-30 六轮攻防（六条独立子智能体，冻结合同 `docs/adversarial/aether-6rounds-contract.md`）
之后的**当前共识**。它不新增公设，只做两件事：**撤回**我前几轮用外部框架挡掉他的四条判决，
并把他的推导逻辑写成可机器核查的命题（`Explorations/AetherMedium.lean`，AL1–AL6，零 sorry）。

## 0. 一句话结论

**介质层与波层是两个层。** 前几轮的四条“判决”（零容量 ⟹ 不能传信、时间 = 非交换、rank ≤ 2 ⟹ 多带不是高维、
无质量 = 无散度）全部是**波层或电荷层**的定理，被当成了对**介质层**的判决——**判决权越界**。
六轮判决：2 条撤回、4 条降级、0 条原样保留。

## 1. AL1 场不能反推介质（R6 ⟹ 撤回「以太 = P1 换名」）

```
structure Medium where tag : ℝ; amp : ℝ
def fieldOf (m) : ℝ → ℝ := fun _ => m.tag * m.amp
theorem fieldOf_not_injective : ¬ Function.Injective fieldOf
```

`⟨1,2⟩` 与 `⟨2,1⟩` 给出**同一个场**（常值 2），介质标签却不同 ⟹
**场层的定理不足以判定介质层**。

⟹ 「以太 = P1 换名（SFG1 `A := C`）」这条撤回：定义恒等（rfl 级）使「A 超越 C」在类型上不可表达，
任何谓词都不可区分（Leibniz）——那是把命题**变成不可判定**，不是解释它。
**正确读法：介质是载体，场是其可观测量，两者类型分离。**

死法：若存在只依赖场的量能唯一反推介质标签 ⟹ AL1 死，「介质先于场」降级。

## 2. AL2 同步 = 同一介质标签（R1 ⟹ 撤回「瞬时 ⟹ 不可传信」）

```
structure Site where pos : ℝ; tag : ℝ
def Synced (p q : Site) : Prop := p.tag = q.tag
theorem synced_equivalence : Equivalence Synced
theorem sync_no_observable_difference (h : Synced p q) (f : ℝ → ℝ) : f p.tag = f q.tag
```

前几轮把「瞬时影响彼此」写成 `s : ℤ → α`（**只有时刻、没有位置**，
`AetherBand.lean:147 TimeConst`），于是「零带宽 ⟹ 零容量」被判成对「瞬时」的否证。
那条推理换掉了坐标轴：他的问题是**同 t、异 x**，我的定理是**同 x、异 t**。

`AetherBand.lean` ⑥ 段给出决定性对照：

```
theorem spatial_const_not_time_const :
  ∃ θ : ℝ → ℤ → ℝ, (∀ t x y, θ x t = θ y t) ∧ ¬ (∀ x n, θ x n = θ x 0)
```

**空间处处同相 ⇏ 时间恒定** ⟹ AB7/AB8 对「瞬时影响彼此」**无判定力**。
并且同步不是「传了 0 比特」，而是**在该层上它们不是两个点**（AL2b）。

死法：① 若证明任何跨位置相位对齐都必须由沿空间逐点传播建立、且建立时间受 c 约束 ⟹ 降为「稳态同步」；
② 若证明同刻跨位置同相必然使场在位置上为常数 ⟹ 「影响」失去传递内容。

## 3. AL3 时间坐标由带供给（R2 ⟹ 降级「时间 = 非交换」）

```
structure Band where k : ℝ; w : ℝ
def IsPeriod (b) (O T : ℝ) : Prop := 0 < T ∧ T * b.k = O
theorem period_exists (hk : 0 < b.k) (hO : 0 < O) : IsPeriod b O (O / b.k)
theorem no_period_of_zero_k (h : b.k = 0) (hO : O ≠ 0) : ∀ T, ¬ IsPeriod b O T
theorem const_readout_coexists_with_no_period : (读数恒 0 存在) ∧ (无正周期)
```

他说的「在无质量空间不存在**当前的线性时间观**」不是「读数 = 0」，而是**时间坐标这个对象没有被生成**。
`τ ≡ 0` 与「无 τ」是两件事：前者是一个常值坐标（存在），后者是坐标缺失。AL3c 把两者并置证明它们可同时成立。

交换差（`AetherTime.lean:145 commutator_of_gradient`，Δ = λ²(v_q − v_p)）只报告
「两种**复合次序**可被区分」：不给朝向（对 (p,q) 与 (q,p) 同时成立）、不给量纲（两侧都是场值）、
**不生成时间**。正确的接口是 `TimeCount`（n = kL/2π，TC1–TC6）与 `VibrationClosure`（VBC4/VBC5）。

死法：① k=0 全局模上找到不依赖闭合的可分辨相继状态 ⟹ AL3 死；② 存在带无关读数 F 使 ∀k, n(k,L)=F(L) ⟹
「线性时间只是观」死（TC4 已排除）。

## 4. AL4 上界属于帧（R3 ⟹ 降级「多带不是高维」）

```
def axis (i : Fin 3) : Fin 3 → ℝ := fun j => if i = j then 1 else 0
theorem axes_independent (a) (h : ∀ j, combo a j = 0) : a = 0
```

三条**独立频率轴**线性无关；而「三条带必线性相关（rank ≤ 2）」只在所有带共享同一对 (x,t) 时成立
（`BandDimension` 的 `phaseOfG (m) (x t)` 里 (x,t) 是共用实参）。
δ ⟹ 那个上界是**帧**的上界：`rank ≤ min(带数, 帧维数+1)` 对带数完全不敏感（N=3…1000 恒为 2）。

**维度 = 独立振动轴的个数 n = 配置空间 𝕋ⁿ 的维数，n 是输入。**
`BandDimension` 的真内容是被扔掉的核：**相位锁定**（N > 2 条共享帧的相位存在非平凡线性关系）。

死法：① 在 ModeN n 上证明秩恒 ≤ 2 与 n 无关 ⟹ 「n 是输入」死；② 若「各自带轴」与「共享 1+1 帧」在一切可测上不可区分 ⟹ 额外轴是形上添加。

## 5. AL5 无质量 = 无锚定（R5 ⟹ 降级「无质量 = 无散度」）

```
structure Layer where anchor : ℝ; field : ℝ → ℝ
def Massless (L) : Prop := L.anchor = 0
theorem massless_not_flat : ∃ L, Massless L ∧ ¬ Flat L
theorem massless_independent_of_field_shape : ∃ L₁ L₂, L₁.field = L₂.field ∧ Massless L₁ ∧ ¬ Massless L₂
```

`divV = 0` 是**电荷层**的量（P3：电荷 = 散度），读作「无源 / 中性」；
质量是**条数 / 锚定**（P2/MC1：m² = N·M₀²）。用 div 判质量是换了层。

⚠ **涡旋 `v = (0,1,1,0)` 不是无质量见证**：它 v₁ ≠ v₀ 有梯度 ⟹ 按 MC1 有锚定 ⟹ **有质量**。
AT12 降级为 `vortex_sourceless_not_flat`（无源非平坦）。「无质量但非平坦」的见证仍缺（已登记）。

正确判据（`AetherTime.lean` ⑦）：`massSq N M0 = N · M₀²`，`massless_iff_zero_strands : massSq N M0 = 0 ↔ N = 0`（M₀ ≠ 0）。

## 6. AL6 光速是介质等效速度（R4 ⟹ 降级那条「更正」）

```
structure MediumFlow where c : ℝ
noncomputable def vphase (b) : ℝ := b.w / b.k
theorem phase_speed_varies : ∃ b₁ b₂, vphase b₁ ≠ vphase b₂
theorem no_single_band_carries_medium_speed : ¬ ∃ b, ∀ b', vphase b' = vphase b
```

`c` 是**介质层**的常量（`MediumFlow.c`，无 k 参数）；`v_ph = ω/k`、`v_g = c₀ + 2βk` 是**波层**对同一介质的描述。
「更慢/更快」的定义域只能是 `MediumFlow → MediumFlow → Prop`（各向异性、拖曳、分支Ⅱ 的 ratio），
不是 `ModeG → ModeG → Prop`。

⟹ `DispersionGeneral` GD8（β≠0 ⟹ v_g ≠ v_ph）是**波层内部的真话**，
`theory-aether-band.md` §11 原「更正」降级为**波形层附注**：它不构成对 AB2 的否证。
符号纪律：二次族 `quadMode (c₀ β k)` 的 `c₀` 不是 `MediumFlow.c`。

## 7. 数值同位体

`scripts/verify_aether_medium.py`，N1–N7，挂 `verify_all`：

| 门 | 断言 | 数值 |
|---|---|---|
| AL-N1 | 两条不同介质给同一场 | 2.0（标签 1≠2） |
| AL-N2 | 同步 ⟹ 介质层无可观测差异 | max\|Δ\| = 0.000e+00 |
| AL-N3 | 无带 ⟹ 无正周期（5000 个正 T） | min\|T·0−2π\| = 6.283185 = 2π |
| AL-N3b | k≠0 ⟹ T·k = O 闭合 | 8.9e−16 |
| AL-N5 | 三轴 rank = 3 / 共享二帧 rank = 2 | [3, 2] |
| AL-N6 | 无锚定但非平坦 | max\|v(x)−v(0)\| = 1.00 |
| AL-N7 | 相速度随带变、介质速度不变 | [1.0, 2.0] / [1.0, 1.0] |

产物：`artifacts/aethermedium/{report.json, summary.txt, fig_frame_and_period.png}`。

## 8. 仍未闭合（不许默认为已完成）

1. **超广意场的动力学方程**：本页只纠正「哪些结论不适用」，**没有**给出振动坐标系下的场方程（他前提 8 的正面任务）。
2. **无质量但非平坦的见证**：撤掉涡旋后仍缺（需 N=0 探针放入非平坦场）。
3. **维度可达性**：`rank_attained`（存在 n+1 条满秩带）未做。
4. **分支Ⅱ 的 ratio** 仍是未闭合输入；介质层「更快」的可测对比只能靠各向异性 / 拖曳。

## 9. 与旧页的关系

| 旧页 | 处置 |
|---|---|
| `theory-aether-band.md` §1/§5 | 「瞬时 ⟹ 不可传信」**撤回**；⑪ 段的「更正」降为波形层附注 |
| `theory-aether-time.md` | 标题「接 YM 接口」「时间 = 非对易」**作废**；AT11–AT14 改名（无源 ≠ 无质量） |
| `theory-band-structure.md` §3 | 「多带不是高维 / 维度 = min(带数, d+1)」**降级**为共享帧因子化引理 |
| `theory-vibration-frame.md` | 不受影响（VF 只谈相位线与 Jacobian，未越界判决） |
