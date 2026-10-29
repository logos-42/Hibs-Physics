---
title: 带结构三件：时间计数接口 / 一般色散与群速度 / 带数 ⟷ 维数（TC1–ND5）
source: session
created: 2026-10-29
last_confirmed: 2026-10-29
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: claim
tags: [time-count, dispersion, group-velocity, band, dimension, closure, aether]
status: current
---

# 带结构三件：时间计数 / 一般色散 / 带维度

> leo（2026-10-29 四续）：「按优先级完成，1，2，3 都做完。」
> ① 时间计数接口　② 一般色散下的振动坐标与群速度　③ 带的个数 ⟷ 振动坐标的维数

对应代码（三个新模块，全部零 sorry）：
- [`ProjectionPhysics/Explorations/TimeCount.lean`](../../ProjectionPhysics/Explorations/TimeCount.lean)（TC1–TC6）
- [`ProjectionPhysics/Explorations/DispersionGeneral.lean`](../../ProjectionPhysics/Explorations/DispersionGeneral.lean)（GD1–GD9）
- [`ProjectionPhysics/Explorations/BandDimension.lean`](../../ProjectionPhysics/Explorations/BandDimension.lean)（ND1–ND5）
- [`scripts/verify_band_structure.py`](../../scripts/verify_band_structure.py)（N1–N14，`artifacts/bandstructure/`）

## 1. ① 时间计数接口：闭包次数 ⟷ 带指标

接口只有一行：**一次闭合 = 相位走 2π = 位移一个波长**，于是

```text
跨度 L 上的时间计数（闭合次数）  n = k · L / 2π
计数密度                        ρ = k / 2π = 1/λ

⟹ 时间单位数 = 带指标 × 跨度 / 2π
```

这把两轮的东西接成同一个量：VBC4/VBC5 说「时间单位 = 闭合次数」（相位侧的定义），
VF5/VF8 说「带指标 k 与波长 λ = 2π/k」（空间侧的刻度）——本页证明**两者是同一个数的两种写法**。

| 定理 | 内容 | 数值 |
|---|---|---|
| TC1 | `timeCount_eq_density_mul`：n = ρ·L | N1：2.33e−16 |
| TC2 | `timeCount_add`：n(L₁+L₂) = n(L₁)+n(L₂) | N2：3.06e−16 |
| **TC3** | `timeCount_one_wavelength`：**n(k, 2π/k) = 1** | N3：1.1e−16（6 个 k 含负值） |
| **TC4** | `timeCount_depends_on_band`：k₁ ≠ k₂ ⟹ ∃L 使计数不同 | N4：L=2π 时 n = 1.000 vs 2.500 |
| TC5 | `timeCount_zero_band`：k=0 ⟹ 计数恒 0 | N5：三跨度全 0.0 |
| **TC6** | `countGap_density_eq_inverse_beatWavelength`：**\|Δk\|/2π = 1/λ_beat** | N6：2.8e−17 |

**结论**：时间计数与「广」是**同一个刻度**——「更广」= 计数差更小 = 拍频周期更长。
且**绝对时间计数不存在**（TC4）：只有「某条带上的计数」。

## 2. ② 一般色散：判据不变，但「快」必须拆成两根轴

VF2 的判据原来是 `det = k₁k₂(c₁−c₂)`（线性色散专用）。一般色散下：

```text
det₂(m₁,m₂) := k₁ω₂ − k₂ω₁ = k₁k₂(v_ph,2 − v_ph,1)      v_ph = ω/k
⟹ 退化判据仍然只有一句：两带相速度相同（GD1/GD2，k≠0）

二次色散族 ω = c·k + β·k²：
   det₂ = k₁k₂β(k₂−k₁)        v_ph = c + βk      v_g = dω/dk = c + 2βk
   v_g − v_ph = βk
```

| 定理 | 内容 | 数值 |
|---|---|---|
| **GD1** | `det2_eq_speed_diff`：det = k₁k₂(v_ph,2 − v_ph,1) | N7：300 组（一般 ω）**0.00e+00** |
| **GD2** | `det2_eq_zero_iff`：det = 0 ⟺ v_ph 相同 | N8：同速 6 对全 0、异速 \|det\|=1.0 |
| GD4 | `quad_det2`：二次族 det = k₁k₂β(k₂−k₁) | N9：3.9e−15（相消量） |
| GD7 | `linear_dispersion_speeds_equal`：**β=0 ⟹ v_g = v_ph** | N11：两者 = 0.4000 |
| **GD8** | `nonlinear_speeds_differ`：**β≠0 ∧ k≠0 ⟹ v_g ≠ v_ph** | N11：1.2500 vs 0.8250 |
| **GD9** | `quad_group_speed_gap`：Δv_g = 2βΔk | N12：\|Δv_g\|·λ = 4π\|β\|（2.4e−16） |
| GD9b | `quad_group_gap_abs`：\|Δv_g\| = 2\|β\|\|Δk\| | 同上 |

**两条必须一起说的结论**：

1. **AB 轮的更正**：AB2 说「相位速度无界」。在**线性**色散下 v_g = v_ph，所以把它读成「信号更快」无害；
   但在**一般**色散下 v_g ≠ v_ph（GD8），**相位速度无界不能读成信号更快**——信号（包络）走 v_g。
   这是 AB 那条直觉的正确边界，已在 AB 页与本页同时登记。
2. **「广 ⟹ 涟漪更慢」**（GD9）：\|Δv_g\|·λ_beat = 4π\|β\| ⟹ 波长越长（越广），拍频包络走得越慢；
   λ→∞ 时群速度差→0，即**包络冻结**。这与 AB17（k=0 ⟹ 静态）是同一件事的两个说法。

## 3. ③ 带数 ⟷ 维数：多带不是高维

相位是 (k, ω) 与 (x, t) 的内积。**在 1+1 维时空里 (k, ω) ∈ ℝ²**，所以：

```text
任意三条带都线性相关 ⟹ 第三条带不增加独立坐标 ⟹ 振动坐标的秩 ≤ 2 = 时空维数
（要第 3 个独立振动坐标，必须升**空间维数**，而不是再加一条同向的带）
```

| 定理 | 内容 | 数值 |
|---|---|---|
| **ND1** | `exists_coefficients`：Cramer 解 a,b 使 k₃ = a k₁ + b k₂ ∧ ω₃ = a ω₁ + b ω₂ | — |
| **ND2** | `third_band_redundant`：θ₃(x,t) = aθ₁ + bθ₂ 对一切 (x,t) | N13：残差 **7.1e−15**（300 组） |
| ND3 | `nontrivial_relation`：系数 (−a,−b,1) 非平凡 | — |
| **ND4** | `count_redundant`：n₃(L) = a n₁(L) + b n₂(L) | N14：2.2e−16 |
| ND5 | `global_modes_no_coordinates`：k=ω=0 ⟹ 三条相位恒 0 | — |
| — | 秩封顶（数值）| N14：rank(3 带 × (k,ω)) = **2** |

**结论**：**「维度」的第一个可算版本 = 独立相位的个数 = min(带数, 空间维数+1)**。
在 1+1 维里，加带永远加不出第 3 个坐标；而且连时间计数也不会增加（ND4）——
第三条带的计数只是前两条的同一个线性组合。

## 4. 数字汇总（`artifacts/bandstructure/`，N1–N14 全过）

| 断言 | 结果 |
|---|---|
| N1/N2 计数 = 密度×跨度 / 可加 | 2.33e−16 / 3.06e−16 |
| **N3 一个波长 = 一次闭合** | 1.1e−16（k 含负值） |
| **N4 计数依赖带** | 1.000 vs 2.500 |
| N5 全局模 | 0.0 |
| **N6 计数差密度 = 1/λ_beat** | 2.8e−17 |
| **N7 一般色散 det** | 0.00e+00（300 组） |
| **N8 det=0 ⟺ 同相速度** | 6 对全 0；异速 \|det\|=1.0 |
| N9 二次族 det | 3.9e−15 |
| **N10 群速度 = 导数** | 二次精确 1.4e−13；三次误差比 **{4.000, 4.000}** |
| **N11 线性 ⟹ 相等 / 非线性 ⟹ 不等** | 0.4 vs 0.4；1.25 vs 0.825 |
| **N12 \|Δv_g\|·λ = 4π\|β\|** | 2.4e−16 |
| **N13 三带相关** | 7.1e−15（a=2.3050, b=−1.1650） |
| **N14 计数冗余 + 秩=2** | 2.2e−16；rank = 2 |

## 5. 诚实边界（写死）

1. **二次色散族是模型选择**（选它因为 v_g 有闭式）。一般 ω(k) 下 v_g 仍是 dω/dk，只是没有闭式。
2. **GD5（v_g 就是导数）在 Lean 里没有证**：v4.35 的 `HasDerivAt.pow` 与本文件的 ℝ 实例不同源
   （`Semiring.toModule` vs `NormedField.toNormedSpace.toModule`），`simpa` 统一不了；这属形式化工程问题。
   已用**数值替身**代替（N10：二次上中心差分精确、三次上误差比 = 4 = O(h²)，与 YM-S3 同一手法），
   并在 Lean 文件里显式登记这一空缺。
3. **「维度 = min(带数, d+1)」只有 1+1 维被覆盖**；高维是读法，本页没有形式化 d ≥ 2。
4. 时间计数是**相位圈数**，不是钟读数；把它等同于物理时间是 VBC 的口径（闭合次数 = 时间单位）。
5. **零新可检验预言**。

## 6. 死法（写死）

1. **①**：k≠0 的带在一个波长内不产生一次闭合 ⟹ TC3 死；两条不同 k 的带在**所有**跨度上计数相同 ⟹ TC4 死。
2. **②**：k≠0 且相速度相同但 det ≠ 0 ⟹ GD2 死；群速度差与 1/λ 不成正比 ⟹ GD9 只在二次族成立。
3. **③**：在 1+1 维里找到三条**线性无关**的相位 ⟹ 秩封顶死；第三条带的计数与前两条不合适 ⟹ ND4 死。

## 7. 下一步（已登记，未做）

1. **d 维空间**：把 rank 上界从 2 推到 d+1（需要 (x₀,x₁,…,x_d) 与 (ω,k₁,…,k_d) 的内积形式化）。
2. **一般色散的群速度闭式**：把 GD5 的 Lean 缺口补齐（换实例或用 `deriv` 的 API 而不是 `HasDerivAt.pow`）。
3. **时间计数 → 钟读数**：把 n 从实数取整为整数并与 VBC1（`winding_index_integer`）对齐。
