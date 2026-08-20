---
title: 时空冻结：物质时间冻结（dτ=0）与空间本身冻结（稳态场）
source: session
created: 2026-08-20
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theory
tags: [time-freeze, symplectic, mass-cancellation, horizon, steady-state]
---

# 时空冻结（TimeFreeze）

## 核心命题

leo 问题（2026-08-20，接 dengyu.pdf 的"粒子粗粒化不可逆 / 辛体积可逆"）：

1. **真正的时空冻结**在操作上是否比"抽能量冷却"简单？
2. 在我们的体系里是否已有框架？

答案（Lean `ProjectionPhysics/TimeFreeze.lean` TF1–TF3 / SZ1–SZ5 / C1–C3 全证零 sorry，
数值 `scripts/verify_time_freeze.py` N1–N6 全机器精度）：

- ① **是**——几何路径（抹平流动梯度 / 稳态化 / 视界）成本 ∝ 梯度² 可任意小；
  热力学冷却路径成本 ∝ 1/T_cold 发散（第三定律）
- ② **是**——AMC（质量取消 dτ=0）、BH（视界冻结）、SF（边界维持能量）
  已给出全部构件，本模块统一成"冻结"概念

## 关键定理

### ① 物质时间冻结（质量取消路径，接 AMC2→SM1）

| 定理 | 内容 | 接轨 |
|---|---|---|
| **TF1★** | `time_freeze_iff_comoving`：dτ²=0 ⟺ dx²=(c·dt)²——时间冻结 ⟺ 随流 | SM1 双向代数版 |
| **TF2★** | `mass_cancel_time_freeze`：m_eff²=0 ⟹ 随流位移 ⟹ dτ²=0——质量取消 ⟹ 物质不花自己的时间 | AMC1→AMC2→SM1 链 |
| TF3 | `time_freeze_any_external_dt`：外部坐标时间 dt 任意，物质自身 dτ²=0——冻结是局部的 | SM3 |

### ② 空间本身冻结（稳态场 ∂_t C = 0）

| 定理 | 内容 | 接轨 |
|---|---|---|
| SZ1 | `SteadySpaceField`：C(t+1)=C(t)（离散稳态） | MS：∂_tC=0 |
| **SZ2★** | `steady_field_step_invariant`：稳态 ⟹ 任意步场不变（ℤ 双向归纳）——信息静止 | GQC1 信息守恒 |
| **SZ3★** | `steady_field_no_electric`：稳态 ⟹ E=−∂_tC=0——冻结空间无电场活动 | MS：E=−∂_tC |
| **SZ4★** | `steady_field_time_reversal_symmetric`：稳态 ⟹ C(t−1)=C(t+1)——冻结时空天然可逆（逆转=什么都不做） | 辛可逆 |
| **SZ5★** | `time_dilation_mono_near_horizon`：v→c ⟹ γ=1/√(1−v²/c²) 无界发散——视界处外部时间冻结 | BH1：视界=光速面 |

### ③ 代价账本：几何冻结 vs 热力学冷却

| 定理 | 内容 | 接轨 |
|---|---|---|
| **C1★** | `geometric_freeze_cost_arbitrarily_small`：抹平成本 ∝ g²，∀ε ∃g 成本<ε——几何路径无成本下限 | AMC3 |
| C2 | `space_freeze_sustain_cost_positive`：稳态边界维持能量 ½νB² 正定——冻结不是免费 | SE5/SF11 |
| **C3★** | `thermal_cooling_cost_grows_as_colder`：制冷功 Q(T_hot/T_cold−1) 随 T_cold→0 严格发散——热力学路径无上界 | 卡诺/第三定律 |

## 数值验证（scripts/verify_time_freeze.py，artifacts/timefreeze/）

- **N1** 质量取消时间冻结：μ=1 ⟹ m_eff²=0 精确；随流位移 dτ² ≡ 0.0（机器精度）；
  对照锚定物质 dτ²=5.76（仍花时间）
- **N2** 空间冻结无电场：稳态场 ΔC=0、E=0（残差 0.0）；对照振荡场 E=0.52（非冻结有活动）
- **N3** 视界冻结：γ 单调递增（SZ5），v=0.999999c ⟹ γ=707、v=0.99999999c ⟹ γ=7071；
  g_tt→2e-8（BH1 视界=光速面）
- **N4** 代价对比：制冷到 1K 需 2.99e8 J → 到 0.001K 需 3.0e11 J（1003× 发散）；
  抹平成本 g=1→1e-4 时 0.5→5e-9（收敛）
- **N5** 边界维持：δ_max ∝ B 线性（斜率恒定 2.828，SF11 复现）；E_rot ∝ B² 正定
- **N6** 冻结可逆：稳态场时间反演对称（C(t−1)=C(t+1)）✓ + 信息静止（任意步=初值）✓

图：`artifacts/timefreeze/fig_freeze_cost_paths.png`（热力学发散 vs 几何收敛）、
`fig_time_freeze_paths.png`（视界膨胀 + 质量取消曲线）。

## 直接回答

1. **真正的时空冻结操作上更简单**——因为它是几何路径（抹平流动梯度 / 稳态化），
   不是热力学路径（抽熵）。成本账本：抹平成本 ∝ 梯度²（弱场区便宜、均匀区零成本），
   可任意小；制冷成本 ∝ 1/T_cold（T→0 发散，第三定律）。
2. **体系内已有框架**：质量取消（AMC1–AMC2，物质 dτ=0）、视界（BH1–BH2，
   外部时间冻结）、边界维持（SF11/SE5，稳态的代价）、信息守恒（GQC1，冻结=信息静止）。
   TimeFreeze.lean 把这些统一成"冻结"概念并给出可逆性定理（SZ4：冻结时空时间反演对称）。

## 诚实边界（四层判定）

- **数学恒等**：TF1–TF3（随流⟺dτ²=0）、SZ2–SZ4（稳态⟹平移不变/无电场/反演对称）、
  SZ5（膨胀因子单调）、C1–C3（成本序关系）——真但平凡（SM/BH/SF 重述）
- **结构对应**：量子 Zeno（频繁投影冻结）、Landauer（擦除耗能）、卡诺第三定律、
  视界时间冻结均为已知物理
- **数值匹配**：无新常数产生
- **概念重构**："冻结=几何操作非热力学操作""冻结时空可逆""信息静止=冻结"
  是解释层（与 GQC1 辛体积可逆同体系）

**未建模**：稳态时空的存在性（需满足 Einstein 方程的边界应力，未构造）；
"冻结=信息转移到边界"是全息层注释；μ 的主动产生机制（第二输入缺口未变）；
无新物理预言。

## 下一步候选

- ZenoFreeze.lean：频繁幂等投影（PA 系列）⟹ 演化锁死在像空间——"扫描=冻结"的代数证明
- TimeReversal.lean：哈密顿流可逆 φ_t∘φ_{−t}=id + 时间反演=反辛对合，挂 GQC1
- dengyu 桥梁：粗粒化投影（N 粒子相空间 → 一粒子密度）⟹ 不可逆的定理化
