---
title: 魔角石墨烯 × 聚变——场天花板七层账本（计划）
source: session
created: 2026-09-23
last_confirmed: 2026-09-23
audience: self
stage: draft
schema_version: 2
confidence: unverified
entity_type: meta
tags: [moire, matbg, field-ceiling, ledger, plan]
status: current
---

# 魔角石墨烯 × 聚变：场天花板七层账本（计划）

> 本页是**计划**（判决漏斗 + 执行清单），结果页 = [theory-moire-field-ceiling.md](./theory-moire-field-ceiling.md)。
> 金额一律不入库（规则沿用前几轮）。

## §0 问题

leo：魔角石墨烯（1° 夹角）方案如果用来产生磁场、再由磁场引发引力场约束，实现可控核聚变——
**这个方案会产生的数据如何变化？**

本计划不回答"石墨烯能不能超导"（实验已答：能，Tc ~ 1–3 K），而回答：
把本仓库已证的约束/输运/场源公式里的场源**换成一个魔角石墨烯线圈**，
PF/FC 那一串数字（场强、密度、功率、体积、所需 μ）会变成什么，以及**死在哪一层**。

## §1 方案链条拆解（六环，逐环找现实上限）

    MATBG(θ≈1.1°, N=2) 超导 ──①──▶ 线圈载流 K ──②──▶ 直流约束场 B
        ──③──▶ 等离子体密度 n (β≤1) ──④──▶ 聚变功率 P ∝ n²
        ──⑤──▶ 劳森 τ_req ──⑥──▶ 所需 μ(t)（反引力场）──▶ 约束闭合

± 旁支：时变磁场（PA4）→ 时变空间场 C → μ(t) 载体（RMF 支，FC11 已给硬天花板）。

- ①②③④⑤⑥ 每一环都可独立代入现实上限——**任何一环上限低于需求即该环出局**；
- 本轮**不**假设 μ 机制成立（第二输入缺口未变），只问：**在给定场源上限下，μ 需要做到多少、这个数是否落在 FC11 允许的窗口内**。

## §2 七层账本（每层给公式 + 判据，全部用仓库已证条目）

| 层 | 物理量 | 公式（出处） | 判据 |
|---|---|---|---|
| L1 材料层 | Tc、B_c2⊥/∥、超流面密度 n_s | 实验值（见 §6） | T_op ≤ Tc/2；场必须 < B_c2 |
| L2 导体层 | 片电流 K = J_c·d、安匝 = K/pitch | 二维导体只有 ~0.7 nm 载流通道 | K 比 REBCO 低几个量级 ⟹ 需要多少层 |
| L3 场-密度层 | B_min = √(2μ₀nkT)（PF3）；n_max = βB²/(4μ₀kT)（FC1） | PF3 / FC1 | B < B_min ⟹ β>1 不可能 |
| L4 功率层 | P ∝ n²⟨σv⟩ ⟹ ∝ β²B⁴；同功率体积 V ∝ 1/(β²B⁴) | FC1 + Bosch-Hale ⟨σv⟩ | 场天花板 ⟹ 功率天花板 ⟹ 体积下限 |
| L5 输运层 | τ_E = τ₀/√(1−μ)（二轮修正链）；τ₀ = a²/D₀；劳森 nτ = 2e20 (15 keV) | AMC1 + 碰撞输运标度 | 得 X_req ≡ (1−μ) 的上限 |
| L6 μ 窗口层 | FC11：RMF 窗口 ⟺ μ < 1−m_e/m_i ⟺ **1−μ > m_e/m_i** | FC11b（Lean 已证） | 可行 ⟺ X_req > m_e/m_i；否则 **无解**（不是更难） |
| L7 制冷层 | Carnot W/Q = T_h/T_c − 1；亚开尔文容量 mW 级 vs 装置冷量 kW 级 | 标准热力学 + 稀释制冷机容量 | 容量缺口 = 否决项 |

## §3 判决量（把"能不能"压成四个数）

- **D1 场门** χ_B = B_req(设计密度) / B_c2(场源)：>1 ⟹ 该场源不能在此密度下工作。
- **D2 μ 门★** B_death ≡ 使 X_req(B) = m_e/m_i 的场：**B < B_death ⟹ μ 窗口关闭 ⟹ 方案无解**
  （这是本轮的生死门：它把"场不够强"从"效率下降"升级为"数学上无可行解"）。
- **D3 载流门** χ_K = n_s(REBCO 片超流密度) / n_s(2D 超导体)：达到同等安匝所需层数。
- **D4 制冷门** χ_cryo = 装置冷量需求 / 亚开尔文制冷容量。

**门表（每门预写失败处置）**

| 门 | 判据 | 未过时处置 |
|---|---|---|
| G-场 | B_c2 > B_min(n_design) | 降设计密度 / 改多层（N≥3）体系 |
| G-μ | X_req(B_c2) > m_e/m_i | 该场源出局（不可通过提 μ 绕过——窗口本身关闭） |
| G-载流 | 层数需求在工艺可行域内 | 该材料只能做器件，不能做磁体导体 |
| G-制冷 | 亚开尔文容量 ≥ 冷量需求 | 该材料只能用于 mK 级小器件 |

## §4 执行清单（回填 2026-09-23）

7/7 完成（E6 见状态栏）

- [x] E1 数值脚本 `scripts/verify_moire_field.py`（M1–M8：材料上限代入 / 场-密度-功率标度 / μ 窗口判决 /
      B_death / 载流与制冷缺口 / 反事实对照 N≥3），产出 `artifacts/moirefield/`（report.json + summary.txt + **4 图**）
- [x] E2 Lean `ProjectionPhysics/MoireField.lean`（**MFC1–MFC7**：场天花板单调性 / n∝B² /
      X_req ∝ B⁴ / **死证定理 MFC4★**（X_req ≤ m_e/m_i ⟹ ∄ 可行 μ）/ MFC5★ 组合 /
      **MFC6★ 阈值 ∝ 1/a²** / MFC7 功率比 = 场比⁴），挂入聚合根，零 sorry 零 warning
- [x] E3 原始资料登记 `manifests/raw_sources.csv`（7 条：MATBG×5 / MATTG-Pauli / REBCO）
- [x] E4 wiki 结果页 `theory-moire-field-ceiling.md`
- [x] E5 回写四件套：`index.md` 链接 + `current-status.md` 条目 + `log.md` 行（python 追加，
      并顺手补 `theory-gravity-control-algebra.md` 缺 `created` 的 v1 硬伤）
- [x] E6 门禁：`wiki_check` OK / `wiki_lint --strict=v1` 0 violations /
      `raw_manifest_check` OK / `provenance_check` OK / `supersede_check` OK /
      `make test`（本次新增断言 MF-M2…MF-M8 + `verify_moire_field.py` 注册）
      — `--strict=v2` 仍有 42 条**历史存量**违规（fusion-program-roadmap / masstozero /
      theory-antigravity-confinement 等用旧枚举值 `plan`/`design`/`planning-estimate`），
      本轮两页已改为合法枚举（`meta`+`unverified` / `claim`+`medium`），**未新增违规**。
- [x] E7 commit + push（只 add 本次文件，禁 `-A`）

### §4.5 执行结果回填（六个头条数）

| 量 | 结果 |
|---|---|
| B_min（β≤1 撑住 n=1e20） | **1.099 T** |
| B_death（μ 窗口关闭阈值，a=0.2m） | **0.997 T**，且 ∝ 1/a（0.1m→1.99 T、0.05m→3.99 T） |
| MATBG N=2 面外 0.12 T | n 被截到 1.19e18（差 84×）、P ×3.2e-8、**X_req 4.59e-8 < 地板 2.194e-4 ⟹ 无解** |
| MATBG N=2 面内 1.6 T | 过场门（1.6 > 1.099，裕度 1.46×）、P ×9.99e-4（同功率体积 ×1001） |
| 工程两门 | 载流 1.3e4–4.0e5×；制冷 3.75e6× + Carnot 9.1× |
| 顺带发现 | 仓库自身 n=1e20 设计的 (1−μ)=3.24e-4 只比 FC11 地板高 **1.48×** |

## §5 诚实边界（预写）

- 全部结论 = 仓库已证条目（PF3 / FC1 / FC11b / AMC1）+ 外部实验上层限的**直接代入**——真但平凡，无新物理预言；
- μ 主动产生机制 = 第二输入缺口（未变）；本轮只计算"需要多少 μ、窗口是否打开"；
- 二维材料的 B_c2、n_s、I_c 是多器件分散的实验值，本计划取文献报道的**上界/乐观值**做包络；
- 载流门与制冷门是**量级账**（片电流 vs 安匝、mW vs kW），不是装置设计；
- 反事实对照（N≥3 多层、面内取向）只说明"同样 1° 家族里哪一档能过门"，不构成可用材料结论。

## §6 数据来源（外部，登记进 raw_sources.csv）

| 量 | 值 | 来源 |
|---|---|---|
| MATBG Tc | 1.1–2.1 K（部分器件至 3.5 K） | Cao 2018 Nature 556,43/80；Nano Lett 2022；Díez-Mérida 2023 |
| MATBG B_c2⊥ | ≈ 0.12 T | Díez-Mérida 2023 Nat. Commun. 14,2396（θ=1.11°） |
| MATBG B_c∥ | ≈ 1.6 T（≈ Pauli 限，未显著违背） | Qin & MacDonald 2021 PRL 127,097001；Cao 2021 Nature 595,526 |
| MATTG(3层) B_c∥ | > 10 T（Pauli 违背 2–3×） | Cao 2021 Nature 595,526；Park 2022 Nat. Mater. 21,877 |
| MATBG 最优掺杂 Hall 密度 | 1.96e11 cm⁻² | Nano Lett 2022（Tc≈2.1 K 器件） |
| MATBG 满填充密度 | 2.88e12 cm⁻²（θ=1.11°） | Díez-Mérida 2023 |
| MATBG 体临界电流 | 250 nA（栅定义 JJ） | Park 2025 Nat. Commun. |
| REBCO 非铜 Jc | 1500–2000 A/mm² @4.2 K/19 T | Senatore 2024 SUST |
| REBCO 片电流 Ic/width | ~960–1220 A/cm @4.2 K/19 T | 同上 |
| ITER 低温工厂 | 75 kW @4.5 K 当量 | ITER 公开参数（CFR2 同轮引用） |
| 稀释制冷机容量 | ~20 mW @0.5 K（1–2 mW @0.1 K，量级） | 商用机型公开规格 |
| 聚变锚点 | CFR2 12cm 燃烧室 7–9 T→35 T | Slough 2025（仓库已登记 slough2025cfr2） |
