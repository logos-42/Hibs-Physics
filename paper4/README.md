# paper4/ — 第四篇论文

本目录是 ProjectionPhysics 的第四篇论文（第一篇 `paper/` 大一统框架；第二篇 `paper2/` 汇物理；第三篇 `paper3/` 杨—米尔斯间隙；第四篇 `paper4/` 振动坐标系下的宇宙本体）。

## 文件

| 文件 | 说明 |
|---|---|
| `projection-instant-cnot-speed.tex` | **英文版**：《The Ontology of the Universe in the Vibrating Coordinate Frame》。2026-10-29 四轮工作（AB/AT/VF/带结构）的本体论论文：① 时间序 = 非对易的代数影子（AT1–AT10）；② 无质量≠平坦更正（AT11–AT14，涡旋见证）；③ 振动坐标系（VF1–VF10，真坐标 ⟺ 相速度不一致，det J=k₁k₂(c₁−c₂)，广=起伏同一刻度）；④ 带数不是维数（ND1–ND5）；⑤ 瞬时=同时面非信道（AB7–AB9 / AB18 / AB12–AB15）。**§X（2026-11-01 新增）**：质量间隙来自非阿贝尔规范场的闭合性——四维非阿贝尔格点场（plaquette / 局部协变 / Wilson 迹 / 与维数无关的范数界）、规范自由度继承自流动前提、闭合迫使绕数取整 ⟹ 条数由场给出 ⟹ 谱落在零或单价之上（Y4D/F4D/GT/FT/MB/LAD）。全部定理 Lean 4 零 sorry。 |
| `projection-instant-cnot-speed-zh.tex` | **中文版**：《振动坐标系下的宇宙本体》。内容与英文版等同（含 §X 镜像）；REVTeX 4.2 + ctex（fandol）。 |
| `projection-instant-cnot-speed.pdf` | 英文版编译产物（tectonic，零错误） |
| `projection-instant-cnot-speed-zh.pdf` | 中文版编译产物（tectonic，零错误、零缺字形） |
| `projection-physics.bib` | 参考文献（复制自 paper3 + 新增 liu2026yangmills 自引） |
| `adversarial-review-cns.md` | 六轮攻防审稿剧本（CNS 级，含落地的防火墙段落） |
| `fig_*.png` | 数值图（源自 artifacts/aetherband、aethertime、bandstructure） |

格式与 `paper/projection-unified*.tex`、`paper2/projection-sink-photon*.tex`、`paper3/projection-yangmills-gap*.tex` 完全一致（同一 documentclass / 包 / postulate+theorem 环境 / 署名 / 中英双版 / tectonic 编译）。

## 发布

- **aiXiv（EN 单版）**：`aixiv.261030.000001` —— 线上 **v1.1**（2026-10-30 升版，`Under Review`，`is_public=1`；v1.0 保留为 `official review completed`）。v1.1 = 口径不撤回不降级 + 引用补到 30 条 + 底部 TABLE II/公式排版修复。
  详情页 `https://aixiv.science/papers/aixiv.261030.000001`。
- **本地 v1.2（2026-11-01，待 leo 审阅后升版）**：新增 §X「A mass gap from the closure of a non-Abelian gauge field」（ZH 镜像同名节）+ 2026-11-01 note + 摘要一句 + 引言/公设/路线图/诚实评估同步。**发布前需 leo 点头**。
- 中文版按 leo 规则**只留仓库**，不推送 aiXiv。
- v1.1 含「Note added (2026-10-30)」与 `§Six-round adversarial audit`；v1.2 追加「Note added (2026-11-01)」。

## 编译

```bash
cd paper4 && tectonic projection-instant-cnot-speed.tex
cd paper4 && tectonic projection-instant-cnot-speed-zh.tex
```

判据：`^error` 为空 + `note: Writing ...pdf`；ZH 版另查 `Missing character` 为空（①②③ 这类圈号在 lmroman 里缺字形，已统一改成 (i)(ii)(iii)）。

## 结构

12 节：1 Introduction → 2 Postulates（四公设 + 条数不是自由整数）→ 3 The layer model of the aether（AB1–AB18、两分支、两死线）→ 4 Order as the algebraic shadow of time（AT1–AT10 + 两支撑点族定量桥 + 无质量≠平坦更正）→ 5 The vibrating coordinate frame（VF1–VF10）→ 6 Band structure（TC1–TC6 / GD1–GD9 / ND1–ND5）→ 7 The assembled chain → 8 Relation to the question as posed → 9 Six-round adversarial audit（2026-10-30）→ **10 A mass gap from the closure of a non-Abelian gauge field（2026-11-01）** → 11 Honest assessment → 12 Conclusion + COI/Data availability。

格言：Roy Batty「Tears in Rain」独白（《银翼杀手》1982）；中文版配中文译文格言。

## 诚实边界（全文贯穿）

- **本体论主张 + 诚实设界**：公设大胆（振动坐标系=宇宙本体），但每条识别层主张（时间序=非对易影子、带数=维数、广=起伏、瞬时=同时面）都标为框架的提议而非伪装成定理；初等数学元件（AB2 无界、AB7–9 零容量、GD8 群速度差）如实标注，新在组织成振动坐标系的本体论结构。
- **N6 定量桥**：λ²√(Q_A·N/(N−1)) 只在两支撑点族（起伏集中两点间，含 N=2）精确，一般构型不成立（线性斜坡偏差 15.5%）；定性内容（Q_A=0⟹时间序消失）普遍成立。
- 时间 = 非对易是**解释层读法**，不是定理；「无质量⟹平坦」已撤回（AT11–AT14 证伪：平坦 ⊊ 无质量；涡旋 v=(0,1,1,0) 保留时间序 AT13）。
- 分支Ⅱ的 ratio 是**新无量纲输入**（与 λ、M₀ 同款），未闭合；AB12 是生死线。
- GD5（群速度=导数）未 Lean 证（mathlib v4.35 工程缺口），数值替身；维数上限只覆盖 1+1 维。
- **§X 的边界（写死）**：间隙是构造的输出（闭合 ⟹ 绕数整数 ⟹ 条数由场给 ⟹ 谱 0 或 ≥ M₀），不是计数公设的推论；「间隙与非交换无关」的旧说法已按**编码更正**撤回（交换子不进入间隙，但场通过绕数进来）。仍缺三件（属解释层）：(i) 矩阵 plaquette → 拓扑荷（Pontryagin 指数）的桥；(ii) 一层坐几个态的规则；(iii) 单价随扇区变（共用单价被四个实测比值在 10⁴–10⁵σ 排除，自由变价被 MB5 证为不可证伪）。**没有**测度 / 反射正性 / 连续极限（Y4D9 + FT4：缺的是度量不是拓扑）；**没有**禁闭、没有重整化、没有 Wightman/OS；J^PC、宽度、产生率一概没碰。
- 死法：分支Ⅰ死于 k=0 模携带时变符号；分支Ⅱ死于 ratio 可由公设导出或观测到第三种快因子；平坦读法死于平坦场两汇算子不交换；维数上限死于 1+1 维三条线性无关相位；§X 的简并读法死于「两态质量不收敛到同一个数」（相邻台阶读法要求比值停在 √(7/6)=1.0801）。

## 关联

- 配套 Lean 模块（Explorations/）：AetherBand.lean（AB1–18）、AetherTime.lean（AT1–14）、VibrationFrame.lean（VF1–10）、TimeCount.lean（TC1–6）、DispersionGeneral.lean（GD1–9）、BandDimension.lean（ND1–5）、AetherSync.lean（防火墙：同时面非信道）。
- §X 配套：YangMillsFourD.lean（Y4D1–9）、FlowFourD.lean（F4D1–7）、GapFromTopology.lean（GT1–5）、FlowTopology.lean（FT1–5）、MassBookkeeping.lean（MB1–7）、GlueballLadder.lean（LAD1–7）。
- 数值：`scripts/verify_mass_bookkeeping.py`（→ `artifacts/mass_bookkeeping/report.json`）、`scripts/verify_glueball_ladder_prediction.py`（→ `artifacts/glueball_ladder/report.json`）。
- wiki：theory-aether-band.md、theory-aether-time.md、theory-vibration-frame.md、theory-band-structure.md、theory-yangmills-fourd.md、theory-mass-bookkeeping.md。

## 状态

**v1.1 已发 aiXiv（Under Review）；v1.2 新增 §X 与 2026-11-01 note，本地双版编译通过（0 error），等 leo 审阅后升版。**
