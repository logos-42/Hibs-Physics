# paper4/ — 第四篇论文

本目录是 ProjectionPhysics 的第四篇论文（第一篇 `paper/` 大一统框架；第二篇 `paper2/` 汇物理；第三篇 `paper3/` 杨—米尔斯间隙；第四篇 `paper4/` 振动坐标系下的宇宙本体）。

## 文件

| 文件 | 说明 |
|---|---|
| `projection-instant-cnot-speed.tex` | **英文版**：《The Ontology of the Universe in the Vibrating Coordinate Frame》。把 2026-10-29 四轮工作（AB/AT/VF/带结构）写成本体论论文：① 时间序 = 非对易的代数影子（AT1–AT10：顺序盲⟺可交换、平坦⟹顺序盲、梯度⟹顺序可观测、两支撑点族上时间序强度 = λ²√(Q_A·N/(N−1))）；② 无质量≠平坦更正（AT11–AT14，涡旋见证）；③ 振动坐标系（VF1–VF10，真坐标 ⟺ 相速度不一致，det J=k₁k₂(c₁−c₂)，广=起伏同一刻度）；④ 带数不是维数（ND1–ND5，1+1 维三条带必线性相关，维度=独立相位数）；⑤ 瞬时=同时面非信道（AB7–AB9 零容量 / AB18 范围×更新率 / AB12–AB15 两分支与生死线）。公设大胆：空间流动、质量=条数整数计数、电荷=散度、四力=莱布尼茨分解；全部定理 Lean 4 零 sorry。 |
| `projection-instant-cnot-speed-zh.tex` | **中文版**：《振动坐标系下的宇宙本体》。内容与英文版等同；REVTeX 4.2 + ctex（fandol）。 |
| `projection-instant-cnot-speed.pdf` | 英文版编译产物（tectonic，零错误） |
| `projection-instant-cnot-speed-zh.pdf` | 中文版编译产物（tectonic，零错误） |
| `projection-physics.bib` | 参考文献（复制自 paper3 + 新增 liu2026yangmills 自引） |
| `adversarial-review-cns.md` | 六轮攻防审稿剧本（CNS 级，含落地的防火墙段落） |
| `fig_*.png` | 数值图（源自 artifacts/aetherband、aethertime、bandstructure） |

格式与 `paper/projection-unified*.tex`、`paper2/projection-sink-photon*.tex`、`paper3/projection-yangmills-gap*.tex` 完全一致（同一 documentclass / 包 / postulate+theorem 环境 / 署名 / 中英双版 / tectonic 编译）。

## 发布

- **aiXiv（EN 单版）**：`aixiv.261030.000001` —— **v1.1**（2026-10-30 升版，`Under Review`，`is_public=1`；v1.0 保留为 `official review completed`）。v1.1 = 口径不撤回不降级 + 引用补到 30 条 + 底部 TABLE II/公式排版修复。
  详情页 `https://aixiv.science/papers/aixiv.261030.000001`。
- 中文版按 leo 规则**只留仓库**，不推送 aiXiv。
- 本版含「Note added (2026-10-30)」与 `§Six-round adversarial audit`：六轮攻防判定
  **2 条撤回（瞬时⟹不可传信、以太=P1 换名）+ 4 条降级（时间=非交换、带数不是维数、
  群速度更正相速度、无质量=无散度）**，正文保留原推导链以显示来源，以更正注为准。

## 编译

```bash
cd paper4 && tectonic projection-instant-cnot-speed.tex
cd paper4 && tectonic projection-instant-cnot-speed-zh.tex
```

## 结构

10 节：1 Introduction（四块结构 + 主张 + 是什么/不是什么 + 读法）→ 2 Postulates（四公设）→ 3 The layer model of the aether（AB1–AB18、两分支、两死线）→ 4 Order as the algebraic shadow of time（AT1–AT10 + 两支撑点族定量桥 + 无质量≠平坦更正）→ 5 The vibrating coordinate frame（VF1–VF10）→ 6 Band structure（TC1–TC6 / GD1–GD9 / ND1–ND5）→ 7 The assembled chain（识别层叙事）→ 8 Relation to the question as posed → 9 Honest assessment → 10 Conclusion + COI/Data availability。

格言：Roy Batty「Tears in Rain」独白（《银翼杀手》1982）；中文版配中文译文格言。

## 诚实边界（全文贯穿）

- **本体论主张 + 诚实设界**：公设大胆（振动坐标系=宇宙本体），但每条识别层主张（时间序=非对易影子、带数=维数、广=起伏、瞬时=同时面）都标为框架的提议而非伪装成定理；初等数学元件（AB2 无界、AB7–9 零容量、GD8 群速度差）如实标注，新在组织成振动坐标系的本体论结构。
- **N6 定量桥**：λ²√(Q_A·N/(N−1)) 只在两支撑点族（起伏集中两点间，含 N=2）精确，一般构型不成立（线性斜坡偏差 15.5%）；定性内容（Q_A=0⟹时间序消失）普遍成立。
- 时间 = 非对易是**解释层读法**，不是定理；「无质量⟹平坦」已撤回（AT11–AT14 证伪：平坦 ⊊ 无质量；涡旋 v=(0,1,1,0) 保留时间序 AT13）。
- 分支Ⅱ的 ratio 是**新无量纲输入**（与 λ、M₀ 同款），未闭合；AB12 是生死线。
- GD5（群速度=导数）未 Lean 证（mathlib v4.35 工程缺口），数值替身；维数上限只覆盖 1+1 维。
- 死法：分支Ⅰ死于 k=0 模携带时变符号；分支Ⅱ死于 ratio 可由公设导出或观测到第三种快因子；平坦读法死于平坦场两汇算子不交换；维数上限死于 1+1 维三条线性无关相位。

## 关联

- 配套 Lean 模块（Explorations/）：AetherBand.lean（AB1–18）、AetherTime.lean（AT1–14）、VibrationFrame.lean（VF1–10）、TimeCount.lean（TC1–6）、DispersionGeneral.lean（GD1–9）、BandDimension.lean（ND1–5）、AetherSync.lean（防火墙：同时面非信道）。
- wiki：theory-aether-band.md、theory-aether-time.md、theory-vibration-frame.md、theory-band-structure.md。

## 状态

**攻防审稿中（6 轮子智能体 referee 对抗，进行到第 2 轮）。** 审阅通过后才发布（GitHub 仓库 + aiXiv）。