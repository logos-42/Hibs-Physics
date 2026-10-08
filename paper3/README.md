# paper3/ — 第三篇论文

本目录是 ProjectionPhysics 的第三篇论文（第一篇在 `paper/`，大一统框架；第二篇在 `paper2/`，汇物理：电荷、反引力、光子、自旋 1/2、双流环装置）。

## 文件

| 文件 | 说明 |
|---|---|
| `projection-yangmills-gap.tex` | **英文版**：《The Mass Gap and Self-Interaction in Flowing Space: Discreteness, Noncommutativity, and a Lattice Yang--Mills Structure》。把 2026-10-07 的 Lean 推导链写成论文：① 质量间隙种子（MG1–MG4：质量=整数条数 ⟹ 区间 (0,M₀²) 空）② 自相互作用（YM1–YM3：汇收缩迭代自抹平、双汇非对易、交换差=λ²×梯度）③ 格点杨-米尔斯（CA1–CA6：格点规范场、场强=近邻交换子）④ 连续极限机制（CA8–CA10：四力求导作为存在性机制）⑤ 严格估计（L1–L3：交换子范数有界、导数通道、范数非零）+ 组装链（CA7/CA10）。 |
| `projection-yangmills-gap-zh.tex` | **中文版**：《流动空间中的质量间隙与自相互作用：离散性、非对易性与格点杨--米尔斯结构》。内容与英文版等同；REVTeX 4.2 + ctex（fandol）。 |
| `projection-yangmills-gap.pdf` | 英文版编译产物（tectonic，零错误） |
| `projection-yangmills-gap-zh.pdf` | 中文版编译产物（tectonic，零错误） |
| `projection-physics.bib` | 参考文献（复制自 paper2 + 新增 Yang–Mills 1954、Jaffe–Witten 2000、Peskin–Schroeder） |

格式与 `paper/projection-unified*.tex`、`paper2/projection-sink-photon*.tex` 完全一致（同一 documentclass / 包 / postulate+theorem 环境 / 署名 / 中英双版 / tectonic 编译）。

## 编译

```bash
cd paper3 && tectonic projection-yangmills-gap.tex
cd paper3 && tectonic projection-yangmills-gap-zh.tex
```

## 结构

10 节：1 Introduction（学术规范引言：大问题/缺口/路线图/与既有工作对话/动机史）→ 2 Postulates（流动空间 / 质量=条数 / 电荷=散度 / 四力=莱布尼茨分解，每条带 Reading）→ 3 Mass gap from discreteness（MG1–MG4）→ 4 Self-interaction from sink noncommutativity（YM1–YM3b）→ 5 Lattice Yang–Mills（CA3–CA6）→ 6 Continuum-limit mechanism（CA8–CA10）→ 7 Strict estimates（L1–L3）→ 8 The assembled chain（CA7/CA10）→ 9 Honest assessment → 10 Conclusion + 开放问题清单（6 条）。

16 定理 + 5 公设，每条定理前有直觉段、后有 Reading 解读段；具体数字（YM1 λ=½ n=10 → (½)²⁰≈10⁻⁶、L1 常数 6=2×3、MG4 整数胶球）钉住抽象结果。格言：英文版 Thales「Water is the origin of all things.」/ 中文版《道德经》「有物混成，先天地生。」（老子 第二十五章）。

## 扩充记录（2026-10-08）

按学术审稿人标准扩充（498→972 行英文，子智能体按 excellent-paper-patterns.md 的 15 条模式执行）：
- 引言 4 段→8 段：大问题（Yang–Mills 1954→Clay 千禧年→格点胶球谱 1.6–1.7 GeV / X(2370) 实证锚点）、尖锐缺口（标准 QFT **假设**自相互作用、**测量**质量间隙，两者互不相关）、动机史（黎曼猜想→隐数空间→费米/玻色不能共存→顿悟）、与既有工作对话、如何读本文预告
- 每条定理加直觉段 + 物理解读；新增 MG4（胶球质量平方为整数）、YM3b（|交换差|=λ²|v_q−v_p|）两个 Lean 已验证定理
- 诚实边界派生：not-claimed 从 4 条扩到 5 条（新增：格点是一维的，不声称 3+1 维）；开放问题 6 条（推导 M₀ / λ / 拓扑极限 / 矩阵值 L2 / 3+1 维 / λ²(v_q−v_p) 可观测对应）
- 中文版逐段镜像英文版，label/引用键 34/34 + 18/18 完全一致（程序化验证）

## 引言重构（2026-10-08，用户审阅反馈）

**问题**：引言 8 段太复杂，被段落标签稀释，价值点被淹没。

**修法**：引言压到 **4 段**，每段言之有物——
1. 问题之名所携带的两个事实（离散性 + 自相互作用，标准框架两者皆非推导）
2. **本文的论断**（4 条 bullet，直接摆出 Lean 验证的定理：质量间隙=整数算术、自相互作用=汇非对易性、场强=近邻交换子、连续极限=四力导数）
3. 本文是什么，不是什么（诚实边界一句话 + 指向 Sec IX）
4. 如何阅读本文（精简为一段）

**移入正文**：
- 动机史（黎曼猜想→隐数空间→顿悟）→ 移到第 II 节公设之后「动机：链条如何生长」
- 与既有物理学的对话（保留/反对/新增）→ 移到第 VIII 节组装链之后「与既有物理学的关系」
- 框架介绍（河流模型、前篇成果）→ 压缩进第 2 段公设概述

双版同步重构，label 34/34、引用 17/17、引言段落数 4/4 程序化验证一致。

## 诚实边界（全文贯穿）

- **不声称解决杨–米尔斯问题**：格点构造是代数骨架，不是连续四维量子场论；无路径积分/重整化/连续时空。
- 格距→0 的拓扑极限未形式化（第 7 节开放层，最重）。
- λ、M₀、抹平动力是输入而非推导。
- 汇非对易 ⟷ [A,A] 是解释层对应；离散→连续收敛属于开放层。
- 死法三条：无离散对应物的自相互作用 / 格点场强不收敛到连续 / 非对易自相互作用无质量下界。

## 状态

**待用户审阅**。审阅通过后才发布（GitHub 仓库 + aiXiv）。
