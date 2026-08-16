# paper/ — 论文目录

本目录是 ProjectionPhysics 的论文输出位。

## 文件

| 文件 | 说明 |
|---|---|
| `projection-physics.tex` | **论文主文件（英文版）**。REVTeX 4.2，`\documentclass[aps,prd,preprint,superscriptaddress]{revtex4-2}`——单栏 preprint（Physical Review D 风格），最接近 arXiv 理论物理论文格式 |
| `projection-physics-zh.tex` | **中文版**（内容与英文版等同）。REVTeX 4.2 + ctex（`fontset=fandol`），编译器需 XeLaTeX（tectonic 自动处理） |
| `projection-physics.bib` | 参考文献（18 条，全真实：Gordon 1923 / Hamilton–Lisle 2008 / Morningstar–Peardon 1999 / Chen 2006 / Aspect 1982 / PDG 2024 / de Moura CADE-15 等），两版共用 |
| `projection-physics.pdf` | 英文版编译产物（tectonic 0.17.0，20 页，零错误零 overfull） |
| `projection-physics-zh.pdf` | 中文版编译产物（tectonic 0.17.0，13 页，零错误零 overfull） |
| `projection-unified.tex` | **大一统论文（英文版，2026-08-16）**。流动空间大一统：质量=辛纠缠体积（Cauchy-Binet 链）、信息=辛体积（传输/因果/等效超光速）、四力=流动动量莱布尼茨分解、光子=激发电子螺旋、量子关系从螺旋几何涌现（E=ħω、p=h/λ、E=hf、圆周=波长）、胶球/夸克与"3"的贯穿。REVTeX 4.2 + 7 张配图（paper/figures/） |
| `projection-unified-zh.tex` | **大一统论文（中文版）**。内容与英文版等同；REVTeX 4.2 + ctex（fandol） |
| `projection-unified.pdf` | 大一统英文版编译产物（tectonic，零错误，仅 1 处 overfull 警告） |
| `projection-unified-zh.pdf` | 大一统中文版编译产物（tectonic，零错误零警告） |
| `figures/` | 大一统论文配图（7 张，源自 artifacts/qftflow/：fig_triple_rank / fig_tilted_lightcone / fig_charge_helix / fig_photon_models / fig_photon_turns / fig_circumference_wavelength / fig_antiphase_global） |
| `apstemplate.tex` / `apssamp.tex` / `apssamp.bib` / `fig_*.eps` / `vid_*.eps` | APS 官方 REVTeX 模板样例（下载的 zip 原样保留，投稿参考用，不属于论文） |

## 编译

本机无 LaTeX 发行版，用 tectonic 单二进制：

```bash
~/.local/bin/tectonic projection-physics.tex      # 英文版
~/.local/bin/tectonic projection-physics-zh.tex   # 中文版（XeLaTeX 引擎，ctex+fandol 字体）
```

（tectonic 自动处理 bibtex 多趟编译；首次运行联网下载所需包。中文版 PDF
体积较大是因为嵌入了 fandol 中文字体。）

Overleaf 用户：直接上传 `projection-physics.tex` / `projection-physics-zh.tex`
+ `projection-physics.bib`，文档类选 REVTeX 4.2；中文版编译器选 XeLaTeX。

## 结构

10 节 + 2 附录：1 Introduction → 2 Postulates（SLS1–4）→ 3 Mathematical
structure → 4 Mass（MC1–MC2，胶球 √N·M₀）→ 5 Electrodynamics as
kinematics（MS1–MS5）→ 6 Gravitation（Gordon/Φ=½v²/黑洞公设版）→
7 Numerical validation（两表）→ 8 Relation to existing physics（诚实 4 层
判定）→ 9 Discussion（预言 P1–P4 + 开放问题）→ 10 Conclusion → 附录 A
Lean 形式化总览 → 附录 B 6 个证明要点。

## 注意

- preprint 模式（单栏）下 REVTeX 静默忽略 `\keywords` 和 `\pacs`——
  转 `twocolumn`（正式投稿版）时会显示。
- 论文内容全部来自 `docs/wiki/` 共识（wiki-first），§8 诚实 4 层判定与
  `current-status.md` 一致：当前为概念重构层，无新物理声称。
