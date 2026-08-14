# paper/ — 论文目录

本目录是 ProjectionPhysics 的论文输出位。

## 文件

| 文件 | 说明 |
|---|---|
| `projection-physics.tex` | **论文主文件**。REVTeX 4.2，`\documentclass[aps,prd,preprint,superscriptaddress]{revtex4-2}`——单栏 preprint（Physical Review D 风格），最接近 arXiv 理论物理论文格式 |
| `projection-physics.bib` | 参考文献（18 条，全真实：Gordon 1923 / Hamilton–Lisle 2008 / Morningstar–Peardon 1999 / Chen 2006 / Aspect 1982 / PDG 2024 / de Moura CADE-15 等） |
| `projection-physics.pdf` | 编译产物（tectonic 0.17.0，20 页，零错误零 overfull） |
| `apstemplate.tex` / `apssamp.tex` / `apssamp.bib` / `fig_*.eps` / `vid_*.eps` | APS 官方 REVTeX 模板样例（下载的 zip 原样保留，投稿参考用，不属于论文） |

## 编译

本机无 LaTeX 发行版，用 tectonic 单二进制：

```bash
~/.local/bin/tectonic projection-physics.tex
```

（tectonic 自动处理 bibtex 多趟编译；首次运行联网下载所需包。）

Overleaf 用户：直接上传 `projection-physics.tex` + `projection-physics.bib`，
文档类选 REVTeX 4.2 即可。

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
