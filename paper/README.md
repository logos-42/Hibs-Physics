# paper/ — 论文目录

本目录是 ProjectionPhysics 的论文输出位。

## 文件

| 文件 | 说明 |
|---|---|
| `projection-unified.tex` | **大一统论文（英文版，2026-08-16）**：《The Geometric Description of Physics at the Cosmic Scale》（物理学在宇宙尺度下的几何的描述）。流动空间大一统：质量=辛纠缠体积（Cauchy-Binet 链）、信息=辛体积（传输/因果/等效超光速/全域相干）、四力=流动动量莱布尼茨分解、光子=激发电子螺旋、量子关系从螺旋几何涌现（E=ħω、p=h/λ、E=hf、圆周=波长）、胶球/夸克与"3"的贯穿。REVTeX 4.2 + 6 张配图（figures_en/） |
| `projection-unified-zh.tex` | **大一统论文（中文版）**：《物理学在宇宙尺度下的几何的描述》。内容与英文版等同；REVTeX 4.2 + ctex（fandol），配图用 figures/ |
| `projection-unified.pdf` | 大一统英文版编译产物（tectonic，零错误） |
| `projection-unified-zh.pdf` | 大一统中文版编译产物（tectonic，零错误） |
| `figures/` | 中文版配图（6 张，源自 artifacts/qftflow/：fig_triple_rank / fig_tilted_lightcone / fig_charge_helix / fig_photon_models / fig_photon_turns / fig_antiphase_global） |
| `figures_en/` | 英文版配图（同 6 张，EN tex 引用此目录） |

## 编译

本机无 LaTeX 发行版，用 tectonic 单二进制：

```bash
```

（tectonic 自动处理 bibtex 多趟编译；首次运行联网下载所需包。中文版 PDF
体积较大是因为嵌入了 fandol 中文字体。）


## 结构

11 节 + 1 附录：1 Introduction → 2 Postulates（SLS1–4）→ 3 Mass as
symplectic entanglement volume（Cauchy-Binet 链）→ 4 Information
（GQC1–3 + 全域相干 QFT5）→ 5 The four forces（莱布尼茨分解）→
6 The photon（激发电子螺旋）→ 7 The quantum relations from helix
geometry（GQR1–6）→ 8 Glueball, quark, and the one "3"（√N·M₀）→
9 Numerical validation（N1–N29）→ 10 Honest assessment（4 层判定）→
11 Conclusion → 附录 A 完整推导链（公设 → 6 条链 → 预言 → 诚实边界，
逐步标注 Lean 定理与数值验证号）。

## 注意

- preprint 模式（单栏）下 REVTeX 静默忽略 `\keywords` 和 `\pacs`——
  转 `twocolumn`（正式投稿版）时会显示。
- 论文内容全部来自 `docs/wiki/` 共识（wiki-first），§8 诚实 4 层判定与
  `current-status.md` 一致：当前为概念重构层，无新物理声称。
