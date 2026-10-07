# paper2/ — 第二篇论文

本目录是 ProjectionPhysics 的第二篇论文（第一篇在 `paper/`，大一统框架）。

## 文件

| 文件 | 说明 |
|---|---|
| `projection-sink-photon.tex` | **英文版**：《Divergence, Sink Contraction, and the Half-Phase Geometry: Charge, the Antigravity Field, the Photon, and Spin 1/2 from Flowing Space》。把两条 2026-10-06 的线合并成一篇：① 电荷 = 流散度源/汇 + 加速电荷 ⟹ 反引力 ⟹ 光子推导链（CF1–CF5 / CR1–CR5）+ 收敛 = 抹平的向心收缩平方衰减定理（CR7–CR10）；② 临界叶半相位几何 ln(√e)=½ 定位自旋½（CS1–CS5）。末尾接双流环装置应用（自抹平 132→85 步）。 |
| `projection-sink-photon-zh.tex` | **中文版**：《散度、汇收缩与半相位几何：流动空间中的电荷、反引力场、光子与自旋 1/2》。内容与英文版等同；REVTeX 4.2 + ctex（fandol）。 |
| `projection-sink-photon.pdf` | 英文版编译产物（tectonic，零错误） |
| `projection-sink-photon-zh.pdf` | 中文版编译产物（tectonic，零错误） |

格式与 `paper/projection-unified*.tex` 完全一致（同一 documentclass / 包 / postulate+theorem 环境 / 署名 / 中英双版 / tectonic 编译）。

## 编译

```bash
cd paper2 && tectonic projection-sink-photon.tex
cd paper2 && tectonic projection-sink-photon-zh.tex
```

## 结构

9 节：1 Introduction → 2 Postulates（SLS / 三方向锚定 / 四力）→ 3 Charge as flow divergence（CF1–CF5）→ 4 Accelerated charge ⟹ field varies; nuclear channel（CR1–CR2）→ 5 Convergence is flattening: sink contraction（CR7–CR10）→ 6 Half-phase geometry: spin 1/2（CS1–CS5）→ 7 Device application: two-flow-ring optimization → 8 Numerical verification → 9 Honest assessment → Conclusion。

诚实边界（§9）：条件链（若抹平发生则光子）、λ/δ/ε 是输入、连续 3D 对应未形式化、自旋统计定理仍是半条、无新可检验预言。

## 与 paper/ 的关系

- `paper/` 是大一统框架（质量/信息/四力/光子/量子关系/胶球），8-16 定稿；
- `paper2/` 是 2026-10-06 新增的两条线（电荷–反引力–光子 + 自旋½ 几何），自成一篇。