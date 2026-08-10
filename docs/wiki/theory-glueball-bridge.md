---
title: 胶球桥接评估：纯胶子复合态与隐核质量
source: session + external physics references
source_note: 2026-08-10 对当前 HIBS/ProjectionPhysics 质量路线的胶球兼容性评估
created: 2026-08-10
last_confirmed: 2026-08-10
audience: self
stage: draft
schema_version: 2
confidence: low
entity_type: concept
tags: [glueball, gluon, QCD, hidden-space, mass]
status: current
---

# 胶球桥接评估

## 1. 结论

当前路线与胶球**概念上相容，但还没有胶球定理**。

相容点是：胶球是纯内部场自由度形成的复合态，而本项目已经有“核/隐空间内部结构经过非线性组合向可观测层泄露”的代数原型，以及核二次型和空间流质量候选。

不能直接相容的地方是：当前项目没有胶子、色荷、规范变换、色单态条件、禁闭能量或胶球谱。因此不能把现有 `hiddenYukawaMass = |y·v|` 直接叫作胶球质量；胶球质量应首先来自纯胶子动力学，Higgs 只应作为允许的门户/混合项。

物理目标本身应保持清楚：胶球是胶子场的色单态复合态，格点纯 Yang–Mills 计算通常首先研究 `0++`、`2++` 等谱态；这与“内部复合态先有质量、再讨论可观测投影”的方向相合，但不等于当前模型已经推出 QCD 胶球。[PDG 光介子谱综述](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-light-mesons-spectroscopy.pdf)；[纯 Yang–Mills 胶球格点研究](https://arxiv.org/abs/2211.15176)。

## 2. 当前代码能提供的接口

- `ProjectionAlgebra.lean` 已证明核元素乘积可以离开核并进入像层；这可作为“内部胶子组合产生可观测复合态”的代数类比，但不是禁闭或规范不变性。
- `HiddenOnlyHiggs.lean` 已证明核二次型 `Q_H(h)=h²`，以及隐空间位移质量 `m_flow² = Q_H(y·ΔΦ)`；这可作为纯胶子场强/流残差质量泛函的候选骨架。
- `HiddenSpacePhysics.lean` 已有空间流、旋量阻抗和三夸克质量原型；但 `QuarkTriplet` 不能直接代表胶球，因为胶球不是三夸克态。
- `HIBSPhysicalBridges.lean` 的 Yukawa、离散 beta 和质量壳均是显式桥接结构的后果；其中离散 beta 不是 QCD beta，质量壳字段也不是 HIBS A1–A3 的自动推论。

新增 [GlueballBridge.lean](../../ProjectionPhysics/GlueballBridge.lean) 已把 G1–G4 的最小依赖链编译进 Lean：

- `GaugeAction` / `GaugeInvariant`：规范作用与固定点不变量接口；
- `GluonMode` / `GluonConfiguration`：纯胶子模式和 `colorBalance = 0` 的色单态代理；
- `pureGlueMassSquared`：对隐核场强平方求和的纯胶子质量平方候选；非零隐模式使其非零；
- `GlueballChannel.scalar0pp`：只让 `0++` 通道进入 Higgs 门户；
- `MassSquaredMatrix`：胶球—Higgs 二维质量矩阵；Higgs 耦合关闭时，纯胶球基态是本征态且质量候选保持不变。

这一步证明的是结构链和解耦性质，不是 `SU(3)` Yang–Mills、禁闭或实验胶球质量。当前 `colorBalance` 和 `identityGaugeAction` 都是明确标注的代理/接口，下一步必须替换为非平凡色代数和规范作用。

## 3. 推荐的形式化路径

### G1. 纯胶子复合态（已完成最小接口）

已新增抽象 `GaugeAction` 和 `GaugeInvariant`，定义 `GluonMode`、有限胶子组合和 `gaugeInvariant` 固定点条件。`colorBalance = 0` 证明了最小色单态代理，胶球数据结构只含胶子模式、不含夸克模式。

### G2. 胶球算符与量子数（已完成最小通道）

已实现 `scalar0pp`、`tensor2pp`、`pseudoscalar0mp` 三个离散通道标签，并把通道绑定到纯胶子组合；目前还没有连续旋转群或真正的 `J^{PC}` 表示。

### G3. 纯胶子质量（已完成离散候选）

定义多分量核二次型/场流能量：

```text
pureGlueMassSq(G) = fieldEnergy(G) + confinementResidual(G)
```

当前 `fieldEnergy` 用隐核整数分量的平方和实现，并证明非零隐模式使 `pureGlueMassSquared` 非零、且质量平方非负。它是纯胶子场能量代理，尚未包含禁闭残差或空间梯度。

### G4. Higgs 门户，而非直接 Yukawa（已完成解耦定理）

只对 `0++` 胶球引入门户系数 `λ_GH`，构造胶球—Higgs 的二维质量矩阵：

```text
M² = [[m_G0²,       δ_GH],
      [δ_GH,        m_H² ]]
δ_GH = λ_GH · v_H · overlap(G, H)
```

已证明 `λ_GH = 0` 时矩阵解耦、纯胶球基向量是本征态、`m_G0²` 不因 Higgs 关闭而消失；也已证明非 `0++` 通道的门户项为零。非零混合下的本征值、连续归一化和物理谱仍待有理/实系数层。

### G5. 物理识别

最后才接质量壳、色散关系、尺度依赖和实验单位。只有完成规范不变量、复合态质量泛函和至少一个谱通道后，才可以说“模型产生胶球质量”；在此之前只能说“产生离散质量候选”。

## 4. 必须避免的三种跳步

1. `y·v` 可以给出 Yukawa 型质量，但不能单独解释纯胶子禁闭质量。
2. 三夸克 `nucleusMassIndex` 不能替代胶球复合态。
3. 单调离散 coupling 不能称为 QCD 的渐近自由；还缺色规范场、重整化尺度和 beta 函数。
