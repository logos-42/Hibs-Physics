# ProjectionPhysics — 代数涌现物理学（Lean 4 草案）

> **上游材料**：HIBS 论文（三公理隐藏空间桥接系统，刘元杰 & 徐依娜）+
> 与 Gemini 的六轮推导对话（`/Users/apple/lean/HIBS/gemini/`）。
> 本仓库: [github.com/logos-42/Hibs-Physics](https://github.com/logos-42/Hibs-Physics) ·
> HIBS 开源仓库: [github.com/logos-42/Lean_HIBS](https://github.com/logos-42/Lean_HIBS)
>
> **工程目标**：证明"物理即代数的表示"——从 HIBS 公理 (S, ⊕, ⊗) 与非单射
> 投影 π 出发，所有物理量（度规、能量、动量、质量、自旋）都是
> **Image 二次型 Q 与 Kernel 标量 K 的必然表示**，而非人为定义。
>
> English: [README.md](README.md) · 数学草案细节: [SPEC.md](SPEC.md)

## 核心主张

> **任何可观测量都只是两个对象的函数：**
> **Image**（π(S) 上的二次型 Q）与 **Kernel**（ker π 的标量不变量 κ）。
> 不存在第三种自由度。

若此 *表示完备性* 成立，则：质量 = 核的标量表示；度规 = Q 诱导的双线性形式；
动量 = 乘法流（Flow）的投影；自旋/狄拉克结构 = Q 的 Clifford 表示。
已知物理（牛顿、麦克斯韦、薛定谔、狄拉克、爱因斯坦）成为极限特例，
核空间中标准物理忽略的部分则产生全新预言（质量融化、因果指纹）。

## 已证明（编译通过，无 sorry）

```
observables_depend_only_on_image     Kernel 不可观测：π(s_im + s_ker) = π s_im
invariant_factor_through_projection  可观测量必然因子化通过投影：I = J ∘ π
left_inverse_of_injective            单射嵌入 ⟹ 存在左逆投影（HIBS 6.5 一般化）
kernel_mass_zero_on_trivial_kernel   平凡核 ⟹ 核质量为零
nontrivial_kernel_gives_internal_degree  非平凡核 ⟹ 存在内部自由度
matMul_assoc / matMul_add_right      矩阵算法：2×2 复矩阵乘法结合律/分配律（A1–A4）
sigma1_sq ... anticommute ...        自旋：Pauli 生成元平方 = I、反交换（C1–C2）
i_emerges_from_clifford              ★ (σ₁σ₂)² = -1：虚数单位从反交换涌现（C3）
sigma3_from_sigma1_sigma2            σ₃ = i·σ₁σ₂：第三生成元从前两个涌现（C4）
spinor_rep_hom                       (MN)ψ = M(Nψ)：自旋表示是同态（C5）
sigma1_sigma2_eq ... (×6)            完整乘法表：σᵢσⱼ = δᵢⱼI − iεᵢⱼₖσₖ（C6）
cVecSpace / reProj_linear            ℂ 是 2 维实向量空间；Re 是线性映射（L1–L2）
kernel_smul_closed                   ★ 核在数乘下封闭，核是子空间（L3）
rank_nullity_complex_re              ★ dim ℂ = dim ker(Re) + dim im(Re) = 1+1（L5）
polarization                         极化恒等式：2B(x,y) = Q(x+y) − Q(x) − Q(y)（L6）
projection_generates_state           ★ 投影产生状态：无状态源经投影获得状态（H1–H5）
quat_i_sq ... quat_ijk_minus_one     ★ i²=j²=k²=ijk=-1 从 Clifford 反交换涌现（Q1–Q3）
quatToMat_mul                        ★ 四元数 ⊂ Mat2 = Cℓ(3) 表示，保加法保乘法（Q5）
realImagProjection                   ★ 互补投影对 {Π_re, Π_im}：幂等+正交+完备（PA2）
kernel_mul_leaks_to_image            ★ 核质量泄露：i·i=-1 且 Re(i²)=-1≠0（PA7）
cKernelBiForm                        ★ 核上双线性形式：Q(k) = κ(k)，核张量 = 质量候选（PA8）
```

### 核心证明思路

- **C1 因子化**：可观测量"不区分同一观测值的微观态"（π s₁ = π s₂ ⟹ I s₁ = I s₂）。
  定义 J(v) := I(选一个 s 使 π s = v)，则 I = J ∘ π。**一切可观测的都是 π(s) 的函数**
  ——核只贡献标量自由度（如维度），这正是质量猜想需要的。
- **K5 左逆**：ι 单射 ⟹ 像上每个 v 有唯一原像 ⟹ 取原像即得 π 使 π ∘ ι = id。
  **投影不是假设，而是嵌入单射性的必然结果**（HIBS 定理 6.5 的一般形式）。
- **K3 Kernel 不可观测**：往态里加任意核元素，观测值不变——完备性的地基。

## 隐数主线(2026-08-06 方向)

**隐数 ≠ 复数的另一种写法**。隐数的第一性不是 i²=-1,而是**投影幂等 P²=P**(状态生成机制)。

```
复数/四元数(比较对象):             隐数(主线):
  单位元 → 乘法规则 → 旋转            潜在对象 → 映射/投影 → 状态出现
```

- **隐数空间**(H1–H5):无状态向量 = `observed = none`;投影产生状态;不同投影给不同状态;幂等投影 Π = ι∘Re;方向 = Re·1 + Im·i
- **投影代数**(PA1–PA8,主线):互补投影对(幂等/正交/完备)是状态生成机制的代数公理;复合表 = **半群**而非群(Π_re 非单射,确定性来自信息损失);**核质量泄露**(核乘法不封闭:i·i=-1 泄漏到实轴);**核张量**(核上双线性形式 Q(k)=κ(k),质量候选 m²=κ)
- **四元数**(Q1–Q7,比较对象):i²=j²=k²=ijk=-1 是 Clifford 反交换的必然表示——隐数空间若有内部乘法,必然产生非交换结构

## 草案（结构已陈述，证明为开放目标）

```
RepresentationCompleteness   I = F(Q, κ)   —— Q 半已证（C1），κ 半待核表示论
KernelRepresentation         质量 = Aut(ker π) 的唯一标量表示（m = Φ(ker π)）
KernelNullTheorem            核平凡 ⟹ 动量在零锥上 Q(p) = 0（前半已证：N1/N2）
```

## 物理论证思路（五座桥梁）

| 物理量 | 代数定义 | 论证要点 |
|---|---|---|
| 不变量 | I(ζ) 在 Aut(S) 下恒定 | 系统的核心指纹 |
| 能量 | E = I(ζ) − J(π(ζ))（信息损失） | 投影无法输出的那部分不变量 |
| 动量候选量 | P = π(Flow(ζ))（乘法链投影） | 只是定义；守恒需额外证明 `P ∘ Flow = P` |
| 质量 | m = κ(ζ_κ)（核标量不变量） | 投影无法出口到可观测像的代数残渣 |
| 相互作用 | ζ₁ ⊗ ζ₂（A2b 强制流入 R） | 代数级联与坍缩 |

## 诚实声明

1. **草案是草案**：三个 structure 是良型陈述（含全部假设），Lean 保证自洽，
   不保证成立。证明它们是研究计划本身。
2. **(1,3) 签名未被推导**：所有"推导出减号"的尝试要么走私连续时空（∂_μ）、
   要么借用质量壳条件、要么手挥。在真正证明之前，度规表示诚实地缺席。
3. **"推导出 KG/薛定谔/狄拉克"不是独立推导**：它们预设连续时空与场论框架，
   是重新表述。
4. **数字命理学已剔除**：π 幂次"匹配"粒子质量比（如 6π⁵ ≈ 1836.118）是凑数，
   不属于本仓库。

## 构建

```bash
elan override set v4.28.0
lake build            # 34 jobs, 无 error 无 sorry
.lake/build/bin/projphys
```

## 目录

```
ProjectionPhysics/
├── SPEC.md                 # 数学草案：定理清单、证明状态、诚实声明（中文）
├── README.md               # 英文详细说明
├── README.zh-CN.md         # 本文件（中文概览）
├── ProjectionPhysics.lean   # 根模块
├── Main.lean                # 可执行入口
└── ProjectionPhysics/
    ├── Definitions.lean     # 投影/核/像/信息守恒/不变量/二次型/ProjectionPair
    ├── Kernel.lean          # 核的代数性质（K1–K6，全部已证）
    ├── Completeness.lean    # 不变量因子化（已证）+ 完备性草案
    ├── Mass.lean            # 核质量（平凡核情形已证）+ 核表示草案
    ├── NullTheorem.lean     # Kernel Null 草案 + 代数核心
    ├── Bridges.lean         # 五座桥梁的代数定义
    ├── Algebra.lean         # 矩阵算法：加法群→自同态环→乘法结合律（A1–A4）
    ├── Clifford.lean        # 自旋：Pauli 反交换 + i 涌现 + 完整乘法表（C1–C6）
    ├── LinearAlgebra.lean   # 矢量/张量/kernel：向量空间公理、核子空间、
    │                        # rank-nullity（虚轴 = ker Re）、极化恒等式（L1–L6）
    ├── HiddenSpace.lean     # 隐数空间：无状态向量、Option 标签、状态生成（H1–H5）
    ├── Quaternion.lean      # 四元数（比较对象）：i²=j²=k²=ijk=-1 从 Clifford 涌现（Q1–Q7）
    ├── ProjectionAlgebra.lean # 隐数投影代数（主线）：互补投影、复合半群、
    │                          # 核质量泄露、核张量（PA1–PA8）
    ├── HiddenSpacePhysics.lean # 新离散物理桥梁：三轴、空间流、旋量阻抗质量、
    │                           # 三夸克自由度指数、路径长度时间（HSP1–HSP5）
    ├── HIBSPhysicalBridges.lean # HIBS 适配：A1–A3、Higgs-Yukawa 型质量、
    │                            # 离散 beta、质量壳/零锥契约（HIBS1–HIBS5）
    ├── HiddenOnlyHiggs.lean     # 纯隐数、无时间的静态 Higgs/Yukawa 型质量桥
    ├── HiddenHiggsFlowInterface.lean # 独立流参数接口，不等同于时间
    ├── HiddenAxisConversions.lean # H/R/I 全状态正交可逆转换标准
    ├── HiddenMassTimeEvents.lean # 质量事件计数与离散涌现时间同步
    ├── HiddenEventClocks.lean # 事件/质量事件区分、局部离散时钟与路径聚合
    ├── FlowConservation.lean # Flow 链组合律与条件式动量不变量
    └── MinimalCore.lean # ★ 最小核心：质量=自旋旋量流对空间运动的锚定
                         # （旋量阻抗）⟹ m≠0；胶球 m_G²=|a|²+|b|²+|c|²>0（MC1–MC2）
    └── SpaceLightSpeed.lean # ★ 矢量光速：光速=空间本身的等效速度（新概念）；
                             # 光子=完全随空间⟹零锚定；电子=自旋⟹锚定为正（SLS1–SLS3）
    └── DiracBridge.lean # ★ 狄拉克桥：质量项=手征耦合（DB4: γ⁰ψ=ψ⟺ψ_L=ψ_R；
                         # DB5: m=0⟹Weyl 手征对称=光子；DB6: γ 反交换）
    └── SpaceLightSpeed.lean # ★ SLS6 相对论重构：惯性系=随空间流动；
                             # 光速不变=空间流动普适（洛伦兹公式形式保持）
    └── LorentzRebuild.lean # ★ 洛伦兹重构（mathlib）：boost 保持度规 η=diag(-1,1)；
                            # γ²-γ²β²=1；快度加法；速度加法；β<1（LR1–LR5）
    └── PauliMathlib.lean # Clifford 核心的 mathlib 重写（σ²=I/反交换/i 涌现/
                          # σ₃=-iσ₁σ₂）——ext+fin_cases+ring 替代分量 omega（C1'–C4'）
    └── DiracMathlib.lean # 狄拉克桥的 mathlib 重写：4×4 γ 矩阵（γ⁰²=1/γⁱ²=-1
                          # 度规签名、反交换、质量=手征耦合）（DB1'–DB6'）
    └── MinimalCoreMathlib.lean # 最小核心的 mathlib 重写：m²=|ψ₁|²+|ψ₀|²
                                # （旋量流锚定；非零旋量⟹m>0）（MC1'–MC4'）
    └── SpaceMetric.lean # 空间流动度规（GR 重构种子）：光子随空间（dx=c·dt）
                         # ⟹dτ=0 不花时间；质量偏离⟹dτ>0；时间=偏离程度（SM1–SM6）
    └── MinimalCoreMathlib.lean # MC6' 三胶子纠缠：m_G²=m₁²+m₂²+m₃² 叠加锚定；
                                # (σ₁+σ₂+σ₃)ψ≠0 纠缠流（混沌阈值 λ≥1.5）
    └── RelativityDeviation.lean # RD1–RD7 相对论差值项：光速不变=(c−v)被分母抵消；
                                 # γ²(u)=1/(2u/c−u²/c²)；光子 u=0⟹dτ=0
    └── SphericalHarmonics.lean # SH1–SH5 胶球力=球谐函数猜想：(σ₁+σ₂+σ₃)²=3I
                                # 球对称标量；三胶子=Y_1 三分量；GR 推广=角动量→质量源
    └── SpaceGravity.lean # SG1–SG6 GR 从动量守恒推导：Gordon 度规
                          # g=[[1−v²/c²,v/c²],[v/c²,−1/c²]]；Φ=½v² 匹配弱场 GR
```

## 路线（下一步）

1. **核表示论**：有限核 Aut(ker) 的标量不变量唯一性——质量解析缺的另一半（D2）
2. **度量签名（D4）**：最薄弱环节，尚无诚实的 Minkowski 减号推导
3. **系数环升级**（ℤ[i] → ℚ[i]/ℝ）：解锁差商（D7'）、3D 旋转、连续物理
4. **多投影族**：Fin n 指标集、投影秩，连接 rank-nullity（L5/L6）

---

*Lean 4 (core, 无 mathlib) 形式化。证明手段：omega / simp / rw / ac_rfl / 经典选择。*
