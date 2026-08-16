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
> English: [README.md](README.md) · 数学草案细节: [SPEC.md](SPEC.md) ·
> **论文**: [paper/projection-physics.tex](paper/projection-physics.tex)（英文版，
> REVTeX 单栏 preprint）+ [projection-physics-zh.tex](paper/projection-physics-zh.tex)（中文版）；
> 两版均已加 §8 探索汇总（自旋涌现/双缝谐波/分形 KBC/胶球耦合）。
> **许可证**: [MIT](LICENSE)

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

## 近期 QFTFlow 探索线（2026-08-16）

活跃探索线位于 `ProjectionPhysics/Explorations/QFTFlow.lean`
（4146 jobs，零 sorry），全部形式化 + 数值验证（N1–N28 机器精度）：

- **扭量统一（GQ/GQN/GQM/GQS）**：质量² = |detₙ|² = Σ|子式|²——质量 = 辛纠缠体积
  （Cauchy-Binet 链，一般 Finset 版，n=2 任意 m 完整）
- **信息 = 辛体积（GQC1）**：酉传输（流动传播）保持 det(AA†)——流动中信息守恒
- **因果 = 格点局域（GQC2）**：带宽 ≤ 1 ⟹ t 步带宽 ≤ t——格点流动涌现光锥
- **等效超光速 = 几何（GQC3）**：倾斜光锥——流动拖曳使等效速度 1+v_flow > c，
  而信号局部仍 ≤ c（Alcubierre/Painlevé–Gullstrand 结构）
- **流动动量与四力（GQF）**：p = m(C−v)；d/dt p = (dm)C + m(dC) − (dm)v − m(dv)
  ——电场/核力/磁场/引力四通道（莱布尼茨法则）
- **光子 = 激发电子螺旋（GQP）**：模型 B 双螺旋对称 ⟹ 环向抵消 ⟹ 无质量；光子随流
- **★ 匹配：E = ħω = h·f = 每圈角动量 × 每秒圈数（GQR）**：ħ 重释为每弧度角动量
  （可数几何量）；圈数 = 频率（可数）。相对误差 0
- **★ 圆周 = 波长（GQR4-6）**：h 与 ħ 的 2π = 螺旋截面圆周。r = λ/2π（约化波长）⟹
  2πr = λ（一圈 = 一个波长）⟹ ħ = r·p（角动量 = 半径×动量）⟹ **德布罗意 p = h/λ 与
  普朗克-爱因斯坦 E = pc = hf 从螺旋几何涌现**。真实常数代入：ħ = r·p 复现实测 ħ
  （相对误差 6e-10，浮点级）；E 误差 0。诚实：r = λ/2π 是几何选择（来源未知）、
  ħ = rp 是经典恒等——推导链已闭合，第一性推导未达成
- **胶球/夸克数条数（N28）**：N=3 方向 → 3 色 → 3 胶球锚定——同一"3"贯穿
  空间/色/胶球；8 胶子 = 2³ = dim Cℓ(6)。夸克质量（2.2 MeV → 173 GeV）**无**条数规律
  （QCD 自由参数，诚实）

诚实状态：以上全部是代数恒等 + 解释（解释层）；尚无新的可证伪预言。
第二输入缺口（e、ℏ、M₀、G 仍为未量化输入）未变；从螺旋几何推导 ℏ 是开放的下一步。

## 诚实声明

1. **草案是草案**：三个 structure 是良型陈述（含全部假设），Lean 保证自洽，
   不保证成立。证明它们是研究计划本身。
2. **(1,3) 签名未被推导**：所有"推导出减号"的尝试要么走私连续时空（∂_μ）、
   要么借用质量壳条件、要么手挥。在真正证明之前，度规表示诚实地缺席。
3. **"推导出 KG/薛定谔/狄拉克"不是独立推导**：它们预设连续时空与场论框架，
   是重新表述。
4. **数字命理学已剔除**：π 幂次"匹配"粒子质量比（如 6π⁵ ≈ 1836.118）是凑数，
   不属于本仓库。

## 构建与验证

```bash
lake build                  # ~4140 jobs，无 error，零 sorry/admit
make test                   # 统一门禁：lake build + 8 个验证脚本重跑
                            #   + 回归锚点断言（报告在 artifacts/ 各目录）
make fast                   # 门禁（跳过数值脚本重跑，只读既有报告）
python3 scripts/wiki_check.py   # wiki 完整性（链接 + frontmatter）
```

## 目录

```text
ProjectionPhysics/
├── LICENSE                 # MIT 开源协议
├── SPEC.md                 # 数学草案：定理清单、证明状态、诚实声明（中文）
├── README.md               # 英文详细说明
├── README.zh-CN.md         # 本文件（中文概览）
├── Makefile                # 统一门禁入口（make test → scripts/verify_all.py）
├── paper/                  # 论文（REVTeX 4.2，单栏 preprint，中英双版）
│   ├── projection-physics.tex    # 英文版（含 §8 探索汇总，tectonic 编译 PDF）
│   ├── projection-physics-zh.tex # 中文版（内容等同）
│   └── projection-physics.bib    # 参考文献（18 条全真实）
├── scripts/                # 验证与可视化（8 个 verify_*.py 进门禁）
│   ├── verify_all.py            # 统一门禁（lake build + 零 sorry 扫描 + 脚本 + 断言）
│   ├── verify_maxwell_space.py  # 电磁 = 空间场 C 的运动学（MS1–MS5）
│   ├── verify_spacefield3d.py   # 3D 向量微积分：div(curl C)=0 自动（SF1–SF5）
│   ├── verify_spin_from_space.py# 自旋 = 三方向结构涌现（SFS1–SFS5）
│   ├── verify_fractal_flow.py   # 分形宇宙：KBC 空洞 + Hubble 悖论（δ* = −0.25）
│   ├── verify_double_slit.py    # 双缝 = 空间螺旋谐波干涉（DS1–DS4）
│   ├── verify_glueball_coupling.py # 胶球三方向耦合 + 质量化（GC1–GC4）
│   ├── verify_maxwell_flow.py   # 麦克斯韦 × 流动公设（MF1–MF6, P1–P4）
│   ├── verify_entanglement_helix.py # CHSH 局域界（EH1–EH4）
│   ├── verify_blackhole_wormhole.py # Gordon 黑洞/虫洞（BH1–WH1）
│   └── wiki_check.py            # wiki 完整性检查
├── ProjectionPhysics.lean   # 根模块
├── Main.lean                # 可执行入口
└── ProjectionPhysics/                    # 主线 + 探索（见英文 README 正文）
    ├── SpaceLightSpeed.lean     # ★ 主线：矢量光速——c=空间本身的等效速度；光子随空间⟹m=0；电子自旋⟹m>0（SLS1–SLS6）
    ├── SpaceMetric.lean         # ★ 主线：空间流动度规——dτ²=dt²−dx²/c²；光子 dx=c·dt⟹dτ=0；质量=偏离⟹dτ>0（SM1–SM6）
    ├── SpaceGravity.lean        # ★ 主线：Gordon 度规——g=[[1−v²/c²,v/c²],[v/c²,−1/c²]]；Φ=½v² 匹配弱场 GR（SG1–SG11）
    ├── RelativityDeviation.lean # 主线：差值相对论——(c−v)/(1−cv/c²)=c；γ²(u)=1/(2u/c−u²/c²)（RD1–RD7）
    ├── LorentzRebuild.lean      # 主线（mathlib）：洛伦兹重构——boost 保持度规/快度加法/速度加法/β<1（LR1–LR5）
    ├── PauliMathlib.lean        # 主线（mathlib）：Clifford 重写（C1'–C4'）
    ├── DiracMathlib.lean        # 主线（mathlib）：狄拉克桥——γ⁰²=1、γⁱ²=−1；质量=手征耦合（DB1'–DB6'）
    ├── MinimalCoreMathlib.lean  # 主线（mathlib）：质量=锚定——m²=|ψ₁|²+|ψ₀|²；非零旋量⟹m>0（MC1'–MC6'）
    ├── Explorations/            # 探索线（2026-08-14 后活跃）：新方向结果
    │   ├── EntanglementHelix.lean    # 双螺旋纠缠局域界（EH1–EH4）
    │   ├── BlackHoleWormhole.lean    # Gordon 黑洞/虫洞（BH1–WH1）
    │   ├── MaxwellFlow.lean          # 麦克斯韦 × 流动公设（MF1–MF6, PH1–PH2）
    │   ├── MaxwellSpace.lean         # 电磁 = 空间场运动学（MS1–MS5）
    │   ├── SpaceField3D.lean         # 3D 向量微积分（SF1–SF5）
    │   ├── SpinFromSpace.lean        # 自旋 = 三方向涌现（SFS1–SFS5）
    │   ├── DoubleSlit.lean           # 双缝 = 螺旋谐波干涉（DS1–DS4）
    │   ├── GlueballCoupling.lean     # 胶球三方向耦合（GC1–GC4）
    │   ├── SpinStatistics.lean       # 自旋统计硬约束（SS1–SS8）
    │   ├── CliffordSix.lean          # Cℓ(6) 8 维表示（CS1–CS3）
    │   ├── ColorOctetMathlib.lean    # 3⊗3=8⊕1 无迹分解（CM1–CM3）
    │   ├── SphericalHarmonics.lean   # 胶球力=球谐（SH1–SH5）
    │   ├── SU3Bridge.lean            # SU(3) 循环子群
    │   └── GlueballBridge.lean       # SU(3) 色作用、胶球质量
    └── Archive/                 # 弃用（08-06 前隐数路线 + core 双轨）：Definitions/Kernel/Completeness/
                                # Mass/NullTheorem/Bridges/Algebra/Clifford/LinearAlgebra/Differential/
                                # SymmetryBreaking/HiddenSpace/Quaternion/ProjectionAlgebra/HiddenSpacePhysics/
                                # HIBSPhysicalBridges/HiddenOnlyHiggs/HiddenHiggsFlowInterface/
                                # HiddenAxisConversions/HiddenMassTimeEvents/HiddenEventClocks/
                                # FlowConservation/DiracBridge/MinimalCore
```

## 路线（下一步）

1. **核表示论**：有限核 Aut(ker) 的标量不变量唯一性——质量解析缺的另一半（D2）
2. **度量签名（D4）**：最薄弱环节，尚无诚实的 Minkowski 减号推导
3. **"第二输入"（最深开放问题）**：ℏ、e、M₀ 的数值与电子对二维表示的选择——仍是输入而非结论（见论文 §9）
4. **连续 3D 微积分**：离散 3D curl/div 恒等（SF1–SF5）已形式化；连续版本与连续性仍开放
5. **摆脱重释的可检验出口**：非均匀流动 ⟹ 洛伦兹破缺；格点检验胶球 √N·M₀ 高通道（n=4,5,6）

---

*Lean 4 (mathlib) 形式化。证明手段：omega / simp / rw / ac_rfl / ring / nlinarith。*
