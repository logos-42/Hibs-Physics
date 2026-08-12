# ProjectionPhysics — 数学草案 SPEC

> 来源：HIBS 论文（刘元杰、徐依娜）+ 与 Gemini 的六轮推导对话（`../HIBS/gemini/`）
> 工程目标：证明"物理即代数的表示"——所有物理量（度规、能量、动量、质量、自旋）
> 是投影 π 与核 ker π 的必然表示，而非人为定义。

## 状态图例

- ✅ **已证**：Lean 4 编译通过的定理（见对应模块）
- 📋 **草案**：结构已陈述（含全部假设），证明为开放目标
- ❌ **待定**：概念尚需精确化

## 1. 基本设定

隐藏空间 S（带加法 ⊕ 与乘法 ⊗），观测空间 V，非单射投影 π : S → V。

- 核：`KernelOf π = { s : S // π s = 0 }`（Definitions.lean）
- 像：`ImageOf π = { v : V // ∃ s, π s = v }`
- 信息守恒（等变）：`π(σ_S s) = σ_V (π s)`（InfoPreserving）
- 可观测量：在观测等价类上取常值 `IsObservable π I`

## 2. 已证明定理（✅ Kernel.lean / Completeness.lean / Mass.lean）

| 编号 | 定理 | 内容 | 物理意义 |
|---|---|---|---|
| K1 | `kernel_add_closed` | π 保加法 ⟹ 核加法封闭 | 核是子空间 |
| K2 | `kernel_contains_zero` | π0 = 0 ⟹ 0 ∈ 核 | 核非空 |
| K3 | `observables_depend_only_on_image` | π(s_im + s_ker) = π s_im | **Kernel 不可观测**：完备性的地基 |
| K4 | `nontrivial_kernel_gives_internal_degree` | 非平凡核 ⟹ 核内 ∃ 两个不同元素 | 核有内部自由度（Kernel Null 论证第一步） |
| K5 | `left_inverse_of_injective` | 单射嵌入 ⟹ ∃ 左逆投影 | 投影的存在性来自嵌入单射（HIBS 定理 6.5 一般化） |
| K6 | `pair_embed_injective` | ProjectionPair ⟹ 嵌入单射 | 与 K5 对偶 |
| C1 | `invariant_factor_through_projection` | 可观测量 I = J ∘ π（因子化） | **"Q 来自 Image"的精确内容** |
| C2 | `invariant_factor_iff` | 观测等价不变 ⟺ 通过 π 因子化 | 完备性等价刻画 |
| C3 | `factor_preserves_add` | I 保加法 ⟹ J 保加法（像上态射） | 结构保持 |
| M1 | `kernel_mass_zero_on_trivial_kernel` | 平凡核 ⟹ 核质量可归一化为零 | **Kernel Null 第一段** |
| N1 | `trivial_kernel_iff_no_internal_degree` | 核平凡 ⟺ 无内部自由度 | 定义等价 |
| N2 | `no_internal_degree_implies_no_kernel_mass` | 无内部自由度 ⟹ 无核质量 | M1 的别名 |
| B1 | `infoLoss_zero_on_observable` | I = J∘π ⟹ 纯可观测态信息损失为零 | 信息损失定义一致性 |
| A1 | `comp_additive` | 保加法映射复合仍保加法 | 自同态环封闭（A2a ⟹ End(S) 是环） |
| A2 | `comp_assoc` | 函数复合结合 | 一切矩阵乘法结合律之源 |
| A3 | `matMul_assoc` | 2×2 复矩阵乘法结合律 (MN)P = M(NP) | **矩阵算法从复合涌现** |
| A4 | `matMul_add_right` | 矩阵乘法分配律 M(N+K) = MN+MK | 矩阵算法完整 |
| C1 | `sigma1_sq`/`sigma2_sq`/`sigma3_sq` | σᵢ² = I | Clifford 生成元平方 = 度规 |
| C2 | `sigma1_sigma2_anticommute` 等 | σᵢσⱼ + σⱼσᵢ = 0 (i≠j) | **Clifford 反交换关系** |
| C3 | `i_emerges_from_clifford` | (σ₁σ₂)² = −1 | ★ **虚数单位从反交换涌现**（呼应 HIBS：ℂ 非基本） |
| C4 | `sigma3_from_sigma1_sigma2` | σ₃ = i·σ₁σ₂ | 第三生成元从前两个涌现 |
| C5 | `spinor_rep_hom` | (MN)ψ = M(Nψ) | 旋量表示是同态（自旋 = 表示） |
| C6 | `sigma1_sigma2_eq` … `sigma3_sigma2_eq` (×6) | σᵢσⱼ = δᵢⱼI − iεᵢⱼₖσₖ 完整乘法表 | 9 个乘积全部确定 |
| L1 | `VecSpace` 结构 + `cVecSpace`/`intVecSpace` | 向量空间公理；ℂ 是 2 维实向量空间、Int 是 1 维 | 隐数空间的矢量结构 |
| L2 | `reProj_linear` | Re : ℂ → Int 保加法保数乘 | 线性映射（HIBS f : S → R） |
| L3 | `kernel_smul_closed` / `kernel_is_subspace` | 核在数乘下封闭；核是子空间 | 补 K1 的缺 |
| L4 | `complexBasisInst` / `kerReBasisInst` / `imReBasisInst` | ℂ 的基 {1,i}；ker(Re) 的基 {i}；im(Re) 的基 {1} | 张成 + 线性无关 |
| L5 | `rank_nullity_complex_re` | **dim ℂ = dim ker(Re) + dim im(Re) = 1+1** | ★ **rank-nullity 实例：虚轴 iR 是实部投影的核**（HIBS A3 的 iR） |
| L6 | `polarization` / `quad_zero` | 2B(x,y) = Q(x+y) − Q(x) − Q(y)；Q(0)=0 | ★ 极化恒等式：度规从二次型涌现（Metric Representation 心脏） |
| L7 | `cOrthogonalDecomp` / `cOrthogonalDecomp_unique` | z = Re(z)·1 + Im(z)·i，分解唯一 | ℂ 的正交分解（可观测 + 核） |
| L8 | `completeness_complex` | **\|z\|² = Re(z)² + Im(z)² = Q(π z) + κ(ζ_κ z)** | ★ **范数分解：信息 = Image 二次型 + Kernel 二次型，无第三自由度** |
| L9 | `completenessComplex` | RepresentationCompleteness 的 ℂ 实例（**全部字段已证**） | ★ 草案 D1 实例化 |
| L10 | `kernelInv_zero_of_zero` | 核元素为零 ⟹ κ = 0 | 核质量归零（ℂ） |
| E1 | `matTr_add` | tr(M+N) = tr M + tr N | 散度（迹）是线性标量函数 |
| E2 | `matTr_neg`/`matTr_zero`/`matTr_one` | tr(−M)=−tr M；tr 0 = 0；tr I = 1+1 | 迹的奇偶性；tr(I) = 表示维数 |
| E3 | `matTr_transpose` | tr(Mᵀ) = tr M | 迹对转置不变（对角线不动） |
| E4 | `matTr_skew_zero` | **tr(M − Mᵀ) = 0** | ★ **散度∘旋度 = 0**：∇·(∇×A)=0 的代数种子 |
| E5 | `skew_antisymmetric` | (M−Mᵀ)ᵀ = −(M−Mᵀ) | ★ 旋度反对称（楔积空间元素） |
| E6 | `sym_skew_decomposition` | (M+Mᵀ)+(M−Mᵀ) = M+M | 对称/反对称分解（无除法 Cartan 分解） |
| E7 | `matTr_mul_comm` | **tr(MN) = tr(NM)** | ★ 迹的循环性（信息流守恒的代数形状） |
| E8 | `matTr_scalar` | tr(z·M) = z·tr M | 散度是系数环上的标量 |
| E9 | `linear_map_difference_quotient` | **L(s+h) − L(s) = L h** | ★ **导数 = 线性算子本身**（差商与位置无关） |
| E10 | `slope_difference_quotient` | (π∘L)(s+h) − (π∘L)s = (π∘L) h | 斜率 = π∘L 的差商形式（A1 复合封闭） |
| E11 | `pauli_trace_zero`（+ σᵢ×3） | tr σᵢ = 0 | 自旋无迹（旋量流无散） |
| E12 | `sigma2_skewsymmetric`（+ σ₁σ₃ 对称） | σ₂ᵀ = −σ₂ | 自旋的旋转部分 = 旋度生成元 |
| E13 | `scalar2_mul` | matMul (scalar2 z) (scalar2 w) = scalar2 (z·w) | 标量嵌入保乘法（斜率 = L(1)·h 倍数形式的载体） |
| E14 | `scalar2_commute` | matMul (scalar2 z) M = matMul M (scalar2 z) | 标量层是中心（标量 = 方向无关的量） |
| E15 | `mul_hom_comp` | 保乘法映射的复合仍保乘法 | A1 的乘法孪生版（代数同态封闭于复合） |
| E16 | `left_mul_comp` | (h ↦ A·(B·h)) = (h ↦ (A·B)·h) | A3 结合律 ⟹ Flow 线性化是左乘（差商化简 (a·h)·h⁻¹ = a 的伏笔） |
| H1 | `projection_generates_state` / `state_generation` | 无状态源经投影获得状态（状态 = 观测值 π(s)） | **"投影产生状态"的形式化**（无状态 = Option none，有状态 = some v） |
| H2 | `state_consistency` / `projected_consistent` | 标签 Some v ⟹ π(source) = v | 状态标签是事实，不是装饰 |
| H3 | `distinct_projections_distinct_states` + `re_im_proj_distinguish` + `cI_has_two_states` | π₁s ≠ π₂s ⟹ 状态不同（Re vs Im 在 cI 上区分：0 vs 1） | **状态由投影决定**，非源元素的内在属性 |
| H4 | `hiddenReProj_idempotent` / `hiddenReProj_linear` / `hiddenReProj_kernel_iff` | Π = ι∘Re 幂等 + 线性；ker Π = 虚轴 | **幂等投影 = 观测塌缩**（观测后再观测不变） |
| H5 | `direction_emerges_from_projection` | z = Re(z)·1 + Im(z)·i | 方向涌现（复述 L7 正交分解） |
| Q1 | `quat_i_sq`/`quat_j_sq`/`quat_k_sq` | i² = j² = k² = -1 | 四元数单位平方 = -1（C3 的 i 涌现的推广） |
| Q2 | `quat_ijk_minus_one` / `iSigmas_ijk` / `triple_product_square` | ijk = -1；(iσ₁)(iσ₂)(iσ₃) = -1；(σ₁σ₂σ₃)² = -1 | ★ **三生成元积 = -1 从反交换涌现**（"隐数单元 a·b·c = -1"已证） |
| Q3 | `quat_ij_ne_ji` / `iSigma1_iSigma2_ne_comm` | ij = k ≠ -k = ji | ★ **非交换：隐数代数必然非交换**（与 ℂ 的本质区别） |
| Q4 | `quat_mul_assoc` | (qp)r = q(pr) | ℍ 是结合环 |
| Q5 | `quatToMat_add`/`quatToMat_mul`/`quatToMat_i/j/k` | Φ 保加法保乘法；Φ(i) = iσ₁ | ★ **四元数 ⊂ Mat2 = Cℓ(3) 表示**（i²=-1 的矩阵版） |
| Q6 | `cToQuat_mul` | 复数乘法 ↔ 四元数乘法 | ℂ 是 ℍ 的子环（扩展不丢结构） |
| Q7 | `quatHiddenUnit`/`cliffordHiddenUnit` | HiddenUnit 双实例（ℍ 环 / Mat2 矩阵） | ★ **"隐数单元" = 反交换生成元的必然表示，不是新公理** |
| PA1 | `IsProjection` + `comp_of_commuting_projections_is_projection` | 投影 = 幂等自映射 P²=P；交换投影的复合仍是投影 | ★ **投影复合成为变换的代数前提**（正交投影族自动满足） |
| PA2 | `ComplementaryProjection` + `realImagProjection` | 互补投影对（幂等/正交/完备），ℂ 实例 {Π_re, Π_im} | ★ **状态生成机制的代数公理**：元素 = 两互补观测方向之和 |
| PA3 | `hiddenImProj_idempotent` + `comp_table_*` + `projection_composition_semigroup` | 复合表 5 项全确定；{Π_re, Π_im, 0} 在复合下封闭 | 变换复合封闭（状态生成可迭代） |
| PA4 | `hiddenImProj_kernel_iff` / `hproj_re_image` | ker Π_im = 实轴；im Π_re = 实轴 | 可观测层 / 不可观测层分层 |
| PA5 | `hproj_re_not_injective` / `hproj_re_not_bijective` | **Π_re 非单射（0 与 cI 同像 0）** | ★ **投影代数生成半群而非群**；确定性来自信息损失（K3 推论） |
| PA6 | `pvm_skeleton` | 幂等 + 正交 + 完备 = 投影值分解 | ★ **量子测量（PVM）的代数骨架**，无概率公理 |
| PA7 | `cI_sq_neg_one` + `kernelLeak`/`kernelLeak_i` + `kernel_mul_leaks_to_image` + `kernel_pair_mul_leaks` + `leak_product_in_image` | **i² = -1 且 Re(i²) = -1 ≠ 0：核乘法不封闭** | ★ **核质量泄露**：核是加法子空间（K1）但非乘法理想，"Goldstone 被吃掉"的代数原型 |
| PA8 | `cKernelBiForm` + `kernelBiForm_quad`/`kernelBiForm_quad_kernel`/`kernelBiForm_unit_norm`/`kernelBiForm_nondegenerate` | **核上双线性形式 B(x,y) = Im x·Im y**；二次型 Q(k) = κ(k) = kernelInvC；核上非退化 | ★ **核张量化**：ker π 上的 (0,2) 张量——质量候选 m² = κ(ζ_κ) 的第一个物理连接 |
| MC1 | `spin_flow_anchor_mass_pos_of_spinor_nonzero` + `spin_flow_anchor_mass_zero_of_zero_spinor` | **内部运动状态 s（自旋 = Clifford σψ 旋量流）→ 空间运动 F → 质量 m := 锚定效果（旋量流分量范数）→ 自旋非零 ⟹ m > 0；零旋量 ⟹ m = 0** | ★ **最小核心命题（旋量流版）**：质量=物质抵抗空间本身运动的锚定效果，自旋本身就是运动状态（`MinimalCore.lean` MC1 + MC1h 隐数版） |
| MC2 | `triplet_glueball_mass_squared_formula` + `triplet_glueball_mass_squared_positive_of_any_nonzero` + `triplet_unit_mode_mass_squared_is_three` | **G=(a,b,c), color profile=(1,1,1), m_G²=|a|²+|b|²+|c|²；至少一个非零 ⟹ m_G² > 0；a=b=c=1 ⟹ m_G²=3** | ★ **胶球最小版**：三胶子内部运动状态色单态；三方向假设 √3·M₀ 精确匹配格点 0++（`MinimalCore.lean`） |
| SLS1 | `light_speed_is_universal_space_property` + `tri_directional_space_has_universal_speed` | **空间速度矢量（三方向）模 = 普适常数 c²；任何空间点等效速度模相同** | ★ **矢量光速新概念**：光速 = 空间本身的等效速度（非空间内物质速度）；三方向空间运动（`SpaceLightSpeed.lean`） |
| SLS2 | `anchor_mass_zero_of_photon` | **无内部运动 + 完全随空间运动 ⟹ 零锚定 ⟹ 零质量** | 光子 = 完全随空间运动（去掉垂直方向向量）（`SpaceLightSpeed.lean`） |
| SLS3 | `anchor_mass_positive_of_internal_motion` + `anchor_mass_positive_of_relative_motion` | **自旋非零 ⟹ 锚定为正；偏离空间运动也产生锚定** | 电子 = 自旋（法向旋转）⟹ 有质量（`SpaceLightSpeed.lean`） |
| SLS4 | `planar_directions_anticommute` + `normal_direction_emerges_from_plane` + `planar_motion_products_give_i` + `x_motion_spin_is_sigma1` + `x_motion_spin_flow_nonzero` | **σ₁σ₂+σ₂σ₁=0（平面圆周运动代数）；σ₃=i·σ₁σ₂（★法向量从平面涌现）；(σ₁σ₂)²=-1（i 涌现）；x 运动投影=σ₁；空间运动产生非零旋量流** | ★ **波法向量旋量（思路 B 落地）**：空间运动方向 → 自旋生成元 → 等效旋转角动量（`SpaceLightSpeed.lean`） |
| SLS5 | `three_direction_three_glueball_bridge` | **空间三方向运动模² = 3 ∧ 三胶子质量平方 = 3** | ★ **三方向 ↔ 三胶子**：空间三方向 = 色三方向 = 三胶子，"三"是同一个三（`SpaceLightSpeed.lean`） |
| DB4 | `mass_equation_couples_chiralities` | **(γ⁰−1)ψ = 0 ⟺ ψ_L = ψ_R** | ★ **质量解 = 手征耦合**：静止狄拉克方程要求左右手相等（`DiracBridge.lean`） |
| DB5 | `zero_mass_has_chiral_asymmetry` | **∃ψ, γ⁰ψ ≠ ψ（手征不对称解存在）** | m=0 ⟹ 手征对称（Weyl）= 光子（`DiracBridge.lean`） |
| DB6 | `gamma0_gamma1_anticommute` + `gamma0_sq` | **γ⁰γ¹+γ¹γ⁰ = 0；γ⁰² = 1** | Clifford 关系在 4×4 狄拉克层（`DiracBridge.lean`） |
| SLS6 | `IsInertialFrame` + `light_speed_invariance_comoving_observer` + `IsUniformSpaceFlow` | **惯性系 = 随空间流动；随空间观测者测光速恒定（光速不变=空间流动普适）；洛伦兹不变性 = 空间流动均匀** | ★ **相对论重构**：公式形式不变、解释层全变——c=空间流动/惯性=随空间/引力=流动非均匀（`SpaceLightSpeed.lean`） |
| LR1–LR5 | `boost_is_lorentz` + `gamma_sq_minus_beta_sq` + `boost_mul_boost` + `rapidity_add_velocity_add` + `finite_rapidity_never_reaches_light` | **boost(θ) 保持 η=diag(−1,1)；γ²−γ²β²=1；快度加法；速度加法；β<1** | ★ **洛伦兹重构（mathlib）**：新假设下洛伦兹变换形式与标准一致，解释层改变（β=偏离空间流动）（`LorentzRebuild.lean`） |
| C1'–C4' | `sigma1_sq`/`sigma2_sq`/`sigma3_sq` + `sigma1_sigma2_anticommute` + `sigma12_sq` + `sigma3_from_sigma12` | **σ²=I；σ₁σ₂+σ₂σ₁=0；(σ₁σ₂)²=−1；σ₃=−iσ₁σ₂** | Clifford 核心的 mathlib 重写（对照版，`ext`+`fin_cases`+`ring`）（`PauliMathlib.lean`） |

## 2.5 推导链：公理 → 矩阵 / 张量 / 自旋（已形式化）

```
A2a (⊕ 封闭) ──► S 加法群 ──► End(S) 环（A1: 复合封闭；A2: 复合结合）
   ──► 选基 ⟹ 矩阵表示 ──► 矩阵乘法结合律/分配律（A3, A4 已证）
A2b (⊗ : S×S → R) ──► 双线性形式（张量原语）──► 二次型 Q
   ──► Clifford 代数 Cℓ(Q)（C1: σ²=I；C2: 反交换）
   ──► 旋量空间（C5: 表示同态）──► 自旋
   ──► ★ (σ₁σ₂)² = −1（C3）：i 是表示对象，不是公理
   ──► σ₃ = i·σ₁σ₂（C4）：第三方向从前两个涌现（手性的代数雏形）
   ──► 转置/迹/反对称（Differential.lean E1–E12）──► 散度 = tr(L)、旋度 = (L−Lᵀ)（代数种子）
```

## 3. 草案声明（📋 待证明）

### D1. Representation Completeness Theorem
```
设 (S, ⊕, ⊗) 满足 HIBS 公理 A1–A3，π : S → V 非单射信息守恒投影。
则任意可观测量 I 唯一分解为：
    I(s) = F( Q(π(s)), κ(ζ_κ(s)) )
Q = 像空间二次型（Image 不变量）；κ = 核标量不变量（Kernel 不变量）。
完备性：不存在独立于 {Q, κ} 的第三自由度。
```
**现状**：
- ✅ Q 半已证（C1：I = J∘π）+ ℂ 实例 `observable_factors_through_re`
- ✅ **ℂ 实例化**：`completenessComplex`（全部字段已证）+ 范数分解 `completeness_complex`（|z|² = Re² + Im²，Q+κ 无第三项）
- ⚠️ 注意（诚实修正）：任意可观测 I 无法用"平方 Q"表示（I z = z.re 丢符号）——完备性的可证部分是**因子化 I = J∘π**；"Q+κ 分解"以范数分解定理（L8）为具体形式，κ 的唯一性（D2）仍开放
- **Lean 位置**：`Completeness.RepresentationCompleteness` + `LinearAlgebra.completenessComplex`

### D2. Kernel Representation Theorem
```
核 ker π 拥有内部代数结构；Aut(ker π) 上的标量表示唯一。
满足 (a) Image 不可见 (b) Aut 不变 (c) 与投影秩无关 的标量只能依赖 dim(ker π)。
质量 m = Φ(dim ker π)，不是定义。
```
**现状**：M1（平凡核 ⟹ 质量零）已证；唯一性需核上表示论。
**Lean 位置**：`Mass.KernelRepresentation`

### D3. Kernel Null Theorem
```
核容量 C_κ → 0（核平凡）⟹ 投影后动量 p 满足 Q(p) = 0（零锥上）。
论证链：无内部自由度 ⟹ 无静止参考系 ⟹ 唯一路径 Q(p) = 0 ⟹ "光速"成为推论。
```
**现状**：N1/N2（无内部自由度 ⟹ 无核质量）已证；"Q(p)=0"需 Metric
Representation（动量 Q 的定义与色散关系推导）完成后才能证。
**Lean 位置**：`NullTheorem.KernelNullTheorem`

### D4. Metric Representation（五座桥梁之一）
```
任何投影 π 诱导唯一的双线性形式 B(u,v)（由二次型 Q 经极化恒等式给出）。
Minkowski 签名 (1,3) 是 B 的符号差结论，不是公理。
```
**现状**：完全未证。极化恒等式（Jordan–von Neumann）在 core Lean 可形式化，
但"签名 (1,3)"需要额外的结构假设——**这是全工程最薄弱、最关键的一环**。

### D5. Flow Representation
```
Flow F := 乘法链 ⊗ 的连续施加；动量 P := π(F(ζ))。
动量守恒来自乘法结合律（非 Noether 定理）。
```
**现状**：`Bridges.momentumOf` 已定义；守恒性未证（需要 ⊗ 结合性假设）。

### D6. Clifford Emergence
```
投影产生二次型 ⟹ 存在唯一 Clifford 表示；γ 矩阵、Dirac 是表示而非基本对象。
```
**现状**：
- ✅ **3 维实例化**：`pauliClifford : CliffordEmergence 3`（Pauli 生成元，反交换 + 平方全部验证，Fin 3 全情况分解）
- ✅ C1–C6：σᵢ²=I、反交换、(σ₁σ₂)²=−1、σ₃=iσ₁σ₂、完整乘法表、旋量表示同态
- 开放：一般维数 Cℓ(p,q) 的表示论；Weyl 手性分解（A3 的 √→iR 需要复结构）
- **Lean 位置**：`Clifford.pauliClifford`

### D7. Differential Emergence（导数/斜率/散度/旋度的代数身份）
```
设 F : S → S 是流通算子（Flow），线性化为 L ∈ End(S)（A1/A2 ⟹ End(S) 是环）。
则向量微积分算子是 End(S) 的表示：
    斜率 := π ∘ L          （线性化在观测方向上的投影）
    散度 := tr(L)          （线性化的迹：核方向的信息流）
    旋度 := (L − Lᵀ)/2     （线性化的反对称部分：Clifford 楔积空间的元素）
守恒律（碰撞不变量守恒） := tr(π∘L) 沿核方向的退化（DengYu 连续方程）
```
**现状（2026-08-04 编译 + 代数种子形式化）**：
- ✅ End(S) 环结构已证（A1 复合封闭 + A2 复合结合）——导数"居住"的环存在
- ✅ Clifford 反交换/楔结构已证（C2：σᵢσⱼ + σⱼσᵢ = 0）——**旋度的代数雏形已存在**（Cℓ ⊃ 外代数）
- ✅ **代数种子已形式化（Differential.lean，E1–E16）**：迹（散度）已定义并证线性性/循环性/标量性；转置已定义（对合/保加法/反同态 (MN)ᵀ=NᵀMᵀ）；**tr(M−Mᵀ)=0**（散度∘旋度=0）；**(M−Mᵀ)ᵀ=−(M−Mᵀ)**（旋度反对称）；对称/反对称分解；**差商定理 L(s+h)−L(s)=L(h)**（导数=线性算子本身）；斜率=π∘L 差商形式；自旋无迹 tr σᵢ=0；σ₂ 反对称（旋度生成元）；标量嵌入保乘法/中心性（E13/E14）；保乘法复合封闭（E15）；左乘复合=左乘乘积（E16）
- ⚠️ **核心缺口（诚实，2026-08-04 修正）**：公理无连续性、且**无逆元**（除法 = 乘以逆元，归约路径通着；但 ℂ = Int×Int 是 ℤ[i]-型环，全仓无 `Inv`/`Field` 实例，ℤ[i] 非域 ⟹ 差商 `(f(s₁)⊖f(s₂)) ⊗ (s₁⊖s₂)⁻¹` 无定义）。迹/转置已在 Mat2 上形式化，**但带除法的差商仍无定义**——给 S 补上逆元后差商/斜率在隐数空间内即有意义
- 📋 **D7' 差商草案结构（Differential.lean `DifferenceQuotient`）**：把"逆元登场"显式化——假设 L 保乘法 + 保单位 + 非零元有乘法逆元，结论（开放目标）为差商方向无关 `(L h)·h⁻¹ = L 1`。与 E9 的"位置无关"（加法层）互补，这是"方向无关"（乘法层）。`inv_existence` 在 ℤ[i] 下不可满足，实例化需升级系数环到 ℚ[i]/ℝ
- ❌ 连续版本（∇·、∇×、∂_μ）需 D4 度量 + 光滑性假设，与 §5 的 ∂_μ 走私警告同级
- **物理含义**：散度 = 核方向的信息流（∝ 信息损失/能量，见 Bridges.infoLoss）；旋度 = 不可观测的环形核运动（K4 内部自由度的微分版）；斜率 = 可观测演化比率（动量 P = π∘Flow 的差分版本）
- **推导结论**：线性映射的差商恒等于它自己 ⟹ 当前框架内"导数 = 线性算子本身"（平凡的，已证 E9/E10）；非线性结构出现前，散度/旋度无法脱离 End(S) 环走得更远
- **Lean 位置**：`Differential.lean`（E1–E12 已证）；连续版本仍无（依赖 D5 ⊗ 结合性 + D4 度量）

### D8. Symmetry Breaking（自发对称性破缺）

```
对称性 = 核平移：ζ ↦ ζ ⊕ κ（κ ∈ ker π），观测不变（K3 已证）。
势经投影因子化 V(ζ) := Ṽ(π ζ) ⟹ 自动核平移不变（规律对称）。
真空流形 = 整条核纤维 π⁻¹(v₀) = v₀ ⊕ ker π。
破缺 = 选择真空：观测等价但状态不同的真空存在。
Goldstone = 核模式：沿核方向移动无势能变化（无质量方向）。
```

**现状（2026-08-05 编译）**：
- ✅ **SB1** `factorized_potential_is_kernel_shift_symmetric`：因子化势核平移对称（K3 直接推论）
- ✅ **SB2** `kernel_fiber_is_ground`：核纤维都是真空 · ✅ **SB2'** `shifted_vacuum_is_ground`：真空的核平移仍真空（Goldstone 代数种子）
- ✅ **SB3** `broken_vacua_observationally_equivalent`：非平凡核 ⟹ 观测等价、势相等、状态不同的真空存在（"规律对称+状态不对称"是可证定理）
- 📋 `SymmetryBreaking` 结构（axiom-like，与 D1–D7 同级）
- **与 D7' 关键对比**：差商卡乘法逆元（ℤ[i] 非域）；破缺只需加法+核，ℤ[i] 完全满足——**破缺比微积分更早可达**
- **开放问题**：①质量 = 真空核分量（接 KernelRepresentation）需 ⊗ 泄漏机制（i⊗i = −1 ∈ ℝ，核非理想 ⟹ Goldstone"被吃掉"的代数原型）；②连续剩余对称（U(1) 型稳定子）；③动态破缺（T>T_c 相变）需时间
- **Lean 位置**：`SymmetryBreaking.lean`（SB1–SB3 已证）

### D9. Hidden Quaternion（隐数四元数）

```
隐数空间中是否存在满足 i² = -1 或 a·b·c = -1 的特殊单元（HiddenUnit）？
答案（已证）：存在。
四元数单位 {i, j, k} ↔ 反交换生成元 {iσ₁, iσ₂, iσ₃}：
    i² = j² = k² = -1  ⟸  C1（σᵢ² = I）+ E14（标量中心）
    ijk = -1           ⟸  C6（σ₁σ₂ = -iσ₃）+ C1
    ij ≠ ji            ⟸  C2（反交换）
表示 Φ(a+bi+cj+dk) = aI + b(iσ₁) + c(iσ₂) + d(iσ₃) 保加法保乘法
⟹ "i²=-1 型单元"是反交换的必然表示，不是新公理。
```

**现状（2026-08-06 编译）**：
- ✅ **Q1** `quat_i_sq`/`quat_j_sq`/`quat_k_sq`：i² = j² = k² = -1
- ✅ **Q2** `quat_ijk_minus_one`（ℍ 环内）；`iSigmas_ijk`（矩阵表示内）；`triple_product_square`（纯 Clifford：(σ₁σ₂σ₃)² = -1——用户"a·b·c = -1"猜想的已证实例）
- ✅ **Q3** `quat_ij_ne_ji`：ij ≠ ji（非交换）
- ✅ **Q4** `quat_mul_assoc`：ℍ 结合环
- ✅ **Q5** `quatToMat_mul`/`quatToMat_i/j/k`：Φ 保加法保乘法，Φ(i) = iσ₁——**四元数完全落入 Mat2 = Cℓ(3) 表示**
- ✅ **Q6** `cToQuat_mul`：ℂ ⊂ ℍ 子环
- ✅ **Q7** `quatHiddenUnit`/`cliffordHiddenUnit`：HiddenUnit 草案双实例化（ℍ 环 + Mat2 矩阵）
- 📋 `QuatRotation` 草案（单位四元数共轭作用 v ↦ q·v·q⁻¹ → 3D 旋转）：需范数 |q|²=1 + 逆元，ℤ 系数无逆元（D7' 同款卡点，实例化需升级系数环到 ℚ[i]/ℝ）
- **新增 ℂ 减法实例**：`instance : Sub ℂ`（core 缺 Sub，Mat2 同款处理见 Differential 模块）
- **Lean 位置**：`Quaternion.lean`（Q1–Q5 已证）；`HiddenSpace.lean`（H1–H5 已证，无状态向量/投影产生状态/幂等投影）

### D10. Hidden Space（隐数空间：无状态向量）

```
无状态万向向量 u ∈ H 的形式化：
    State(u) = undefined ⟺ HiddenVector 的 observed = none
投影 P : H → V 产生状态：P(u) = v ⟺ observed = some v 且 π(source) = v
不同投影 ⟹ 不同状态（Re 与 Im 在 cI 上区分）。
```

**现状（2026-08-06 编译）**：
- ✅ **H1** `projection_generates_state`/`state_generation`：投影产生状态（状态 = 观测值）
- ✅ **H2** `state_consistency`：标签 Some v ⟹ π(source) = v（标签是事实）
- ✅ **H3** `distinct_projections_distinct_states` + `cI_has_two_states`：不同投影 ⟹ 不同状态（π₁s ≠ π₂s ⟹ 状态不同；cI 在 Re 下为 0、Im 下为 1）
- ✅ **H4** `hiddenReProj_idempotent`/`hiddenReProj_linear`/`hiddenReProj_kernel_iff`：幂等投影 Π = ι∘Re 线性、幂等、核 = 虚轴（"观测塌缩"）
- ✅ **H5** `direction_emerges_from_projection`：方向涌现（复述 L7 正交分解）
- **与量子测量类比**：投影产生状态（H1）+ 幂等塌缩（H4）+ 核不可观测（K3）三者的代数骨架，无概率公理
- **Lean 位置**：`HiddenSpace.lean`（H1–H5 已证）

### D11. Hidden Projection Algebra（隐数投影代数）★ 路线主线

```
隐数的第一性不是 i²=-1（复数路线），而是投影幂等 P² = P（状态生成机制路线）。
    Hidden Space → Projection Algebra → State Space → Geometry
    （四元数/旋转 = 比较对象：空间已有时的变换机制，非隐数实现目标）

投影族 {P_i} 满足:
    幂等 P_i² = P_i          (观测后不再改变)
    正交 P_i∘P_j = 0 (i≠j)   (不同方向互不可见)
    完备 ΣP_i = id            (信息不丢失)
变换 T = P_i∘P_j 的复合是否封闭?是否成群?
```

**现状（2026-08-06 编译）**：
- ✅ **PA1** `IsProjection`（幂等自映射）+ `comp_of_commuting_projections_is_projection`：交换投影的复合仍是投影（抽象层）
- ✅ **PA2** `ComplementaryProjection` 结构（幂等/正交/完备）+ **ℂ 实例 `realImagProjection`**：{Π_re, Π_im} 全部字段已证
- ✅ **PA3** 复合表 5 项：re∘re=re、im∘im=im、re∘im=0、im∘re=0、0∘任何=0——**{Π_re, Π_im, 0} 构成半群**（`projection_composition_semigroup`）
- ✅ **PA4** 核/像分层：ker Π_im = 实轴、im Π_re = 实轴（可观测层 = 实数，不可观测层 = 虚数）
- ✅ **PA5** ★ **半群而非群**：`hproj_re_not_injective`（0 与 cI 同像）——非平凡投影不可逆，**状态生成有损 = 确定性来自信息损失**（K3 推论）；群结构需要可逆层（旋转/四元数，比较对象）
- ✅ **PA6** ★ **PVM 骨架**：`pvm_skeleton`——幂等+正交+完备 = 投影值分解（量子测量结构的代数骨架，无概率公理）
- ✅ **PA7** ★ **核质量泄露**：`kernel_mul_leaks_to_image`——∃ k ∈ ker π，Re(k²) ≠ 0（实例：i·i = -1，Re(-1) = -1）；核是加法子空间（K1）但**乘法不封闭**（非理想）；`kernelLeak` 定义泄漏量 + `kernelLeak_i` = -1；`leak_product_in_image`：泄漏产物可观测（流向像层，非丢失）。**这是"Goldstone 被吃掉"与"质量从核涌现"的代数原型（SB 文档 i⊗i = -1 ∈ ℝ 的定理化）**
- ✅ **PA8** ★ **核张量化**：`cKernelBiForm`（B(x,y) = Im x·Im y，验证 BiForm 公理）——ker π 上的 (0,2) 张量；`kernelBiForm_quad_kernel`：**核张量二次型 Q(k) = κ(k) = kernelInvC（质量候选 m² = κ 的第一个物理连接）**；`kernelBiForm_unit_norm`：B(i,i) = 1；`kernelBiForm_nondegenerate`：核上非退化（核张量是真度量）
- 📋 开放：多投影族的一般理论（投影秩、约当代数）、可逆层（变换群 = 旋转群,需域系数）、Born 规则（概率,框架外）；**质量解析的完整链（质量 = Φ(dim ker)，D2）仍需核上表示论**
- **Lean 位置**：`ProjectionAlgebra.lean`（PA1–PA8 已证）

## 4. 与 HIBS / DengYu 的连接

- **HIBS**：K5 ↔ HIBS 定理 6.5（π∘ι = id）；ProjectionPair ↔ HIBS 的嵌入-投影结构。
- **DengYu**：玻尔兹曼碰撞算子 Q 的碰撞不变量（1, v, |v|²）正是 Q 的核——
  "Kernel 决定质量"对应"碰撞不变量决定流体守恒律"；粗粒化投影是本工程 π 的物理实例。

## 5. 诚实声明

- D1–D6 是**研究目标**，不是已证定理；结构中的 `completeness`/`null_cone` 等字段
  是假设（axiom-like），Lean 只保证陈述良型，不保证成立。
- "推导出 KG/薛定谔/狄拉克方程"（gemini 对话 5.md）依赖连续时空假设（∂_μ），
  在严格第一性原理下不成立——这些是"已有框架下的重新表述"，不是独立推导。
- 数值匹配（6π⁵ ≈ 1836.118 等）为数字命理学，与定理链无关，已从本工程剔除。
