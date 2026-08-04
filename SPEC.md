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

## 2.5 推导链：公理 → 矩阵 / 张量 / 自旋（已形式化）

```
A2a (⊕ 封闭) ──► S 加法群 ──► End(S) 环（A1: 复合封闭；A2: 复合结合）
   ──► 选基 ⟹ 矩阵表示 ──► 矩阵乘法结合律/分配律（A3, A4 已证）
A2b (⊗ : S×S → R) ──► 双线性形式（张量原语）──► 二次型 Q
   ──► Clifford 代数 Cℓ(Q)（C1: σ²=I；C2: 反交换）
   ──► 旋量空间（C5: 表示同态）──► 自旋
   ──► ★ (σ₁σ₂)² = −1（C3）：i 是表示对象，不是公理
   ──► σ₃ = i·σ₁σ₂（C4）：第三方向从前两个涌现（手性的代数雏形）
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
**现状（2026-08-04 编译）**：
- ✅ End(S) 环结构已证（A1 复合封闭 + A2 复合结合）——导数"居住"的环存在
- ✅ Clifford 反交换/楔结构已证（C2：σᵢσⱼ + σⱼσᵢ = 0）——**旋度的代数雏形已存在**（Cℓ ⊃ 外代数）
- ⚠️ **核心缺口（诚实，2026-08-04 修正）**：公理无连续性、且**无逆元**（除法 = 乘以逆元，归约路径通着；但 ℂ = Int×Int 是 ℤ[i]-型环，全仓无 `Inv`/`Field` 实例，ℤ[i] 非域 ⟹ 差商 `(f(s₁)⊖f(s₂)) ⊗ (s₁⊖s₂)⁻¹` 无定义）。差商/线性化/迹/转置均未形式化；给 S 补上逆元后差商/斜率在隐数空间内即有意义
- ❌ 连续版本（∇·、∇×、∂_μ）需 D4 度量 + 光滑性假设，与 §5 的 ∂_μ 走私警告同级
- **物理含义**：散度 = 核方向的信息流（∝ 信息损失/能量，见 Bridges.infoLoss）；旋度 = 不可观测的环形核运动（K4 内部自由度的微分版）；斜率 = 可观测演化比率（动量 P = π∘Flow 的差分版本）
- **推导结论**：线性映射的差商恒等于它自己 ⟹ 当前框架内"导数 = 线性算子本身"（平凡的）；非线性结构出现前，散度/旋度无法脱离 End(S) 环走得更远
- **Lean 位置**：无（草案；依赖 D5 ⊗ 结合性 + D4 度量）

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
