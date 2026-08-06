# Wiki 日志

## [2026-08-06] 证明补充 | 隐数空间 + 四元数从 Clifford 反交换涌现（H1–H5, Q1–Q5, D9/D10）

- 问题（leo 的任务 Prompt）：无状态万向向量 u ∈ H 如何经投影产生状态？隐数空间中是否存在满足 i²=-1 或 a·b·c=-1 的"隐数单元"？隐数结构是否类似复数/四元数？
- **隐数空间（D10, HiddenSpace.lean H1–H5 全部已证）**：
  - H1 投影产生状态：`HiddenVector`（source + Option 状态标签）形式化"无状态"= none、"有状态"= some v；`projection_generates_state`：任何源元素经投影获得状态且状态 = 观测值
  - H2 状态真实性：标签 Some v ⟹ π(source) = v（consistency 字段）
  - H3 不同投影 ⟹ 不同状态：`distinct_projections_distinct_states`（π₁s ≠ π₂s ⟹ 状态不同）；实例：cI 在 Re 下为 0、Im 下为 1（`cI_has_two_states`）
  - H4 幂等投影 Π = ι∘Re：幂等（观测后再观测不变）+ 线性 + 核 = 虚轴（"观测塌缩"）
  - H5 方向涌现：z = Re(z)·1 + Im(z)·i（复述 L7）
- **隐数四元数（D9, Quaternion.lean Q1–Q5 全部已证）**：
  - 核心答案：**四元数关系是 C1/C2/C6 的推论，不是新公理**。{i,j,k} ↔ {iσ₁, iσ₂, iσ₃}（Pauli 复化）
  - Q1 i²=j²=k²=-1（`quat_i_sq` 等）；Q2 ijk=-1（`quat_ijk_minus_one`、矩阵版 `iSigmas_ijk`、纯 Clifford 版 `triple_product_square`：(σ₁σ₂σ₃)²=-1 = **"a·b·c=-1"猜想的已证实例**）；Q3 ij≠ji（`quat_ij_ne_ji`，隐数代数必然非交换）；Q4 结合环（`quat_mul_assoc`）
  - Q5 表示 Φ(a+bi+cj+dk) = aI+b(iσ₁)+c(iσ₂)+d(iσ₃) 保加法保乘法（`quatToMat_mul`）——**四元数完全落入 Mat2 = Cℓ(3) 表示**
  - Q6 ℂ ⊂ ℍ 子环（`cToQuat_mul`）；Q7 `HiddenUnit` 草案双实例化（`quatHiddenUnit` ℍ 环 + `cliffordHiddenUnit` Mat2 矩阵）
- **新增**：`HiddenSpace.lean`（Module 12, H1–H5）+ `Quaternion.lean`（Module 13, Q1–Q5）+ `instance : Sub ℂ`（core 缺 Sub，Mat2 同款）；`ProjectionPhysics.lean` 根模块加 import
- **诚实边界**：`QuatRotation`（单位四元数共轭作用 → 3D 旋转）需范数 + 逆元，ℤ 无逆元（D7' 同款卡点，升级 ℚ[i]/ℝ 后可达）；无概率公理——"类量子坍缩"仅取代数骨架（投影产生状态 + 幂等 + 核不可观测）
- 来源：2026-08-06 会话（leo × 小剑）。

## [2026-08-05] 理论概念编译 + 证明 | 对称性破缺在隐数框架内实现（SB1–SB3, D8）

- 问题（leo）：物理的对称性破缺推导（Z₂ 势 → 真空选择 → Goldstone → Higgs）能否在隐数推导里实现？
- 核心主张：**对称性 = 核平移 ζ ↦ ζ⊕κ（κ ∈ ker π），观测不变——即已证的 K3**。theory-time-emergence.md 的"没有对称群 ⟹ 谈不上破缺"结论更新：对称群 = ker π，破缺对象与方式都有了落点。
- 势经投影因子化 V(ζ) := Ṽ(π ζ) ⟹ 自动核平移不变（**SB1 已证**，规律对称是定理不是假设）；真空流形 = 整条核纤维（**SB2 已证**）；真空的核平移仍真空（**SB2' 已证**，Goldstone 代数种子）；非平凡核 ⟹ 观测等价、势相等、状态不同的真空存在（**SB3 已证**，"规律对称+状态不对称"逐字成立）。
- **Goldstone 对应**：核模式 = 沿核纤维移动无势能变化 = 无质量方向（K4 内部自由度）；质量 = 真空核分量（接 KernelRepresentation）；⊗ 泄漏（i⊗i = −1 ∈ ℝ，核非理想）是"Goldstone 被吃掉"的代数原型。
- **与 D7' 关键对比**：差商卡乘法逆元（ℤ[i] 非域）；**破缺只需加法+核，ℤ[i] 完全满足——破缺比微积分更早可达**。这是 D8 的卖点。
- 新增 `SymmetryBreaking.lean`（Module 11）：`KernelShiftSymmetric` 定义 + SB1/SB2/SB2'/SB3 已证 + `SymmetryBreaking` 草案结构（axiom-like，字段即物理故事：proj/potential/factorizes/vacuum/is_ground/broken）。
- 诚实边界：动态破缺（T>T_c 相变）需时间（无）；连续剩余对称（U(1) 型稳定子）需乘法作用+复结构；ℤ[i] 实例化 is_ground 验证需非线性（Int 平方非负，omega 不够）。
- 来源：2026-08-05 会话（leo × 小剑）。

## [2026-08-04] 证明补充 | E9 与逆元：差分 vs 差商的分界（E13–E16 + D7'）

- 澄清（leo 问"E9 可以和逆元有关吗"）：E9 证明只用加法逆元（乘法逆元未出场）；E9 是**差分**（分子 L h），真正的**差商**要除以 h——h⁻¹ 是乘法逆元的入口；补逆元后差商化简需乘法结合律（E16 伏笔）+ L 保乘法（E13 雏形）。"位置无关"（加法，平凡）与"方向无关"（乘法，非平凡）在除法门前分界。
- 新增定理：E13 `scalar2_mul`（标量嵌入保乘法）、E14 `scalar2_commute`（标量层是中心）、E15 `mul_hom_comp`（保乘法复合封闭，A1 乘法孪生）、E16 `left_mul_comp`（左乘复合=左乘乘积，A3 结合律 ⟹ Flow 线性化是左乘）。
- 新增草案结构 D7' `DifferenceQuotient`：L 保乘法 + 保单位 + 非零元有乘法逆元 ⟹ 差商方向无关 `(L h)·h⁻¹ = L 1`（开放目标；ℤ[i] 无逆元，实例化需升级系数环到 ℚ[i]/ℝ）。
- 诚实边界：D7' 的 `inv_existence` 在 Mat2/Int 下不可满足——这正是"补上逆元"的 Lean 表达。
- 来源：2026-08-04 会话（leo × 小剑）。

## [2026-08-04] 证明补充 | D7 微分涌现的代数种子（Differential.lean E1–E12）

- 新增 `Differential.lean`（Module 9）：迹 matTr（散度）、转置 matTranspose（旋度原料）、差商定理。
- 已证：tr 线性（E1）/奇偶性 + tr(I)=维数（E2）/对转置不变（E3）/tr(M−Mᵀ)=0（**E4 散度∘旋度=0**）/(M−Mᵀ)ᵀ=−(M−Mᵀ)（E5 旋度反对称）/对称-反对称分解（E6）/tr(MN)=tr(NM)（**E7 迹循环性**）/tr(z·M)=z·tr M（E8 标量性）/转置对合+反同态 (MN)ᵀ=NᵀMᵀ。
- **★ E9 导数=线性算子本身**：L(s+h)−L(s)=L(h)（差商与位置无关，D7 平凡但关键推论）；E10 斜率=π∘L 差商形式（A1 复合封闭）；E11 自旋无迹 tr σᵢ=0；E12 σ₂ 反对称（旋度生成元）。
- 诚实边界：带除法的差商仍无定义（无逆元）；连续 ∇·/∇× 仍卡 D4。E1–E12 是"代数种子"，不是微积分。
- 来源：2026-08-04 会话（leo × 小剑）。

## [2026-08-04] 理论概念编译 | 微分涌现 + 除法术语修正

- 分析：草案中**无**斜率/旋度/散度/导数内容（全仓 grep 零命中）；散度未推导；唯一微积分痕迹是 time 页标注为走私的 ∂_t。
- 新增 `theory-differential-emergence.md` + SPEC D7：导数 = End(S) 环上的线性化（End(S) 已证为环 A1/A2）；斜率 = π∘L；散度 = tr(L)；旋度 = 反对称部分（Clifford 楔结构已证 C2）。
- 术语修正（leo 指出）：**除法 = 乘以逆元**，归约路径通；真实卡点是 ℂ = Int×Int 无 `Inv`/`Field` 实例（ℤ[i]-型环非域），差商在隐数空间无定义，但补逆元后斜率即有隐数空间意义。
- 来源：2026-08-04 会话问答（leo × 小剑）。

## [2026-08-04] 启动 | 初始化知识系统

- 建立 wiki、manifest、检查脚本和 repo 级默认规则。

## [2026-08-04] 理论概念编译 | 核/质量/投影 + 时间/自旋

- 新增 `theory-kernel-mass.md`：核=投影的核（实例：虚轴 iR = ker(Re)）；质量=核标量不变量（表示论路线）；投影/流通/核运动定义；已证/草案状态索引。
- 新增 `theory-time-emergence.md`：当前理论无时间；时间涌现两条候选路线（Flow 乘法步数 / 签名负号方向）；对称性破缺无形式化基础；下一步 D5。
- 来源：2026-08-04 会话问答（leo × 小剑）。

