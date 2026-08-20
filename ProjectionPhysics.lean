-- ProjectionPhysics — root module
--
-- 工程草案：从 HIBS 三公理出发的"代数涌现物理学"
-- （Representation Completeness / Kernel Null / 五座桥梁）
--
-- ★ 目录分层（2026-08-14 减法重组，按 AGENTS.md 减法原则）：
--
--   【主线 = 空间流动假设（08-11 后，全部物理 5 行）】
--   SpaceLightSpeed.lean   矢量光速：c = 空间本身的等效速度（SLS1–SLS6）
--   SpaceMetric.lean       空间流动度规：dτ²=dt²−dx²/c²，光子 dτ=0（SM1–SM6）
--   SpaceGravity.lean      Gordon 度规：引力=流动非均匀，Φ=½v²（SG1–SG11）
--   RelativityDeviation.lean 差值相对论：光速不变=(c−v)被抵消（RD1–RD7）
--   LorentzRebuild.lean    洛伦兹重构（mathlib）：boost 保持度规（LR1–LR5）
--   DiracMathlib.lean      狄拉克桥 mathlib 版：质量=手征耦合（DB1'–DB6'）
--   MinimalCoreMathlib.lean 最小核心 mathlib 版：质量=锚定（MC1'–MC6'）
--   PauliMathlib.lean      Clifford mathlib 重写（C1'–C4'）
--
--   【探索 = 胶球/色结构（frozen，2026-08-14 起不再加定理）】
--   Explorations/SpinStatistics.lean     自旋统计硬约束（SS1–SS8）
--   Explorations/CliffordSix.lean        Cℓ(6) 8 维表示（CS1–CS3）
--   Explorations/ColorOctetMathlib.lean  3⊗3=8⊕1 无迹分解（CM1–CM3）
--   Explorations/SphericalHarmonics.lean 胶球力=球谐（SH1–SH5）
--   Explorations/SU3Bridge.lean          SU(3) 循环子群
--   Explorations/GlueballBridge.lean     SU(3) 色作用与胶球质量
--
--   【归档 = 隐数代数前身路线 + core 双轨参考（deprecated，08-06 前主线）】
--   Archive/Definitions.lean   投影/核/像/信息守恒/不变量/二次型
--   Archive/Kernel.lean        核的代数性质（可证明定理 K1–K6）
--   Archive/Completeness.lean  不变量因子化定理（可证明）+ 完备性草案
--   Archive/Mass.lean          核质量（平凡核 ⟹ 质量为零，可证明）+ 核表示草案
--   Archive/NullTheorem.lean   Kernel Null Theorem 草案 + 代数核心
--   Archive/Bridges.lean       五座桥梁的代数定义
--   Archive/Algebra.lean       矩阵算法：加法群→自同态环→矩阵乘法结合律（A1–A4）
--   Archive/Clifford.lean      自旋：Pauli 矩阵反交换 + i 涌现 + 旋量表示（C1–C5）
--   Archive/LinearAlgebra.lean 矢量/张量/kernel：向量空间公理、核子空间、rank-nullity、
--                     双线性形式 + 极化恒等式（L1–L7）
--   Archive/Differential.lean  微分涌现的代数种子：迹(散度)/转置/反对称部分(旋度)/差商（E1–E12）
--   Archive/SymmetryBreaking.lean 对称性破缺：核平移对称(规范)/核纤维真空流形/Goldstone(核模式)（SB1–SB3, D8）
--   Archive/HiddenSpace.lean   隐数空间：无状态万向向量/Option 状态标签/投影产生状态/幂等投影（H1–H6）
--   Archive/Quaternion.lean    四元数：Hamilton 关系 i²=j²=k²=ijk=-1 从 Clifford 反交换涌现 + 矩阵表示（Q1–Q5）
--   Archive/ProjectionAlgebra.lean 投影代数：投影族/互补投影对/复合表半群/核像分层/量子测量骨架（PA1–PA6）
--   Archive/HiddenSpacePhysics.lean 隐数物理桥梁：三轴/空间流/旋量阻抗质量/夸克自由度/涌现时间（HSP1–HSP5）
--   Archive/HIBSPhysicalBridges.lean HIBS 到 Higgs-Yukawa/离散 beta/质量壳接口（HIBS1–HIBS5）
--   Archive/HiddenOnlyHiggs.lean 纯隐数、无时间的静态 Higgs 构造（HOH1–HOH5）
--   Archive/HiddenHiggsFlowInterface.lean 可选流参数接口（独立于静态模型，HOH3）
--   Archive/HiddenAxisConversions.lean H/R/I 全状态正交可逆转换标准
--   Archive/HiddenMassTimeEvents.lean 质量事件计数生成离散涌现时间
--   Archive/HiddenEventClocks.lean 事件/质量事件、局部离散时钟与路径聚合
--   Archive/FlowConservation.lean Flow 链组合律与条件式动量不变量
--   Archive/DiracBridge.lean  狄拉克桥 core 版（DB1–DB6，mathlib 版在主线）
--   Archive/MinimalCore.lean  最小核心 core 版（MC1–MC2+MC1h，mathlib 版在主线）
--
-- 注：历史模块清单（含已移入主线/探索/归档的完整映射）见 2026-08-14 重组前
-- 的 git 历史；本注释只维护当前分层。SpaceLightSpeed 引用 Archive.Clifford/
-- Archive.MinimalCore（core 锚定定义，历史遗留依赖，见 wiki 减法重组记录）。

--   RelativityDeviation.lean 相对论公式的差值项：光速不变=(c-v)被分母抵消；γ²用差值参数化

import ProjectionPhysics.Archive.Definitions
import ProjectionPhysics.Archive.Kernel
import ProjectionPhysics.Archive.Completeness
import ProjectionPhysics.Archive.Mass
import ProjectionPhysics.Archive.NullTheorem
import ProjectionPhysics.Archive.Bridges
import ProjectionPhysics.Archive.Algebra
import ProjectionPhysics.Archive.Clifford
import ProjectionPhysics.Archive.LinearAlgebra
import ProjectionPhysics.Archive.Differential
import ProjectionPhysics.Archive.SymmetryBreaking
import ProjectionPhysics.Archive.HiddenSpace
import ProjectionPhysics.Archive.Quaternion
import ProjectionPhysics.Archive.ProjectionAlgebra
import ProjectionPhysics.Archive.HiddenSpacePhysics
import ProjectionPhysics.Archive.HIBSPhysicalBridges
import ProjectionPhysics.Archive.HiddenOnlyHiggs
import ProjectionPhysics.Archive.HiddenHiggsFlowInterface
import ProjectionPhysics.Archive.HiddenAxisConversions
import ProjectionPhysics.Archive.HiddenMassTimeEvents
import ProjectionPhysics.Archive.HiddenEventClocks
import ProjectionPhysics.Archive.FlowConservation
import ProjectionPhysics.Explorations.SU3Bridge
import ProjectionPhysics.Explorations.GlueballBridge
import ProjectionPhysics.Explorations.SpinStatistics
import ProjectionPhysics.Explorations.CliffordSix
import ProjectionPhysics.Explorations.ColorOctetMathlib
import ProjectionPhysics.Archive.MinimalCore
import ProjectionPhysics.SpaceLightSpeed
import ProjectionPhysics.Archive.DiracBridge
import ProjectionPhysics.LorentzRebuild
import ProjectionPhysics.PauliMathlib
import ProjectionPhysics.DiracMathlib
import ProjectionPhysics.MinimalCoreMathlib
import ProjectionPhysics.SpaceMetric
import ProjectionPhysics.RelativityDeviation
import ProjectionPhysics.Explorations.SphericalHarmonics
import ProjectionPhysics.SpaceGravity
import ProjectionPhysics.SpaceFold
import ProjectionPhysics.MassCancellation
import ProjectionPhysics.Explorations.EntanglementHelix
import ProjectionPhysics.Explorations.BlackHoleWormhole
import ProjectionPhysics.Explorations.MaxwellFlow
import ProjectionPhysics.Explorations.MaxwellSpace
import ProjectionPhysics.Explorations.SpaceField3D
import ProjectionPhysics.Explorations.SpinFromSpace
import ProjectionPhysics.Explorations.DoubleSlit
import ProjectionPhysics.Explorations.GlueballCoupling
import ProjectionPhysics.Explorations.Twistor
import ProjectionPhysics.Explorations.QFTFlow
import ProjectionPhysics.Explorations.SpaceExtensibility
