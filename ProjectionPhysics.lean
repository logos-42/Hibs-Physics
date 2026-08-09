-- ProjectionPhysics — root module
--
-- 工程草案：从 HIBS 三公理出发的"代数涌现物理学"
-- （Representation Completeness / Kernel Null / 五座桥梁）
--
--   Definitions.lean   投影/核/像/信息守恒/不变量/二次型
--   Kernel.lean        核的代数性质（可证明定理 K1–K6）
--   Completeness.lean  不变量因子化定理（可证明）+ 完备性草案
--   Mass.lean          核质量（平凡核 ⟹ 质量为零，可证明）+ 核表示草案
--   NullTheorem.lean   Kernel Null Theorem 草案 + 代数核心
--   Bridges.lean       五座桥梁的代数定义
--   Algebra.lean       矩阵算法：加法群→自同态环→矩阵乘法结合律（A1–A4）
--   Clifford.lean      自旋：Pauli 矩阵反交换 + i 涌现 + 旋量表示（C1–C5）
--   LinearAlgebra.lean 矢量/张量/kernel：向量空间公理、核子空间、rank-nullity、
--                     双线性形式 + 极化恒等式（L1–L7）
--   Differential.lean  微分涌现的代数种子：迹(散度)/转置/反对称部分(旋度)/差商（E1–E12）
--   SymmetryBreaking.lean 对称性破缺：核平移对称(规范)/核纤维真空流形/Goldstone(核模式)（SB1–SB3, D8）
--   HiddenSpace.lean   隐数空间：无状态万向向量/Option 状态标签/投影产生状态/幂等投影（H1–H6）
--   Quaternion.lean    四元数：Hamilton 关系 i²=j²=k²=ijk=-1 从 Clifford 反交换涌现 + 矩阵表示（Q1–Q5）
--   ProjectionAlgebra.lean 投影代数：投影族/互补投影对/复合表半群/核像分层/量子测量骨架（PA1–PA6）
--   HiddenSpacePhysics.lean 隐数物理桥梁：三轴/空间流/旋量阻抗质量/夸克自由度/涌现时间（HSP1–HSP5）
--   HIBSPhysicalBridges.lean HIBS 到 Higgs-Yukawa/离散 beta/质量壳接口（HIBS1–HIBS5）
--   HiddenOnlyHiggs.lean 纯隐数、无时间的静态 Higgs 构造（HOH1–HOH5）
--   HiddenHiggsFlowInterface.lean 可选流参数接口（独立于静态模型，HOH3）
--   HiddenAxisConversions.lean H/R/I 全状态正交可逆转换标准
--   HiddenMassTimeEvents.lean 质量事件计数生成离散涌现时间

import ProjectionPhysics.Definitions
import ProjectionPhysics.Kernel
import ProjectionPhysics.Completeness
import ProjectionPhysics.Mass
import ProjectionPhysics.NullTheorem
import ProjectionPhysics.Bridges
import ProjectionPhysics.Algebra
import ProjectionPhysics.Clifford
import ProjectionPhysics.LinearAlgebra
import ProjectionPhysics.Differential
import ProjectionPhysics.SymmetryBreaking
import ProjectionPhysics.HiddenSpace
import ProjectionPhysics.Quaternion
import ProjectionPhysics.ProjectionAlgebra
import ProjectionPhysics.HiddenSpacePhysics
import ProjectionPhysics.HIBSPhysicalBridges
import ProjectionPhysics.HiddenOnlyHiggs
import ProjectionPhysics.HiddenHiggsFlowInterface
import ProjectionPhysics.HiddenAxisConversions
import ProjectionPhysics.HiddenMassTimeEvents
