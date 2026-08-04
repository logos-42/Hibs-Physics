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
