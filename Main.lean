import ProjectionPhysics

def main : IO Unit := do
  IO.println "ProjectionPhysics: 代数涌现物理学（HIBS 延伸工程）— Lean 4 草案."
  IO.println "已证明定理:"
  IO.println "  observables_depend_only_on_image   — Kernel 不可观测 (K3)"
  IO.println "  invariant_factor_through_projection — 可观测量因子化通过投影"
  IO.println "  left_inverse_of_injective           — 单射嵌入 ⟹ 存在左逆投影 (K5)"
  IO.println "  kernel_mass_zero_on_trivial_kernel   — 平凡核 ⟹ 核质量为零"
  IO.println "  nontrivial_kernel_gives_internal_degree — 非平凡核 ⟹ 内部自由度 (K4)"
  IO.println "矩阵算法 (A1–A4):"
  IO.println "  comp_additive / comp_assoc         — 自同态环: 复合封闭且结合"
  IO.println "  matMul_assoc / matMul_add_right    — 2×2 复矩阵乘法结合律/分配律"
  IO.println "自旋 (C1–C5):"
  IO.println "  sigma1_sq / sigma2_sq / sigma3_sq  — Pauli 生成元平方 = I"
  IO.println "  sigma1_sigma2_anticommute ...      — 反交换 γᵢγⱼ+γⱼγᵢ = 0"
  IO.println "  i_emerges_from_clifford            — ★ (σ₁σ₂)² = -1: 虚数单位涌现"
  IO.println "  spinor_rep_hom                     — 旋量表示保持乘法 (MN)ψ = M(Nψ)"
  IO.println "草案声明 (待证明): RepresentationCompleteness / KernelRepresentation / KernelNullTheorem / CliffordEmergence"
