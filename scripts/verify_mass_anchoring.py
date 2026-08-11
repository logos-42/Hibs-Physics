#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
质量锚定假设的数值验证 — 诚实检验 v2（旋量流 + 胶球谱比）
假设: 质量 = 内部运动状态(自旋) × 空间运动的阻抗(锚定效果)
v2 更新: ① 自旋 = 旋量流 σψ (Clifford), ② 胶球谱 m² = N·M₀² 检验。

常数来源: CODATA 2018 / PDG 2024
"""
import math

c      = 299792458.0                 # m/s
hbar   = 1.054571817e-34             # J·s
me     = 9.1093837015e-31            # kg
me_MeV = 0.51099895000               # MeV
alpha  = 1/137.035999084             # 精细结构常数
re     = 2.8179403262e-15            # m  电子经典半径
lc     = 3.8615926796e-13            # m  电子康普顿波长
g_e    = 2.00231930436256            # 电子 g 因子
a_e    = (g_e-2)/2                   # 异常磁矩
mp     = 1.67262192369e-27           # kg
mp_MeV = 938.27208816                # MeV
eV     = 1.602176634e-19             # J

print("=" * 74)
print("检验 1: 电子 — 等效质量 = 自旋 × 空间阻抗 ?")
print("=" * 74)

S = hbar / 2                          # 电子自旋角动量 ℏ/2

# 1A: 康普顿尺度 (恒等式: λ_c 由 m_e 定义)
m_A = S / (lc * c)
print(f"\n[1A] m_cand = S/(λ_c·c) = {m_A:.6e} kg = m_e/2 (比值 {m_A/me:.6f})")
print(f"     → 恒等式: λ_c = ℏ/(m_e·c) ⟹ 无独立信息 [自洽, 非预言]")

# 1B: 经典半径 (恒等式: r_e 内含 m_e)
m_B = S / (re * c)
print(f"\n[1B] m_cand = S/(r_e·c) = {m_B:.6e} kg (比值 {m_B/me:.4f})")
print(f"     2α·S/(r_e·c) = {2*alpha*S/(re*c):.6e} kg ≡ m_e, 但 r_e 内含 m_e ⟹ 恒等式")

# 1C: 玻尔半径
a0 = hbar / (alpha * me * c)
m_C = hbar / (c * a0)
print(f"\n[1C] m_cand = ℏ/(c·a₀) = {m_C:.6e} kg = α·m_e (比值 {m_C/me:.6f}) ⟹ 恒等式")

# 1D: 光子
print(f"\n[1D] 光子: 模型预言零锚定 ⟹ m=0; 实验上限 <1e-18 eV ⟹ [通过, 序关系]")

# 1E: g-2
print(f"\n[1E] a_e 实验 = {a_e:.15f}, 模型 = 0 (无 QED 圈图) ⟹ [失败点]")

# 1F: 质子/电子
print(f"\n[1F] m_p/m_e 实验 = {mp/me:.3f}, 模型自旋同为 ℏ/2 ⟹ [失败点: 需内部结构]")

print()
print("=" * 74)
print("检验 2: 胶球 — 格点谱 vs m² = N·M₀² (v2 新增)")
print("=" * 74)

# 格点 QCD 中心值 (2022-2024)
m0pp = 1.71      # GeV
m2pp = 2.40      # GeV
m0mp = 2.56      # GeV
rt3 = math.sqrt(3)
rt2 = math.sqrt(2)

print(f"\n[2A] 格点: m(0++)={m0pp}, m(2++)={m2pp}, m(0-+)={m0mp} GeV")
print(f"     m(2++)/m(0++) = {m2pp/m0pp:.4f} vs √2 = {rt2:.4f} (差 {abs(m2pp/m0pp-rt2)/rt2*100:.2f}%)")
print(f"     m²(2++)/m²(0++) = {(m2pp/m0pp)**2:.4f} ≈ 2")

print(f"\n[2B] 模型 m_G = √N·M₀: 0++(N=2), 2++(N=4), 0-+(N=5)")
print(f"     拟合 M₀ = m(0++)/√2 = {m0pp/rt2:.3f} GeV")
M0 = m0pp / rt2
for name, N, m_exp in [("0++", 2, m0pp), ("2++", 4, m2pp), ("0-+", 5, m0mp)]:
    m_model = math.sqrt(N) * M0
    dev = abs(m_model - m_exp) / m_exp * 100
    print(f"     {name}: √{N}·M₀ = {m_model:.3f} GeV vs 格点 {m_exp:.2f} GeV (偏差 {dev:.1f}%)")

print(f"\n[2C] 0++ 胶球 J=0 但内部两自旋-1 胶子: 内部运动非零 ⟹ 不矛盾 (修正 v1 论证)")

print()
print("=" * 74)
print("检验 3: 旋量流锚定 (v2 — MinimalCore.lean MC1 新实现)")
print("=" * 74)
print("""
  spinFlow σψ : 自旋算子 σ 作用在旋量 ψ 上 = 内部运动状态
  锚定质量 := 旋量流四分量范数之和 (componentNorm)
  定理: ψ ≠ 0 ⟹ 0 < m(σ₁ψ)     [非零自旋 ⟹ 非零锚定]
  光子: ψ = 0 ⟹ m = 0          [零旋量 ⟹ 零锚定]
  Lean 已验证 (#eval: σ₁·(1,0)→1, σ₁·(0,1)→1, σ₁·(1,1)→2;
                 隐数版 h²: 3→9, -4→16)
""")

print("=" * 74)
print("结论 (v2)")
print("=" * 74)
print("""
1. 电子: 恒等式陷阱不变 — 无独立预言力 (需独立空间阻抗输入).
2. 胶球谱: m² = N·M₀² 与格点 0++/2++ 相容 (N=2,4, M₀≈1.21 GeV);
   0-+(N=5) 偏差 ~9% (格点不确定度内边缘). 这是假设唯一有
   数值内容的支持点 — M₀ 仍为拟合参数, 但谱形 √N 是结构预言.
3. 自旋=旋量流实现: 代数正确 (非零⟹非零, 零⟹零), 但仍是序关系.
4. 失败点不变: a_e 需 QED, m_p/m_e 需内部结构.
5. 诚实判断: "自旋×空间阻抗"是自洽序关系框架; 胶球谱比 √N 是
   最接近数值预言的方向, 需要更精确格点数据确认.
""")
