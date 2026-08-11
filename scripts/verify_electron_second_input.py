#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
电子第二输入检验 — 寻找独立的"空间阻抗"值 (不从 m_e 反推)

背景: 质量 = 自旋 × 空间阻抗 假设在电子上失败的原因是恒等式陷阱 —
所有用 {ℏ,c,λ_c,r_e,a₀} 构造的长度都由 m_e 定义, 循环.
任务 2 (leo): 寻找一个不从 m_e 反推的独立输入, 使 m_e 成为预言.

候选独立输入 (全部不引用 m_e):
  A. 三方向模型的 M₀ ≈ 0.987 GeV (来自胶球 0++ 拟合, 独立于电子!)
  B. 普朗克尺度 m_P = √(ℏc/G) ≈ 1.22e19 GeV (引力尺度)
  C. 精细结构常数 α 的组合 (纯数, 独立)
  D. 4Λ_QCD ≈ 1 GeV (QCD 尺度, 独立于电子)

检验: m_e 能否写成 独立输入 × f(α, 纯数)?
"""
import math

# --- CODATA 2018 / PDG ---
me_GeV   = 0.51099895000e-3        # 电子质量 GeV
me_MeV   = 0.51099895000
M0       = 0.9873                    # 三方向模型空间阻抗 (胶球拟合, 独立于电子)
mP_GeV   = 1.220890e19               # 普朗克质量
alpha    = 1/137.035999084
LambdaQCD = 0.25                     # GeV (MS-bar 尺度)

print("=" * 74)
print("任务 2: 电子第二输入检验 — 空间阻抗的独立来源")
print("=" * 74)

print(f"\n[基础] m_e = {me_GeV:.6e} GeV; M₀(胶球) = {M0:.4f} GeV; m_P = {mP_GeV:.3e} GeV")
print(f"       m_e/M₀ = {me_GeV/M0:.6e}")
print(f"       m_e/m_P = {me_GeV/mP_GeV:.6e}")
print(f"       m_e/(4Λ_QCD) = {me_GeV/(4*LambdaQCD):.6e}")

print("\n[检验 A] m_e = M₀ × f(α) ?  (M₀ 来自胶球, 与电子无关)")
f = me_GeV / M0
print(f"  f = m_e/M₀ = {f:.6e}")
cands = {
    "α²": alpha**2,
    "α²×10": 10*alpha**2,
    "α³": alpha**3,
    "α/(2π)": alpha/(2*math.pi),
    "α²/(4π)": alpha**2/(4*math.pi),
    "α/(2π)²": alpha/(2*math.pi)**2,
    "α/2π·√3": alpha*math.sqrt(3)/(2*math.pi),
    "α²·(π/2)": alpha**2*math.pi/2,
}
for name, val in cands.items():
    ratio = f/val if val else float('inf')
    print(f"    f vs {name} = {val:.6e}  比值 {ratio:.4f}")

print("\n[检验 B] m_e = m_P × g(α) ?  (普朗克尺度, 引力)")
g = me_GeV / mP_GeV
print(f"  g = m_e/m_P = {g:.6e}")
for n in range(5, 15):
    a_n = alpha**n
    if a_n > 0:
        print(f"    α^{n} = {a_n:.4e}  比值 {g/a_n:.4f}")

print("\n[检验 C] 纯数组合 (不依赖任何质量尺度)")
print(f"  m_e/M₀ = {f:.6e}")
print(f"  1/(2·965) ≈ {1/(2*965):.6e}  (965 不干净)")
print(f"  α²×10 = {10*alpha**2:.6e}  与 f 比值 {f/(10*alpha**2):.4f}")

print("\n" + "=" * 74)
print("结论 (诚实)")
print("=" * 74)
print(f"""
1. 三方向 M₀ ≈ {M0:.4f} GeV 是第一个独立于电子的尺度 (来自胶球 0++ 拟合).
   但 m_e/M₀ = {f:.3e} ≈ α²×10 只差 {abs(f/(10*alpha**2)-1)*100:.1f}%,
   不是干净公式 — 不能宣布匹配.
2. 普朗克尺度: m_e/m_P = {g:.3e} ≈ α^11 附近但不精确 (比值 {g/alpha**11:.3f}),
   无干净幂律.
3. 独立判断: 胶球尺度 M₀ (纯 QCD 动力学) 与电子质量 (Higgs/Yukawa 起源)
   在标准模型中机制不同 — 期望它们没有简单的 α 组合关系.
4. 真正诚实的结论: 第二输入**尚未找到**. 三方向假设给出胶球尺度,
   但电子质量需要另一条路径 (Higgs 门户/QED 动力学层), 这正是
   MinimalCore 边界声明的内容 — 电子数值留作后续扩展.
5. 这不是失败: "空间阻抗"作为概念有了第一个独立候选 (M₀≈1 GeV),
   但它在胶球上工作 (纯动力学质量), 在电子上不工作 (需耦合层) —
   这恰好与标准模型的分工一致 (QCD 质量 vs Higgs 质量).
""")
