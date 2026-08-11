#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
三方向假设的数据匹配度检验 — 严格版
用格点 QCD 不确定度评估两套诠释的匹配度:
  诠释 A (三方向): m_G = √N·M₀, N = {3, 6, 7}, M₀ = m(0++)/√3
  诠释 B (v2 两胶子): m_G = √N·M₀', N = {2, 4, 5}, M₀' = m(0++)/√2
判据: 偏差 %, σ 数 (偏差/格点不确定度), 加权评分.

格点不确定度 (2022-2024 综述, 典型值):
  m(0++) = 1.71 ± 0.05 GeV
  m(2++) = 2.40 ± 0.12 GeV
  m(0-+) = 2.56 ± 0.15 GeV
"""
import math

# --- 格点中心值 + 不确定度 (GeV) ---
spectrum = {
    "0++": (1.71, 0.05),
    "2++": (2.40, 0.12),
    "0-+": (2.56, 0.15),
}
order = ["0++", "2++", "0-+"]

# --- 两套诠释 ---
interpretations = {
    "A 三方向 (3,6,7)": {0: 3, 1: 6, 2: 7},
    "B 两胶子 (2,4,5)": {0: 2, 1: 4, 2: 5},
}

print("=" * 74)
print("数据匹配度检验: 三方向假设 (m_G = √N·M₀)")
print("=" * 74)

# 0++ 拟合 M₀
m0 = spectrum["0++"][0]
M0_A = m0 / math.sqrt(3)
M0_B = m0 / math.sqrt(2)
print(f"\n格点谱: " + ", ".join(f"{k}={v[0]}±{v[1]}" for k, v in spectrum.items()))
print(f"拟合: M₀(A) = m(0++)/√3 = {M0_A:.4f} GeV;  M₀'(B) = m(0++)/√2 = {M0_B:.4f} GeV")

print(f"\n{'通道':<6} {'格点':<14} {'A 预测':<12} {'A 偏差%':<9} {'A σ':<7} {'B 预测':<12} {'B 偏差%':<9} {'B σ':<7}")
print("-" * 74)

results = {"A": {}, "B": {}}
for i, ch in enumerate(order):
    m_exp, err = spectrum[ch]
    mA = math.sqrt(interpretations["A 三方向 (3,6,7)"][i]) * M0_A
    mB = math.sqrt(interpretations["B 两胶子 (2,4,5)"][i]) * M0_B
    devA = (mA - m_exp) / m_exp * 100
    devB = (mB - m_exp) / m_exp * 100
    sigA = abs(mA - m_exp) / err
    sigB = abs(mB - m_exp) / err
    results["A"][ch] = (devA, sigA)
    results["B"][ch] = (devB, sigB)
    print(f"{ch:<6} {m_exp:<6.2f}±{err:<6.2f} {mA:<12.3f} {devA:<9.2f} {sigA:<7.2f} {mB:<12.3f} {devB:<9.2f} {sigB:<7.2f}")

# 加权评分 (σ 越小越好; 0++ 是拟合点不计)
def score(interp):
    s = 0.0
    for ch in order[1:]:
        s += results[interp][ch][1] ** 2
    return math.sqrt(s)

sA = score("A")
sB = score("B")
print(f"\n加权 σ (2++/0-+ 平方和根, 排除拟合点): A = {sA:.3f}, B = {sB:.3f}")
print(f"判定: 诠释 {'A 更优' if sA < sB else 'B 更优'} (差值 {abs(sA-sB):.3f} σ)")

print("\n" + "-" * 74)
print("N 序列的两种可能解释 (诚实标注)")
print("-" * 74)
print(f"""
  A: N = 3, 6, 7   → 3=三方向基态; 6=3×2; 7=3+4  (无干净规则)
  B: N = 2, 4, 5   → 2=两胶子; 4=2×2; 5=2+3      (无干净规则)
  两者都是事后拟合 N, 第一性解释均缺.
  注: 2++ 预测在 A/B 下相同 (√6/√3 = 2/√2 = √2), 无区分力.
  区分点在 0-+: A 偏差 2.0% (0.35σ) vs B 偏差 5.6% (0.95σ).
""")

print("=" * 74)
print("检验 2: 电子第二输入 (m_e = M₀·f) 匹配度")
print("=" * 74)
me = 0.51099895000e-3
f = me / M0_A
f10a2 = 10 * (1/137.035999084)**2
dev = (f - f10a2) / f10a2 * 100
print(f"  m_e/M₀ = {f:.6e}  vs  10α² = {f10a2:.6e}")
print(f"  偏差 = {dev:.2f}%")
print(f"  但 '10' 因子无第一性来源 (为何是 10?), 且胶球尺度 M₀ 来自 QCD,"
      f"\n  电子质量在 SM 中来自 Higgs/Yukawa — 机制不同, 2.8% 偏差判定为"
      f"\n  数值巧合候选, 不构成公式 [诚实]")

print("=" * 74)
print("检验 3: r₀ 一致性")
print("=" * 74)
hc = 0.1973269804
r0 = hc / M0_A
print(f"  M₀(A) = {M0_A:.4f} GeV ⟹ r₀ = ℏc/M₀ = {r0:.4f} fm ≈ 0.2 fm")
print(f"  与质子康普顿波长 ℏc/m_p = {hc/0.938:.4f} fm 同量级 (0.2 vs 0.21)")
print(f"  r₀ ≈ 0.2 fm ≈ 4Λ_QCD⁻¹ (Λ_QCD≈0.25 GeV ⟹ 1/Λ=0.79 fm, 4Λ=1.0 GeV)")

print("=" * 74)
print("结论 (诚实)")
print("=" * 74)
print(f"""
1. 三方向诠释 A (N=3,6,7) 在格点不确定度内匹配: 0++ 拟合, 2++ 偏差 0.8%
   (0.15σ), 0-+ 偏差 2.0% (0.35σ). 加权 σ_A = {sA:.3f}.
2. 两诠释对比: A 优于 B (加权 σ {sA:.3f} vs {sB:.3f}), 区分点在 0-+.
   但两者 N 序列都缺第一性解释, 且 2++ 无区分力 (预测相同).
3. 电子: m_e/M₀ ≈ 10α² 偏差 2.8%, 因子 10 无来源 ⟹ 巧合候选, 非公式.
4. 数据匹配度结论: 三方向假设与现有格点数据相容 (全部 <1σ),
   但样本只有 3 个通道, 不足以确立 N 序列规则; 需更多通道
   (1++, 2-+, 3++...) 或更精确格点数据来区分诠释 A/B.
""")
