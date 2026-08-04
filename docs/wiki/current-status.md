---
title: Hibs-Physics 当前状态
source: session
last_confirmed: 2026-08-04
audience: self
stage: draft
schema_version: 2
created: 2026-08-04
tags: [status]
status: current
---

# 当前状态

- **已支持（已证）**：核/质量/投影（K1–K6, L1–L10, M1）· 矩阵算法（A1–A4）· Clifford/自旋（C1–C6）· 信息守恒/能量（B1, infoLoss）
- **草案（未证）**：D1 完备性（ℂ 实例已证）· D2 核表示 · D3 核零锥 · D4 度量签名（最薄弱）· D5 Flow 守恒 · D6 Clifford（3 维已证）· **D7 微分涌现（新）**
- **明确未支持**：时间（无 ∂_t）、导数/斜率/散度/旋度（无连续性 + 无逆元）、光滑性、∇·/∇×
- **最近澄清**："除法 = 乘以逆元"——卡点在 ℂ 无 `Inv` 实例（ℤ[i]-型环非域），非"乘法之外除法独立缺失"
- **最近风险**：D4 签名来源无人证明；gemini 的 ∂_μ 推导为走私假设（SPEC §5）
- **线上状态**：本地 Lean 项目，无部署
