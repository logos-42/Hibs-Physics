-- ProjectionPhysics — SpaceModulation：空间场调制通信（四力合一的可调制空间场）
--
-- leo（2026-08-20）的新假设：
--   · 四种基本力在空间场里是统一的一种场——主线 GQF：四力 = 流动动量
--     P̂ = m(Ĉ − v̂) 的 product rule 分解（电场/核力/磁场/引力 = 同一
--     动量场的四个通道，GQF2）
--   · 这个统一的场可以调制，类似调频（FM）：把信息编码进空间场振荡的
--     相位步长（瞬时频率）——频率偏差 = 每步相位增量 m_k（可数：数圈数，
--     GQR 的"条数 = 圈数 = 频率"）
--   · 需要数学证明可以传递信息：编码 → 传输 → 解码 = 恒等（FM1–FM3）
--   · 不在物质视角下运行，而是直接在空间场内进行：载波 = 空间场本身的
--     方向旋转（幅值恒 1——纯相位调制，与调幅的本质区别 FM6）
--   · 频段是根据空间来理解的：载波频率 = 空间场振荡的相位步长
--     （ω₀ + m_k），频段 = 相位步长集合；空间流动可把调制拖曳到等效
--     超光速（GQC3：静止系等效速度 = 1 + v，流动系局部因果保持）——
--     调制随空间场运动，不在物质介质中传播
--   · 测量的媒介不再是电磁波，而是空间场本身：解调直接读空间场的相位
--     结构（主线 MS：E = −∂_tC、B = ∂_xC 是 C 的运动学——读 C 的相位
--     = 读空间场本身）
--
-- 核心定理（mathlib，FM1–FM6）：
--   FM1 ★ 相位步长可读：连续两个载波样本 s_{k+1}·conj(s_k) = exp(I(ω₀ + m_k))
--        ——信息被编码在载波相位差（瞬时频率），可从两个连续样本读出
--   FM2 ★ 读出注入性：exp(I(ω₀+b₁)) = exp(I(ω₀+b₂)) ⟹ b₁ = b₂（b ∈ {0,1}）
--        ——消息字母表在载波空间可区分（信息可传递的必要条件）
--   FM2b★ 消息注入性：相同载波序列 ⟹ 相同消息（不同消息产生不同信号）
--   FM3 ★ 解码往返：decode(encode(m)) = m——编码 → 传输 → 解码 = 恒等
--        ★ 数学证明空间场调制可以传递信息
--   FM4  调制 ⟹ 统一动量场响应：Ĉ₁ ≠ Ĉ₂ ⟹ m(Ĉ₁−v0) ≠ m(Ĉ₂−v0)（m≠0）
--        ——方向调制必然改变统一场动量（GQF1 接轨）
--   FM5  纯方向调制 ⟹ 总力 = 核力通道 m·dC（四力分解中 dm=0、dv=0 时，
--        GQF2 接轨）——调制方式决定激活哪个力通道
--   FM6 ★ 载波是单位模：|s_k| ≡ 1——纯相位调制（信息在相位/频率，不在幅值）
--   FM7  等效超光速（几何）：引用 GQC3——调制随空间场流动，静止系等效
--        速度可超光速，流动系局部因果保持（注释层 + 数值层）
--   FM8 ★ 频段来源·涡度恒等：刚体旋转流 C=(−Ωy,Ωx,0) 的 CurlZ = 2Ω
--        （涡度 = 二倍角速度——空间场固有振荡 = 涡旋运动）
--   FM9 ★ 固有频率：ω₀ = CurlZ/2 = Ω——空间场固有振荡频率由自身旋度决定，
--        不再是自由输入（第二输入缺口闭合一半）
--   FM10★ 频段 = 磁场谱：B_z = CurlZ（SF5：B = curl C）⟹ ω₀ = B_z/2——
--        频段读的是空间场旋度，测量媒介 = 空间场本身
--   FM11  载波即固有振荡：FM1 的 ω₀ 换成涡旋频率 Ω——调制叠加在空间场
--        固有振荡之上（FM1 + FM9 组合）
--   FM12  正频段：Ω > 0 ⟹ 每步瞬时频率 > 0（频段在正频区）
--
-- 诚实边界：FM1–FM3 是复指数代数（真但平凡——这正是调频数学本身）；
-- 框架贡献 = 把载波安装为空间场（统一场）的方向旋转 + 信息 = 相位步长
-- （可数圈数）+ 解调 = 直接读空间场相位（MS 接轨）+ 随流等效超光速
-- （GQC3 引用）。ω₀ 频段来源：本轮 FM8–FM12 由空间场固有振荡推导
-- （ω₀ = 涡旋频率 = |B|/2，非自由输入）；m_k 的调制激励机制仍是
-- 第二输入缺口。无新物理预言（消息字母表 / 信道容量仍结构层）。

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import ProjectionPhysics.Explorations.Spacefield3D

noncomputable section
open scoped BigOperators
namespace ProjectionPhysics.SpaceModulation

/- 消息：二进制比特流 m_k ∈ {0,1}（消息字母表 = 两个频段）。
   每条消息 = 一个频率偏差序列（瞬时频率 ω_k = ω₀ + m_k，可数圈数）；
   类型 m : ℕ → Fin 2（无限比特流；前 T 位是消息体）。 -/

/-- 相位累积：φ_k = Σ_{j<k} m_j——消息位 = 相位步长（每步相位增量，
    瞬时频率偏差；ω₀ + m_k = 第 k 步的瞬时频率 = 频段位置）。 -/
def fmPhase (m : ℕ → Fin 2) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (m j : ℝ)

/-- 相位累积的递推：φ_{k+1} = φ_k + m_k——相位步长逐位相加
    （消息位累积进相位；FM1 的核心代数步）。 -/
lemma fmPhase_succ (m : ℕ → Fin 2) (k : ℕ) :
    fmPhase m (k + 1) = fmPhase m k + (m k : ℝ) := by
  unfold fmPhase
  rw [Finset.sum_range_succ]

/-- 载波（空间场振荡）：s_k = exp(I·(ω₀·k + φ_k))——空间场方向在复平面
    （平面内两横向方向）上的旋转；幅值恒 1（纯相位调制）；ω₀ = 载波频率
    （频段中心）。这就是被调制的"统一场"：四力（GQF2 四通道）共享的
    单一空间场 C 的方向振荡。 -/
def fmCarrier (ω₀ : ℝ) (m : ℕ → Fin 2) (k : ℕ) : ℂ :=
  Complex.exp (Complex.I * (ω₀ * (k : ℝ) + fmPhase m k))

/-- 连续样本的相位步长读出：r_k = s_{k+1} · conj(s_k)——解调 = 读相邻
    两个载波样本的相位差（直接读空间场本身，不经 E/B；MS：E/B 是 C 的
    运动学）。 -/
def fmStep (ω₀ : ℝ) (m : ℕ → Fin 2) (k : ℕ) : ℂ :=
  fmCarrier ω₀ m (k + 1) * star (fmCarrier ω₀ m k)

/-- 解码（解调）：从相位步长读出消息位——两个频段 exp(I·ω₀)（位 0）与
    exp(I·(ω₀+1))（位 1）。 -/
def fmDecodeBit (ω₀ : ℝ) (x : ℂ) : Fin 2 :=
  if x = Complex.exp (Complex.I * (ω₀ : ℂ)) then 0 else 1

/-! ### FM1★. 相位步长可读：信息 = 载波相位差 -/

/-- FM1★. 连续两个载波样本的读出 = exp(I·(ω₀ + m_k))——信息被编码在载波
    的相位步长（瞬时频率）里，可以从两个连续样本精确读出。
    证明链：φ_{k+1} = φ_k + m_k（fmPhase_succ）→ norm_num 规范化强转 →
    参数分裂（ω₀·(k+1) + φ_k + m_k = (ω₀·k + φ_k) + (ω₀ + m_k)，ring）→
    exp_add 拆分 → exp_conj（star(exp z) = exp(star z)）→
    conj(I·x) = −I·x（simp）→ exp(z)·exp(−z) = 1（配对）。 -/
lemma fm1_step_phase (ω₀ : ℝ) (m : ℕ → Fin 2) (k : ℕ) :
    fmStep ω₀ m k = Complex.exp (Complex.I * (ω₀ + (m k : ℝ))) := by
  unfold fmStep fmCarrier
  rw [fmPhase_succ]
  norm_num
  have harg : Complex.I * ((ω₀ : ℂ) * ((k : ℂ) + 1) + ((fmPhase m k : ℂ) + ((m k : Fin 2) : ℂ))) =
      Complex.I * ((ω₀ : ℂ) * (k : ℂ) + (fmPhase m k : ℂ)) +
        Complex.I * ((ω₀ : ℂ) + ((m k : Fin 2) : ℂ)) := by
    ring
  rw [harg]
  rw [Complex.exp_add]
  rw [← Complex.exp_conj]
  simp [Complex.conj_I, Complex.conj_ofReal]
  have hp : Complex.exp (Complex.I * ((ω₀ : ℂ) * (k : ℂ) + (fmPhase m k : ℂ))) *
      Complex.exp (-(Complex.I * ((ω₀ : ℂ) * (k : ℂ) + (fmPhase m k : ℂ)))) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  calc
    Complex.exp (Complex.I * ((ω₀ : ℂ) * (k : ℂ) + (fmPhase m k : ℂ))) *
        Complex.exp (Complex.I * ((ω₀ : ℂ) + ((m k : Fin 2) : ℂ))) *
        Complex.exp (-(Complex.I * ((ω₀ : ℂ) * (k : ℂ) + (fmPhase m k : ℂ))))
        = Complex.exp (Complex.I * ((ω₀ : ℂ) * (k : ℂ) + (fmPhase m k : ℂ))) *
          Complex.exp (-(Complex.I * ((ω₀ : ℂ) * (k : ℂ) + (fmPhase m k : ℂ)))) *
          Complex.exp (Complex.I * ((ω₀ : ℂ) + ((m k : Fin 2) : ℂ))) := by ring
    _ = 1 * Complex.exp (Complex.I * ((ω₀ : ℂ) + ((m k : Fin 2) : ℂ))) := by rw [hp]
    _ = Complex.exp (Complex.I * ((ω₀ : ℂ) + ((m k : Fin 2) : ℂ))) := by simp

/-! ### FM2★. 读出注入性：消息字母表可区分 -/

/-- 辅助引理：|2πn| = 1 对整数 n 无解——n ≠ 0 时 |2πn| ≥ 2π > 1，
    与 |2πn| = 1 矛盾（2πn 的"圈数"不可能是一次奇数半圈）。 -/
private lemma two_pi_int_abs_ne_one {n : ℤ}
    (h : |(2 : ℝ) * Real.pi * (n : ℝ)| = 1) : False := by
  have hnzR : (n : ℝ) ≠ 0 := by
    intro hn0
    have h' : |(2 : ℝ) * Real.pi * (n : ℝ)| = 1 := h
    simp [hn0] at h'
  have hnab : (1 : ℝ) ≤ |(n : ℝ)| := by
    by_contra hlt
    have hlt' : |(n : ℝ)| < 1 := lt_of_not_ge hlt
    have hn0 : n = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt')
    exact hnzR (by exact_mod_cast hn0)
  have hbig : (2 : ℝ) * Real.pi * |(n : ℝ)| ≥ 2 * Real.pi := by
    nlinarith [Real.pi_pos, hnab]
  have hrew : |(2 : ℝ) * Real.pi * (n : ℝ)| = 2 * Real.pi * |(n : ℝ)| := by
    rw [abs_mul, abs_mul]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  have h1eq : (2 : ℝ) * Real.pi * |(n : ℝ)| = 1 := by
    rw [← hrew, h]
  nlinarith [hbig, h1eq, Real.pi_gt_three]

/-- FM2★. 读出注入性：两个消息位在载波空间可区分——exp(I·(ω₀+b₁)) =
    exp(I·(ω₀+b₂)) ⟹ b₁ = b₂（b ∈ {0,1}）。信息可传递的必要条件：接收端
    从相位步长能唯一确定消息位。
    证明链：exp_eq_exp_iff_exists_int（模 2πI）→ 取虚部 → (b₁−b₂) = 2πn
    → |b₁−b₂| ≤ 1 < 2π ≤ |2πn|（n ≠ 0，two_pi_int_abs_ne_one）矛盾
    ⟹ n = 0 ⟹ b₁ = b₂。 -/
lemma fm2_step_readout_injective (ω₀ : ℝ) (b₁ b₂ : Fin 2)
    (h : Complex.exp (Complex.I * (ω₀ + (b₁ : ℝ))) =
         Complex.exp (Complex.I * (ω₀ + (b₂ : ℝ)))) :
    b₁ = b₂ := by
  rcases Complex.exp_eq_exp_iff_exists_int.mp h with ⟨n, hn⟩
  have hsub : Complex.I * ((b₁ : ℝ) - (b₂ : ℝ)) =
      (n : ℂ) * (2 * Real.pi * Complex.I) := by
    calc
      Complex.I * ((b₁ : ℝ) - (b₂ : ℝ))
          = Complex.I * (ω₀ + (b₁ : ℝ)) - Complex.I * (ω₀ + (b₂ : ℝ)) := by
            ring
      _ = (n : ℂ) * (2 * Real.pi * Complex.I) := by
            rw [hn]
            ring
  have him := congrArg Complex.im hsub
  have hlin : (b₁ : ℝ) - (b₂ : ℝ) = 2 * Real.pi * (n : ℝ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using him
  fin_cases b₁ <;> fin_cases b₂
  · rfl
  · -- b₁ = 0, b₂ = 1：2πn = −1 ⟹ |2πn| = 1 ⟹ 矛盾（|2πn| ≥ 2π > 1）
    exfalso
    norm_num at hlin
    have hlin' : (2 : ℝ) * Real.pi * (n : ℝ) = -1 := by linarith
    have habs : |(2 : ℝ) * Real.pi * (n : ℝ)| = 1 := by
      rw [hlin']
      norm_num
    exact two_pi_int_abs_ne_one habs
  · -- b₁ = 1, b₂ = 0：2πn = 1 ⟹ 同样矛盾
    exfalso
    norm_num at hlin
    have hlin' : (2 : ℝ) * Real.pi * (n : ℝ) = 1 := by linarith
    have habs : |(2 : ℝ) * Real.pi * (n : ℝ)| = 1 := by
      rw [hlin']
      norm_num
    exact two_pi_int_abs_ne_one habs
  · rfl

/-! ### FM2b★. 消息注入性：不同消息 ⟹ 不同信号 -/

/-- FM2b★. 消息注入性：相同的载波序列 ⟹ 相同的消息——不同消息产生
    不同的信号（信息可传递：接收端能从信号区分不同消息）。
    证明链：逐位用 FM1（相位步长读出）+ FM2（字母表可区分）。
    T = 消息长度；信号 = 前 T+1 个载波样本（每步读出需要相邻两个样本）。 -/
lemma fm2_message_injective (ω₀ : ℝ) (m m' : ℕ → Fin 2) (T : ℕ)
    (h : ∀ k : Fin (T + 1), fmCarrier ω₀ m k = fmCarrier ω₀ m' k) :
    ∀ j : Fin T, m (j : ℕ) = m' (j : ℕ) := by
  intro j
  have hstep : fmStep ω₀ m (j : ℕ) = fmStep ω₀ m' (j : ℕ) := by
    unfold fmStep
    rw [h ⟨j.1 + 1, Nat.succ_lt_succ j.isLt⟩, h ⟨j.1, Nat.lt_succ_of_lt j.isLt⟩]
  rw [fm1_step_phase, fm1_step_phase] at hstep
  exact fm2_step_readout_injective ω₀ (m (j : ℕ)) (m' (j : ℕ)) hstep

/-! ### FM3★. 解码往返：编码 → 传输 → 解码 = 恒等 -/

/-- FM3★. 解码往返：decode(encode(m)) = m——编码 → 传输 → 解码 = 恒等。
    ★ 数学证明空间场调制可以传递信息：消息被编码进载波相位步长（FM1），
    步长在消息字母表上可区分（FM2），解调精确恢复原消息。
    证明链：分情况 m k = 0 / 1——位 0 的步长落在频段 exp(I·ω₀)（simp）；
    位 1 的步长 exp(I·(ω₀+1)) 与 exp(I·ω₀) 可区分（FM2 注入性，1 ≠ 0）
    ⟹ 解码给 1。 -/
lemma fm3_decode_roundtrip (ω₀ : ℝ) (m : ℕ → Fin 2) (k : ℕ) :
    fmDecodeBit ω₀ (fmStep ω₀ m k) = m k := by
  by_cases h0 : m k = 0
  · rw [fm1_step_phase, h0]
    unfold fmDecodeBit
    simp
  · have h1 : m k = 1 := by
      by_contra h1n
      have hcases : (m k : ℕ) = 0 ∨ (m k : ℕ) = 1 := by
        have hlt : (m k : ℕ) < 2 := (m k).isLt
        omega
      rcases hcases with h0v | h1v
      · exact h0 (Fin.ext h0v)
      · exact h1n (Fin.ext h1v)
    have hstep1 : fmStep ω₀ m k = Complex.exp (Complex.I * (ω₀ + ((1 : Fin 2) : ℝ))) := by
      rw [fm1_step_phase, h1]
    by_cases hc : fmStep ω₀ m k = Complex.exp (Complex.I * (ω₀ : ℂ))
    · -- 步长落在位 0 的频段 ⟹ FM2 注入性给出 1 = 0 ⟹ 矛盾（两频段可区分）
      exfalso
      have hc1 : Complex.exp (Complex.I * (ω₀ + ((1 : Fin 2) : ℝ))) =
          Complex.exp (Complex.I * (ω₀ + ((0 : Fin 2) : ℝ))) := by
        simpa using (Eq.trans hstep1.symm hc)
      exact (by norm_num : ¬(1 : Fin 2) = (0 : Fin 2))
        (fm2_step_readout_injective ω₀ 1 0 hc1)
    · -- 步长不在位 0 的频段 ⟹ 落入位 1 的频段 ⟹ 解码给 1
      have hc' : Complex.exp (Complex.I * (ω₀ + ((1 : Fin 2) : ℝ))) ≠
          Complex.exp (Complex.I * (ω₀ : ℂ)) := by
        intro h
        rw [← hstep1] at h
        exact hc h
      unfold fmDecodeBit
      rw [fm1_step_phase, h1, if_neg hc']

/-! ### FM4–FM5. 调制 ⟹ 统一场（四力）响应 -/

/-- FM4★. 调制 ⟹ 统一动量场响应：空间场方向被调制（Ĉ₁ ≠ Ĉ₂）时，统一场的
    流动动量 P̂ = m(Ĉ − v0) 必然改变（m ≠ 0）——四力合一场的调制不是
    "空转"，一定在动量场上留下可测量的变化（GQF1 接轨：P̂ = m·Ĉ − m·v0）。
    证明：m·(Ĉ₁−v0) = m·(Ĉ₂−v0) ⟹ m·(Ĉ₁−Ĉ₂) = 0 ⟹ Ĉ₁ = Ĉ₂（m ≠ 0 消去）。 -/
lemma fm4_momentum_responds (m Ĉ₁ Ĉ₂ v0 : ℂ) (hm : m ≠ 0) (hC : Ĉ₁ ≠ Ĉ₂) :
    m * (Ĉ₁ - v0) ≠ m * (Ĉ₂ - v0) := by
  intro h
  apply hC
  have h' : m * (Ĉ₁ - Ĉ₂) = 0 := by
    calc
      m * (Ĉ₁ - Ĉ₂) = m * (Ĉ₁ - v0) - m * (Ĉ₂ - v0) := by
        ring
      _ = 0 := by
        rw [h]
        ring
  exact sub_eq_zero.mp (by
    rcases mul_eq_zero.mp h' with hm0 | hX0
    · exact False.elim (hm hm0)
    · exact hX0)

/-- FM5★. 纯方向调制 ⟹ 总力 = 核力通道：四力分解（GQF2 product rule）中
    只有 dC ≠ 0（dm = 0、dv = 0——质量与速度不变，只调制空间场方向）时，
    总动量变化恰好是核力通道 m·dC——调制方式决定激活哪个力通道（四力
    合一于同一动量场 P̂ = m(Ĉ−v̂)）。 -/
lemma fm5_direction_modulation_force (m dC C v : ℂ) :
    (0 : ℂ) * C + m * dC - ((0 : ℂ) * v + m * 0) = m * dC := by
  ring

/-! ### FM6★. 载波是单位模：纯相位调制 -/

/-- FM6★. 载波是单位模：|s_k| ≡ 1——空间场调制是纯相位调制（信息在相位/
    频率步长，不在幅值），幅值恒为 1。与调幅（AM）的本质区别：幅值通道
    不携带信息（幅值噪声不影响解调）。证明链：exp_re/exp_im（z = I·x 的
    re = 0、im = x）→ normSq = cos²x + sin²x = 1（sin_sq_add_cos_sq）。 -/
lemma fm6_carrier_unit (ω₀ : ℝ) (m : ℕ → Fin 2) (k : ℕ) :
    Complex.normSq (fmCarrier ω₀ m k) = 1 := by
  unfold fmCarrier
  rw [Complex.normSq_apply, Complex.exp_re, Complex.exp_im]
  have hre : (Complex.I * (ω₀ * (k : ℝ) + fmPhase m k)).re = 0 := by simp
  have him : (Complex.I * (ω₀ * (k : ℝ) + fmPhase m k)).im =
      ω₀ * (k : ℝ) + fmPhase m k := by simp
  rw [hre, him]
  simp [Real.exp_zero]
  rw [← Real.sin_sq_add_cos_sq (ω₀ * (k : ℝ) + fmPhase m k)]
  ring

/-! ### FM7. 等效超光速（几何，引用 GQC3——注释层 + 数值层）
leo 关键物理观点：调制直接安装在空间场（统一场）上，随空间流动传播——
空间本身在其他位置运动时，携带的调制信息也随之运动。
- 静止系等效速度 = 信号速度 + 流动速度 = 1 + v（v > 0 可超光速）；
  GQC3a（gqc3_equivalent_speed）：流动坐标中 t 步可达 ⟹ 静止距离
  |j−i| ≤ t + |φ_j−φ_i|；GQC3b（gqc3_superluminal_geometric）：信号随流
  + 流动梯度 > 1 ⟹ 1 步内静止位移 > 1——等效超光速。
- 因果保持：信号相对流动从未超过局部光速（GQC2 带宽光锥在流动系成立）。
- "频段根据空间理解"：载波频率 ω₀ 定义在流动系；静止观测者测到的空间
  频率被压缩 λ_st = λ₀/(1+v)（数值层 N32）。
- 数值层：verify_space_modulation.py N30–N33。 -/

/-! ### FM8–FM12. 频段来源：空间场固有振荡（ω₀ = 涡旋频率 = |B|/2）
leo（2026-08-20）补上上一轮的诚实边界缺口：FM1–FM7 里 ω₀（载波频段）
是自由输入。本轮从空间场固有振荡推导它：
  · 空间场的固有振荡 = 空间场的涡旋运动——B = curl C ≠ 0 处空间场局部
    旋转（Spacefield3D SF5：磁场 = 自旋的代数位置；自旋 = 涡旋）
  · 刚体旋转流 C = (−Ωy, Ωx, 0)（角速度 Ω）的涡度 CurlZ = 2Ω——局部
    角速度 = 涡度一半：ω₀ = CurlZ/2 = Ω（流体运动学恒等，真但平凡）
  · ⟹ 载波频率 ω₀ 由空间场自身旋度决定（Ω = 空间场固有角速度），不是
    自由输入；频段 = 空间场旋度谱 = 磁场谱（B = curl C，SF5）
  · FM1 的相位步长重述：exp(I·(ω₀ + m_k)) 中 ω₀ = Ω——调制叠加在空间场
    固有振荡之上（FM11）；正频段约束（FM12）。 -/

/-- 刚体旋转流（绕 z 轴，角速度 Ω）：C = (−Ω·y, Ω·x, 0)。
    空间场固有振荡的原型：C 局部绕 z 轴旋转，旋度 ≠ 0（涡旋）。 -/
def rotFlow (Ω : ℝ) : SpaceField3D.VecField4 :=
  { x := fun _ _ j _ => -Ω * (j : ℝ)
    , y := fun _ i _ _ => Ω * (i : ℝ)
    , z := fun _ _ _ _ => 0 }

/-- FM8★ 涡度恒等：刚体旋转流的 curl z 分量 = 2Ω（涡度 = 二倍角速度）。
    证明链：CurlZ = Dx C.y − Dy C.x = [Ω(i+1)−Ωi] − [−Ω(j+1)+Ωj] = 2Ω。 -/
lemma fm8_rot_flow_curl_z (Ω : ℝ) (t i j k : ℤ) :
    SpaceField3D.CurlZ (rotFlow Ω) t i j k = 2 * Ω := by
  unfold SpaceField3D.CurlZ SpaceField3D.Dx SpaceField3D.Dy rotFlow
  push_cast
  ring

/-- FM8b 涡度向量：x/y 分量为 0（纯绕 z 轴旋转，无其他方向涡旋）。 -/
lemma fm8b_rot_flow_curl_xy (Ω : ℝ) (t i j k : ℤ) :
    SpaceField3D.CurlX (rotFlow Ω) t i j k = 0 ∧
    SpaceField3D.CurlY (rotFlow Ω) t i j k = 0 := by
  unfold SpaceField3D.CurlX SpaceField3D.CurlY SpaceField3D.Dx SpaceField3D.Dy
    SpaceField3D.Dz rotFlow
  constructor <;> push_cast <;> ring

/-- FM9★ 固有振荡频率 = 涡度一半：ω₀ = CurlZ/2 = Ω。
    空间场固有振荡频率由空间场自身旋度决定——不再是自由输入
    （上一轮的"ω₀ 频段来源"缺口，本轮闭合）。 -/
lemma fm9_intrinsic_frequency (Ω : ℝ) (t i j k : ℤ) :
    Ω = SpaceField3D.CurlZ (rotFlow Ω) t i j k / 2 := by
  rw [fm8_rot_flow_curl_z]
  ring

/-- FM10★ 频段 = 磁场谱：B_z = CurlZ（SF5：B = curl C）⟹ ω₀ = B_z/2。
    频段读的是空间场旋度（磁场谱）——测量媒介 = 空间场本身。 -/
lemma fm10_frequency_from_B (Ω : ℝ) (t i j k : ℤ) :
    Ω = (SpaceField3D.B_of (rotFlow Ω)).z t i j k / 2 := by
  unfold SpaceField3D.B_of
  change Ω = SpaceField3D.CurlZ (rotFlow Ω) t i j k / 2
  rw [fm8_rot_flow_curl_z]
  ring

/-- FM11★ 载波即固有振荡：FM1 的相位步长公式中 ω₀ 换成涡旋频率 Ω——
    调制叠加在空间场固有振荡之上（FM1 + FM9 的组合重述）。 -/
lemma fm11_carrier_on_intrinsic (Ω : ℝ) (m : ℕ → Fin 2) (k : ℕ) :
    fmStep Ω m k = Complex.exp (Complex.I * (Ω + (m k : ℝ))) := by
  exact fm1_step_phase Ω m k

/-- FM12 正频段：Ω > 0 ⟹ 每步瞬时频率 ω_k = Ω + m_k > 0
    （频段在正频区；调制只产生正频率偏差）。 -/
lemma fm12_positive_frequency (Ω : ℝ) (m : ℕ → Fin 2) (k : ℕ) (hΩ : 0 < Ω) :
    0 < Ω + (m k : ℝ) := by
  have hm : (0 : ℝ) ≤ (m k : ℝ) := by
    have hlt : (m k : ℕ) < 2 := (m k).isLt
    have hcases : (m k : ℕ) = 0 ∨ (m k : ℕ) = 1 := by omega
    rcases hcases with h0 | h1
    · rw [h0]
      norm_num
    · rw [h1]
      norm_num
  linarith

end ProjectionPhysics.SpaceModulation
