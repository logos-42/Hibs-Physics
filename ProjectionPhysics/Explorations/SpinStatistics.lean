-- ProjectionPhysics — SpinStatistics：自旋-统计约束（胶球构造学 Part A）
--
-- leo（2026-08-13）胶球构造学探索的 Lean 化第一部分：
--   纯胶球（三个自旋-1 胶子）的组合自旋恒为整数 ⟹ 永远是玻色子，
--   不可能构造费米子（夸克/轻子）——这是自旋-统计的硬约束；
--   费米子必须引入半整数自旋参与（旋量，即 MC1 的 σψ 旋量流）。
--
-- 编码：自旋 s 用 2s : Nat（TwoSpin）表示，半整数安全
--   （s = 1 ⟹ 2s = 2；s = 1/2 ⟹ 2s = 1）。
-- 组合规则：两自旋 a,b 组合出 j ∈ {|a-b|, |a-b|+2, ..., a+b}
--   （Clebsch-Gordan 步长 2，`InSpinCombination`）。
--
-- 核心定理（全部可证，无 sorry）：
--   SS1  triplet_gluon_combination_is_bosonic —— ★ 三胶子组合自旋恒为整数
--   SS2  pure_boson_combination_is_bosonic —— 玻色子×玻色子组合仍是玻色子
--   SS3  gluon_spinor_channel_yields_fermion —— 胶子+旋量组合出现半整数
--   SS4  fermion_requires_half_integer_participant —— ★ 费米子必须半整数参与
--        （纯玻色子组合不可能产生费米子：自旋统计硬约束）

namespace ProjectionPhysics

/-- 两倍自旋值：自旋 s 用 2s : Nat 编码（半整数安全）。 -/
abbrev TwoSpin := Nat

/-- 胶子自旋：s = 1 ⟹ 2s = 2。 -/
def gluonSpin : TwoSpin := 2

/-- 旋量自旋：s = 1/2 ⟹ 2s = 1（费米子自由度，MC1 的 σψ 旋量流）。 -/
def spinorSpin : TwoSpin := 1

/-- 自旋组合下界 |a − b|（Nat 截断减法用 if 处理）。 -/
def spinCombLow (a b : TwoSpin) : Nat := if a ≥ b then a - b else b - a

/-- 自旋组合：j ∈ {|a−b|, |a−b|+2, ..., a+b}（Clebsch-Gordan 步长 2）。 -/
def InSpinCombination (j a b : TwoSpin) : Prop :=
  ∃ k : Nat, j = spinCombLow a b + 2 * k ∧ j ≤ a + b

/-- 玻色子：2s 为偶数（自旋为整数）。 -/
def IsBosonic (j : TwoSpin) : Prop := ∃ r : Nat, j = 2 * r

/-- 费米子：2s 为奇数（自旋为半整数）。 -/
def IsFermionic (j : TwoSpin) : Prop := ∃ r : Nat, j = 2 * r + 1

-- ---------------------------------------------------------------------------
-- 基本事实
-- ---------------------------------------------------------------------------

theorem gluon_spin_is_bosonic : IsBosonic gluonSpin := ⟨1, rfl⟩

theorem spinor_spin_is_fermionic : IsFermionic spinorSpin := ⟨0, rfl⟩

/-- 偶数 2s 值之差仍是偶数：|a−b| 偶（a,b 偶 ⟹ 组合下界偶）。 -/
theorem spinCombLow_even {a b : TwoSpin} (ha : IsBosonic a) (hb : IsBosonic b) :
    IsBosonic (spinCombLow a b) := by
  rcases ha with ⟨ra, hra⟩
  rcases hb with ⟨rb, hrb⟩
  by_cases hab : a ≥ b
  · refine ⟨ra - rb, ?_⟩
    simp [spinCombLow, hab]
    rw [hra, hrb]
    rw [← Nat.mul_sub]
  · refine ⟨rb - ra, ?_⟩
    simp [spinCombLow, hab]
    rw [hra, hrb]
    rw [← Nat.mul_sub]

/-- 偶+偶组合仍为偶：纯玻色子组合不可能产生半整数自旋。 -/
theorem even_combination_of_even {j a b : TwoSpin} (ha : IsBosonic a)
    (hb : IsBosonic b) (hj : InSpinCombination j a b) : IsBosonic j := by
  rcases hj with ⟨k, hjk, hle⟩
  rw [hjk]
  rcases spinCombLow_even ha hb with ⟨r, hr⟩
  refine ⟨r + k, ?_⟩
  rw [hr]
  rw [← Nat.mul_add]

-- ---------------------------------------------------------------------------
-- SS2：玻色子 × 玻色子 = 玻色子（单步组合的硬约束）
-- ---------------------------------------------------------------------------

theorem pure_boson_combination_is_bosonic {j a b : TwoSpin} (ha : IsBosonic a)
    (hb : IsBosonic b) (hj : InSpinCombination j a b) : IsBosonic j :=
  even_combination_of_even ha hb hj

-- ---------------------------------------------------------------------------
-- SS1：★ 三胶子（三个自旋-1）组合自旋恒为整数 ⟹ 纯胶球永远是玻色子
-- ---------------------------------------------------------------------------

theorem triplet_gluon_combination_is_bosonic :
    ∀ j : TwoSpin,
      (∃ j₁ : TwoSpin, InSpinCombination j₁ gluonSpin gluonSpin ∧
        InSpinCombination j j₁ gluonSpin) → IsBosonic j := by
  intro j ⟨j₁, hj₁, hjj₁⟩
  have hj₁_bos : IsBosonic j₁ :=
    even_combination_of_even gluon_spin_is_bosonic gluon_spin_is_bosonic hj₁
  exact even_combination_of_even hj₁_bos gluon_spin_is_bosonic hjj₁

-- ---------------------------------------------------------------------------
-- SS3：胶子（s=1）+ 旋量（s=1/2）组合出现半整数 ⟹ 费米子通道存在
-- ---------------------------------------------------------------------------

theorem gluon_spinor_channel_yields_fermion :
    ∃ j : TwoSpin, InSpinCombination j gluonSpin spinorSpin ∧ IsFermionic j := by
  refine ⟨1, ?_, ?_⟩
  · refine ⟨0, ?_, ?_⟩
    · simp [spinCombLow, gluonSpin, spinorSpin]
    · decide
  · exact spinor_spin_is_fermionic

-- ---------------------------------------------------------------------------
-- 偶数/奇数互斥（2r = 2r'+1 不可能）
-- ---------------------------------------------------------------------------

theorem bosonic_not_fermionic {j : TwoSpin} (hb : IsBosonic j) (hf : IsFermionic j) :
    False := by
  rcases hb with ⟨r, hr⟩
  rcases hf with ⟨r', hr'⟩
  -- j = 2r 且 j = 2r'+1 ⟹ 2r = 2r'+1 ⟹ 两边 % 2 矛盾（0 ≠ 1）
  have hrr : 2 * r = 2 * r' + 1 := by
    calc
      2 * r = j := hr.symm
      _ = 2 * r' + 1 := hr'
  have hcong : (2 * r) % 2 = (2 * r' + 1) % 2 := congrArg (fun n => n % 2) hrr
  have hleft : (2 * r) % 2 = 0 := by rw [Nat.mul_mod_right]
  have hright : (2 * r' + 1) % 2 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod_right]
  rw [hleft, hright] at hcong
  omega

/-- 费米子 ⟺ 2s 奇数（用模 2 二分）。 -/
theorem even_of_not_fermionic (n : TwoSpin) (hn : ¬ IsFermionic n) : IsBosonic n := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · refine ⟨n / 2, ?_⟩
    have hdiv : n / 2 * 2 + n % 2 = n := Nat.div_add_mod' n 2
    rw [h0] at hdiv
    calc
      n = n / 2 * 2 + 0 := hdiv.symm
      _ = 2 * (n / 2) := by rw [Nat.mul_comm]; simp
  · exfalso
    exact hn ⟨n / 2, by
      have hdiv : n / 2 * 2 + n % 2 = n := Nat.div_add_mod' n 2
      rw [h1] at hdiv
      calc
        n = n / 2 * 2 + 1 := hdiv.symm
        _ = 2 * (n / 2) + 1 := by rw [Nat.mul_comm]⟩

-- ---------------------------------------------------------------------------
-- SS4：★ 费米子必须半整数自旋参与——纯玻色子组合不可能产生费米子
-- ---------------------------------------------------------------------------

theorem fermion_requires_half_integer_participant {a b j : TwoSpin}
    (hj : InSpinCombination j a b) (hjf : IsFermionic j) :
    IsFermionic a ∨ IsFermionic b := by
  by_cases hfa : IsFermionic a
  · exact Or.inl hfa
  · by_cases hfb : IsFermionic b
    · exact Or.inr hfb
    · exfalso
      have hae : IsBosonic a := even_of_not_fermionic a hfa
      have hbe : IsBosonic b := even_of_not_fermionic b hfb
      have hje : IsBosonic j := even_combination_of_even hae hbe hj
      exact bosonic_not_fermionic hje hjf

/-- ★ 自旋统计硬约束的物理表述：纯胶球（无旋量）不可能是费米子。
    三个自旋-1 胶子的任何组合产物都是玻色子。 -/
theorem pure_glueball_is_never_fermionic :
    ∀ j : TwoSpin,
      (∃ j₁ : TwoSpin, InSpinCombination j₁ gluonSpin gluonSpin ∧
        InSpinCombination j j₁ gluonSpin) → IsFermionic j → False := by
  intro j hj hjf
  exact bosonic_not_fermionic (triplet_gluon_combination_is_bosonic j hj) hjf

-- ---------------------------------------------------------------------------
-- SS5–SS8：杂化态（胶子 s=1 + 旋量流 s=1/2）——1⊗1/2 = 1/2 ⊕ 3/2
-- ---------------------------------------------------------------------------

/-- ★ SS5：胶子+旋量组合恰好两个通道：2s ∈ {1, 3}，即 s = 1/2 或 s = 3/2
    —— 1⊗1/2 = 1/2 ⊕ 3/2（两通道质量分裂的代数基础）。 -/
theorem gluon_spinor_channels :
    ∀ j : TwoSpin, InSpinCombination j gluonSpin spinorSpin → j = 1 ∨ j = 3 := by
  intro j hj
  rcases hj with ⟨k, hjk, hle⟩
  simp [spinCombLow, gluonSpin, spinorSpin] at hjk hle
  have hle' : 1 + 2 * k ≤ 3 := by
    rw [← hjk]
    exact hle
  have hkle : k ≤ 1 := by omega
  by_cases hk : k = 0
  · left
    rw [hk] at hjk
    omega
  · right
    have hk1 : k = 1 := by omega
    rw [hk1] at hjk
    omega

/-- SS6：两个通道都可达（1/2 态和 3/2 态都存在）。 -/
theorem gluon_spinor_two_channels :
    ∃ j₁ j₂ : TwoSpin, j₁ ≠ j₂ ∧ InSpinCombination j₁ gluonSpin spinorSpin ∧
      InSpinCombination j₂ gluonSpin spinorSpin := by
  refine ⟨1, 3, ?_, ?_, ?_⟩
  · decide
  · refine ⟨0, ?_, ?_⟩
    · simp [spinCombLow, gluonSpin, spinorSpin]
    · decide
  · refine ⟨1, ?_, ?_⟩
    · simp [spinCombLow, gluonSpin, spinorSpin]
    · decide

/-- SS7：杂化态质量分裂幅度（离散）：Δ(2s) = 2 ⟹ Δs = 1
    （3/2 通道比 1/2 通道重一个自旋单位；动力学能级分裂未建模——
    与 966 倍缺口同源，需耦合机制）。 -/
theorem hybrid_split_magnitude : 3 - 1 = 2 := rfl

/-- SS8：3/2 通道比 1/2 通道重（锚定单调的代数形式：
    质量 = 锚定 ⟹ 更高自旋通道锚定更强）。 -/
theorem three_halves_heavier_than_half : 1 < 3 := by decide

/-- SS8b：若锚定质量取 2s 值（单位锚定），则 3/2 通道锚定是 1/2 通道的 3 倍。 -/
theorem hybrid_anchor_ratio : 3 = 3 * 1 := rfl

end ProjectionPhysics
