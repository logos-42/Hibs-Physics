/-
SpiralLattice.IntSquares — arithmetic of integer fluxes.

  IS1  |k| ≤ k²          for every integer k
  IS2  k² − k is even    for every integer k
  IS3  k ≠ 0 ⟹ 1 ≤ k²
-/
import SpiralLattice.Postulates

namespace SpiralLattice

/-- IS1: for an integer, |k| ≤ k². -/
theorem natAbs_le_sq (k : Int) : (k.natAbs : Int) ≤ k * k := by
  have h := @Int.natAbs_mul_self k
  have h2 : k.natAbs ≤ k.natAbs * k.natAbs := Nat.le_mul_self _
  have h3 : ((k.natAbs : Nat) : Int) ≤ ((k.natAbs * k.natAbs : Nat) : Int) := by
    exact_mod_cast h2
  rw [h] at h3
  exact h3

/-- IS2: k² and k have the same parity. -/
theorem sq_sub_self_even (k : Int) : (k * k - k) % 2 = 0 := by
  obtain ⟨q, r, hk, hr⟩ : ∃ q r : Int, k = 2 * q + r ∧ (r = 0 ∨ r = 1) :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  subst hk
  rcases hr with rfl | rfl
  · have : (2 * q + 0) * (2 * q + 0) - (2 * q + 0) = 2 * (2 * q * q - q) := by grind
    rw [this]; omega
  · have : (2 * q + 1) * (2 * q + 1) - (2 * q + 1) = 2 * (2 * q * q + q) := by grind
    rw [this]; omega

/-- IS3: a non-zero integer has square at least 1. -/
theorem one_le_sq_of_ne_zero {k : Int} (h : k ≠ 0) : 1 ≤ k * k := by
  rcases Int.lt_or_gt_of_ne h with h | h
  · have := Int.mul_pos_of_neg_of_neg h h; omega
  · have := Int.mul_pos h h; omega

theorem sq_nonneg' (k : Int) : 0 ≤ k * k := by
  have := natAbs_le_sq k; omega

variable {V : Type} [DecidableEq V]

/-- Σ|flux| ≤ energy. -/
theorem absFlux_le_energy (c : List (Link V)) : absFlux c ≤ energy c :=
  sumL_le (fun l _ => natAbs_le_sq l.flux)

theorem energy_nonneg (c : List (Link V)) : 0 ≤ energy c :=
  sumL_nonneg (fun l _ => sq_nonneg' l.flux)

end SpiralLattice
