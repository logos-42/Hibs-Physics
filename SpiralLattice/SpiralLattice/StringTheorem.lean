/-
SpiralLattice.StringTheorem — two opposite divergences are joined by a flux string.

  ST1    For one region, the net outflow is bounded by the absolute flux on the links
         crossing its boundary.
  ST2 ★★ (cut bound) If R regions each emit one unit of flux and no link crosses more than
         one of their boundaries, then Σ|flux| ≥ R, hence energy ≥ R.

On the hypercubic lattice (file `Hypercubic`) the R regions are the half-spaces between the
two charges, R is their Manhattan distance, and ST2 becomes the string theorem:
energy ≥ distance, i.e. a linear potential V(R) ≥ (g²/2a)·R at strong coupling.
-/
import SpiralLattice.Gauss

namespace SpiralLattice

variable {V : Type} [DecidableEq V]

/-- ST1: per-link bound used for one region. -/
theorem link_net_le (S : V → Bool) (l : Link V) :
    l.flux * (ind S l.tail - ind S l.head) ≤
      (l.flux.natAbs : Int) * (if crosses S l then 1 else 0) := by
  unfold ind crosses
  by_cases a : S l.tail <;> by_cases b : S l.head <;> simp [a, b] <;> omega

theorem netOut_le (c : List (Link V)) (S : V → Bool) :
    netOut c S ≤ sumL (fun l => (l.flux.natAbs : Int) * (if crosses S l then 1 else 0)) c :=
  sumL_le (fun l _ => link_net_le S l)

/-- ST2 ★★ Cut bound. -/
theorem cut_bound (c : List (Link V)) (Ss : List (V → Bool))
    (hnet : ∀ S ∈ Ss, netOut c S = 1)
    (hdisj : ∀ l ∈ c, (Ss.filter (fun S => crosses S l)).length ≤ 1) :
    (Ss.length : Int) ≤ absFlux c := by
  have h1 : (Ss.length : Int) = sumL (fun S => netOut c S) Ss := by
    rw [sumL_congr (fun S hS => hnet S hS), sumL_const_one]
  have h2 : sumL (fun S => netOut c S) Ss ≤
      sumL (fun S => sumL (fun l => (l.flux.natAbs : Int) * (if crosses S l then 1 else 0)) c) Ss :=
    sumL_le (fun S _ => netOut_le c S)
  rw [sumL_comm] at h2
  have h3 : ∀ l ∈ c,
      sumL (fun S => (l.flux.natAbs : Int) * (if crosses S l then 1 else 0)) Ss
        ≤ (l.flux.natAbs : Int) := by
    intro l hl
    rw [sumL_mul_left, sumL_ite_one_eq_length]
    have := hdisj l hl
    have h0 : (0 : Int) ≤ (l.flux.natAbs : Int) := by omega
    have : ((Ss.filter (fun S => crosses S l)).length : Int) ≤ 1 := by exact_mod_cast this
    calc (l.flux.natAbs : Int) * ((Ss.filter (fun S => crosses S l)).length : Int)
        ≤ (l.flux.natAbs : Int) * 1 := Int.mul_le_mul_of_nonneg_left this h0
      _ = (l.flux.natAbs : Int) := by omega
  have h4 := sumL_le h3
  unfold absFlux
  omega

/-- ST2 in energy form. -/
theorem cut_bound_energy (c : List (Link V)) (Ss : List (V → Bool))
    (hnet : ∀ S ∈ Ss, netOut c S = 1)
    (hdisj : ∀ l ∈ c, (Ss.filter (fun S => crosses S l)).length ≤ 1) :
    (Ss.length : Int) ≤ energy c :=
  Int.le_trans (cut_bound c Ss hnet hdisj) (absFlux_le_energy c)

end SpiralLattice
