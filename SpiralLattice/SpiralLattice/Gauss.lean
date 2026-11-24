/-
SpiralLattice.Gauss — the lattice Gauss law for an arbitrary region (no continuum limit).

  GL1 ★  Σ_{x ∈ S} div(x) = net flux leaving S.
         Exact on any finite graph; a generalisation of the repository's FT1 (`gauss_law_1d`)
         from a 1-D chain to an arbitrary lattice and an arbitrary region.
  GL2    If the only charges are +1 at x and −1 at y, and S contains x but not y,
         then exactly one unit of flux leaves S.
-/
import SpiralLattice.IntSquares

namespace SpiralLattice

variable {V : Type} [DecidableEq V]

theorem out_region (S : V → Bool) (l : Link V) (vs : List V) (hvs : vs.Nodup)
    (ht : l.tail ∈ vs) (hh : l.head ∈ vs) :
    sumL (fun x => if S x then l.out x else 0) vs = l.flux * (ind S l.tail - ind S l.head) := by
  have hpt : ∀ x ∈ vs, (if S x then l.out x else 0) =
      (if l.tail = x then (if S l.tail then l.flux else 0) else 0)
      - (if l.head = x then (if S l.head then l.flux else 0) else 0) := by
    intro x _
    unfold Link.out
    by_cases h1 : l.tail = x <;> by_cases h2 : l.head = x <;> by_cases hS : S x <;>
      simp_all
  rw [sumL_congr hpt, sumL_sub, sumL_ite_eq _ _ hvs, sumL_ite_eq _ _ hvs]
  simp only [ht, hh, ite_true, ind]
  by_cases a : S l.tail <;> by_cases b : S l.head <;> simp [a, b]

/-- GL1 ★ Lattice Gauss law for a region `S`. -/
theorem gauss_region (c : List (Link V)) (vs : List V) (hc : Covers vs c) (S : V → Bool) :
    sumL (div c) (vs.filter S) = netOut c S := by
  rw [sumL_filter]
  unfold div netOut
  have : (fun x => if S x = true then sumL (fun l => l.out x) c else 0)
      = (fun x => sumL (fun l => if S x then l.out x else 0) c) := by
    funext x
    by_cases h : S x
    · simp [h]
    · simp [h, sumL_const_zero]
  rw [this, sumL_comm]
  apply sumL_congr
  intro l hl
  exact out_region S l vs hc.1 (hc.2 l hl).1 (hc.2 l hl).2

/-- GL2: a region containing the source but not the sink emits exactly one unit of flux. -/
theorem netOut_eq_one (c : List (Link V)) (vs : List V) (hc : Covers vs c)
    (x y : V) (hx : x ∈ vs) (hy : y ∈ vs)
    (hρ : ∀ z ∈ vs, div c z = (if x = z then 1 else 0) - (if y = z then 1 else 0))
    (S : V → Bool) (hSx : S x = true) (hSy : S y = false) :
    netOut c S = 1 := by
  rw [← gauss_region c vs hc S, sumL_filter]
  have hpt : ∀ z ∈ vs, (if S z then div c z else 0) =
      (if x = z then (1 : Int) else 0) - (if y = z then (if S y then 1 else 0) else 0) := by
    intro z hz
    rw [hρ z hz]
    by_cases h1 : x = z <;> by_cases h2 : y = z <;> by_cases hS : S z <;> simp_all
  rw [sumL_congr hpt, sumL_sub, sumL_ite_eq _ _ hc.1, sumL_ite_eq _ _ hc.1]
  simp [hx, hy, hSy]

end SpiralLattice
