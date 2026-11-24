/-
SpiralLattice.Postulates — the cleanest postulates of the spiral-divergence lattice.

Physical reading (flowing-space framework, revised):

  P1 (spiral sites).  Space is a lattice of sites.  Every site is a spiral of the flowing
      medium: its radial part is a divergence (an electric charge, an integer), and its
      rotational part is a hidden angle θ ∈ ℝ/2πℤ (the "third direction" of the site).
      Sites come in two chiralities, outward spirals and inward spirals, and neighbouring
      sites have opposite chirality.  Formally: a parity `p : V → Bool` that flips across
      every link (a bipartite lattice).

  P2 (integer flux).  On every link the conjugate of the compact hidden angle is the link's
      electric flux.  Because the angle is compact, the flux is an integer.  In this file this
      is encoded by taking `flux : Int`; the step "compact angle ⟹ integer conjugate" is the
      standard quantum-mechanical fact (spectrum of −i d/dθ on the circle) and is NOT
      formalised here.

  P3 (Gauss law).  The net outflow of flux at every site equals the site's divergence:
      `div c x = ρ x`.

  P4 (strong-coupling energy).  The electric energy of a configuration is
      H_E = (g²/2a) · Σ_links flux².  We work in units of g²/2a, so the energy is
      `energy c = Σ flux²`.  This is the leading term of the Kogut–Susskind Hamiltonian at
      strong coupling; the magnetic (plaquette) term is not included in the theorems.

Honest scope: everything below is a theorem about P1–P4 on a lattice at leading order in
strong coupling.  Nothing here constructs a continuum theory or proves the Clay problem.
-/
import SpiralLattice.ListSum

namespace SpiralLattice

/-- An oriented link of the lattice, from `tail` to `head`, carrying an integer flux (P2). -/
structure Link (V : Type) where
  tail : V
  head : V
  flux : Int
deriving DecidableEq, Repr

variable {V : Type} [DecidableEq V]

/-- Contribution of link `l` to the net outflow at site `x`. -/
def Link.out (l : Link V) (x : V) : Int :=
  (if l.tail = x then l.flux else 0) - (if l.head = x then l.flux else 0)

/-- Lattice divergence (net outflow) of a flux configuration at site `x`. -/
def div (c : List (Link V)) (x : V) : Int := sumL (fun l => l.out x) c

/-- Electric energy in units of g²/2a (P4). -/
def energy (c : List (Link V)) : Int := sumL (fun l => l.flux * l.flux) c

/-- Total absolute flux Σ |flux|. -/
def absFlux (c : List (Link V)) : Int := sumL (fun l => (l.flux.natAbs : Int)) c

/-- Indicator of a region `S`. -/
def ind (S : V → Bool) (x : V) : Int := if S x then 1 else 0

/-- Net flux leaving the region `S`. -/
def netOut (c : List (Link V)) (S : V → Bool) : Int :=
  sumL (fun l => l.flux * (ind S l.tail - ind S l.head)) c

/-- A link crosses the boundary of `S` if exactly one endpoint lies in `S`. -/
def crosses (S : V → Bool) (l : Link V) : Bool := S l.tail != S l.head

/-- P1: the two chiralities alternate — every link joins an outward and an inward spiral. -/
def Bipartite (p : V → Bool) (c : List (Link V)) : Prop :=
  ∀ l ∈ c, p l.tail ≠ p l.head

/-- Two links join the same pair of sites (in either orientation). -/
def sameEnds (l l' : Link V) : Prop :=
  (l.tail = l'.tail ∧ l.head = l'.head) ∨ (l.tail = l'.head ∧ l.head = l'.tail)

/-- A simple lattice: no self-links and no two links between the same pair of sites. -/
def Simple (c : List (Link V)) : Prop :=
  (∀ l ∈ c, l.tail ≠ l.head) ∧ c.Pairwise (fun l l' => ¬ sameEnds l l')

/-- `vs` is a duplicate-free list of sites containing every endpoint of `c`. -/
def Covers (vs : List V) (c : List (Link V)) : Prop :=
  vs.Nodup ∧ ∀ l ∈ c, l.tail ∈ vs ∧ l.head ∈ vs

end SpiralLattice
