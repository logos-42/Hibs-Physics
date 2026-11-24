/-
SpiralLattice.ColourPrecession — where the non-abelian term [A, A] comes from.

When the hidden coordinate of a spiral is a full 3-D rotation (su(2), components in α³),
an anchored point carries a colour charge Q that is dragged by the hidden flow:
    Q̇ = [Q, A_ν] ẋ^ν.
In su(2) components the commutator is the cross product.  The identities below hold in any
commutative ring α (so in particular for real-valued fields).

  CP1 ★★ (precession channel = commutator)  In the Leibniz decomposition of the momentum
         p_μ = m ẋ_μ + ⟨Q, A_μ⟩, the precession term −⟨Q̇, A_μ⟩ supplies exactly the
         commutator term of the field strength:
           ⟨Q, ∂_μA_ν − ∂_νA_μ⟩ − ⟨[Q, A_ν], A_μ⟩ = ⟨Q, ∂_μA_ν − ∂_νA_μ + [A_μ, A_ν]⟩.
  CP2    (colour charge is conserved in magnitude)  ⟨Q, [Q, A]⟩ = 0, so |Q|² is constant.
  CP3    (the colour force does no work)  For antisymmetric F with zero diagonal
         (as F_μν is by construction), Σ_ij v_i F_ij v_j = 0.
  CP4    (Jacobi)  [a,[b,c]] + [b,[c,a]] + [c,[a,b]] = 0 — the hidden rotations form a Lie
         algebra, which is what makes the field strength covariant.
-/
namespace SpiralLattice

/-- A vector in su(2) ≅ α³. -/
structure V3 (α : Type) where
  x : α
  y : α
  z : α

variable {α : Type} [Lean.Grind.CommRing α]

def V3.dot (a b : V3 α) : α := a.x * b.x + a.y * b.y + a.z * b.z

/-- su(2) commutator in components: [a, b] = a × b. -/
def V3.bracket (a b : V3 α) : V3 α :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

def V3.add (a b : V3 α) : V3 α := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def V3.sub (a b : V3 α) : V3 α := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

/-- CP1 ★★ The colour-precession channel produces the commutator term of F. -/
theorem precession_gives_commutator (Q Amu Anu dmuAnu dnuAmu : V3 α) :
    V3.dot Q (V3.sub dmuAnu dnuAmu) - V3.dot (V3.bracket Q Anu) Amu
      = V3.dot Q (V3.add (V3.sub dmuAnu dnuAmu) (V3.bracket Amu Anu)) := by
  cases Q; cases Amu; cases Anu; cases dmuAnu; cases dnuAmu
  simp only [V3.dot, V3.sub, V3.add, V3.bracket]
  grind

/-- Without the precession channel the commutator is missing: the difference is exactly
⟨Q, [A_μ, A_ν]⟩, which is generically non-zero. -/
theorem missing_term_without_precession (Q Amu Anu dmuAnu dnuAmu : V3 α) :
    V3.dot Q (V3.add (V3.sub dmuAnu dnuAmu) (V3.bracket Amu Anu)) - V3.dot Q (V3.sub dmuAnu dnuAmu)
      = V3.dot Q (V3.bracket Amu Anu) := by
  cases Q; cases Amu; cases Anu; cases dmuAnu; cases dnuAmu
  simp only [V3.dot, V3.sub, V3.add, V3.bracket]
  grind

/-- CP2 The precession Q̇ = [Q, A] is orthogonal to Q, so |Q|² is conserved. -/
theorem precession_preserves_norm (Q A : V3 α) : V3.dot Q (V3.bracket Q A) = 0 := by
  cases Q; cases A
  simp only [V3.dot, V3.bracket]
  grind

/-- CP3 An antisymmetric field strength does no work on the particle. -/
theorem force_does_no_work (F : Fin 3 → Fin 3 → α) (v : Fin 3 → α)
    (hanti : ∀ i j, F i j = -F j i) (hdiag : ∀ i, F i i = 0) :
    v 0 * (F 0 0 * v 0 + F 0 1 * v 1 + F 0 2 * v 2)
      + v 1 * (F 1 0 * v 0 + F 1 1 * v 1 + F 1 2 * v 2)
      + v 2 * (F 2 0 * v 0 + F 2 1 * v 1 + F 2 2 * v 2) = 0 := by
  have h00 := hdiag 0; have h11 := hdiag 1; have h22 := hdiag 2
  have h01 := hanti 0 1; have h02 := hanti 0 2; have h12 := hanti 1 2
  grind

/-- CP4 Jacobi identity for the su(2) bracket. -/
theorem jacobi (a b c : V3 α) :
    V3.add (V3.add (V3.bracket a (V3.bracket b c)) (V3.bracket b (V3.bracket c a)))
      (V3.bracket c (V3.bracket a b)) = ⟨0, 0, 0⟩ := by
  cases a; cases b; cases c
  simp only [V3.add, V3.bracket, V3.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

end SpiralLattice
