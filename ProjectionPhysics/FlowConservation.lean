-- ProjectionPhysics — compositional Flow and conditional momentum conservation
--
-- Associativity/compositionality gives an unambiguous discrete Flow chain.
-- Conservation is a separate invariant condition and is therefore explicit.
-- This module does not introduce time, Hilbert-space operators, or a quantum
-- uncertainty relation.

import ProjectionPhysics.Bridges

namespace ProjectionPhysics

/-! ### Discrete Flow chains -/

/-- The n-step iterate of a state-space Flow. -/
def flowIterate {S : Type} (flow : S → S) : Nat → S → S
  | 0 => fun s => s
  | n + 1 => fun s => flow (flowIterate flow n s)

theorem flowIterate_zero {S : Type} (flow : S → S) (s : S) :
    flowIterate flow 0 s = s := by
  rfl

theorem flowIterate_succ {S : Type} (flow : S → S) (n : Nat) (s : S) :
    flowIterate flow (n + 1) s = flow (flowIterate flow n s) := by
  rfl

/-- Iterated Flow has the expected additive composition law.
    This is a semigroup-action law, not idempotence. -/
theorem flowIterate_add {S : Type} (flow : S → S) (m n : Nat) (s : S) :
    flowIterate flow (m + n) s =
      flowIterate flow m (flowIterate flow n s) := by
  induction m with
  | zero => simp [flowIterate]
  | succ m ih =>
      simp [Nat.succ_add, flowIterate, ih]

/-! ### Conservation as an explicit invariant -/

/-- A quantity is conserved by a discrete Flow when it is unchanged by one step. -/
def flowMomentumInvariant {S V : Type}
    (flow : S → S) (momentum : S → V) : Prop :=
  ∀ s, momentum (flow s) = momentum s

/-- One-step invariance propagates to every finite Flow iterate. -/
theorem flowIterate_preserves_invariant {S V : Type}
    (flow : S → S) (momentum : S → V)
    (h : flowMomentumInvariant flow momentum) :
    ∀ n s, momentum (flowIterate flow n s) = momentum s := by
  intro n
  induction n with
  | zero =>
      intro s
      rfl
  | succ n ih =>
      intro s
      rw [flowIterate_succ]
      rw [h]
      exact ih s

/-- The existing `momentumOf = π ∘ Flow` becomes conserved only after the
    projected-flow invariance is supplied as a separate hypothesis. -/
theorem momentumOf_iterate_invariant {S V : Type}
    (π : S → V) (flow : S → S)
    (h : flowMomentumInvariant flow (momentumOf π flow)) :
    ∀ n s,
      momentumOf π flow (flowIterate flow n s) = momentumOf π flow s := by
  exact flowIterate_preserves_invariant flow (momentumOf π flow) h

end ProjectionPhysics
