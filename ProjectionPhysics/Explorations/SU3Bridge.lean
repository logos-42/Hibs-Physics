-- ProjectionPhysics — 3x3 complex matrix and SU(3) bridge
--
-- The project uses an integer-based complex type, so this module does not
-- attempt to build the full continuous Lie group analytically. It does build
-- the matrix-level SU(3) contract and an explicit nontrivial cyclic subgroup
-- represented by determinant-one unitary 3x3 permutation matrices.

import ProjectionPhysics.Archive.Algebra

namespace ProjectionPhysics

structure Mat3 where
  a00 : ℂ
  a01 : ℂ
  a02 : ℂ
  a10 : ℂ
  a11 : ℂ
  a12 : ℂ
  a20 : ℂ
  a21 : ℂ
  a22 : ℂ

theorem Mat3.ext {M N : Mat3}
    (h00 : M.a00 = N.a00) (h01 : M.a01 = N.a01) (h02 : M.a02 = N.a02)
    (h10 : M.a10 = N.a10) (h11 : M.a11 = N.a11) (h12 : M.a12 = N.a12)
    (h20 : M.a20 = N.a20) (h21 : M.a21 = N.a21) (h22 : M.a22 = N.a22) :
    M = N := by
  cases M
  cases N
  cases h00
  cases h01
  cases h02
  cases h10
  cases h11
  cases h12
  cases h20
  cases h21
  cases h22
  rfl

def mat3One : Mat3 :=
  { a00 := 1, a01 := 0, a02 := 0
    a10 := 0, a11 := 1, a12 := 0
    a20 := 0, a21 := 0, a22 := 1 }

def mat3Mul (M N : Mat3) : Mat3 :=
  { a00 := M.a00 * N.a00 + M.a01 * N.a10 + M.a02 * N.a20
    a01 := M.a00 * N.a01 + M.a01 * N.a11 + M.a02 * N.a21
    a02 := M.a00 * N.a02 + M.a01 * N.a12 + M.a02 * N.a22
    a10 := M.a10 * N.a00 + M.a11 * N.a10 + M.a12 * N.a20
    a11 := M.a10 * N.a01 + M.a11 * N.a11 + M.a12 * N.a21
    a12 := M.a10 * N.a02 + M.a11 * N.a12 + M.a12 * N.a22
    a20 := M.a20 * N.a00 + M.a21 * N.a10 + M.a22 * N.a20
    a21 := M.a20 * N.a01 + M.a21 * N.a11 + M.a22 * N.a21
    a22 := M.a20 * N.a02 + M.a21 * N.a12 + M.a22 * N.a22 }

def complexConj (z : ℂ) : ℂ :=
  ⟨z.re, -z.im⟩

def complexSub (x y : ℂ) : ℂ :=
  ⟨x.re - y.re, x.im - y.im⟩

def mat3Adjoint (M : Mat3) : Mat3 :=
  { a00 := complexConj M.a00, a01 := complexConj M.a10, a02 := complexConj M.a20
    a10 := complexConj M.a01, a11 := complexConj M.a11, a12 := complexConj M.a21
    a20 := complexConj M.a02, a21 := complexConj M.a12, a22 := complexConj M.a22 }

def mat3Trace (M : Mat3) : ℂ :=
  M.a00 + M.a11 + M.a22

def mat3Det (M : Mat3) : ℂ :=
  complexSub
    (M.a00 * complexSub (M.a11 * M.a22) (M.a12 * M.a21))
    (M.a01 * complexSub (M.a10 * M.a22) (M.a12 * M.a20)) +
  M.a02 * complexSub (M.a10 * M.a21) (M.a11 * M.a20)

def MatrixUnitary (M : Mat3) : Prop :=
  mat3Mul (mat3Adjoint M) M = mat3One

def MatrixDetOne (M : Mat3) : Prop :=
  mat3Det M = 1

structure SU3Matrix where
  matrix : Mat3
  unitary : MatrixUnitary matrix
  det_one : MatrixDetOne matrix

def su3IdentityMatrix : Mat3 := mat3One

def su3CycleMatrix : Mat3 :=
  { a00 := 0, a01 := 1, a02 := 0
    a10 := 0, a11 := 0, a12 := 1
    a20 := 1, a21 := 0, a22 := 0 }

def su3Cycle2Matrix : Mat3 :=
  { a00 := 0, a01 := 0, a02 := 1
    a10 := 1, a11 := 0, a12 := 0
    a20 := 0, a21 := 1, a22 := 0 }

theorem su3_identity_matrix_unitary : MatrixUnitary su3IdentityMatrix := by
  apply Mat3.ext <;> apply ℂ.ext <;>
    simp [MatrixUnitary, su3IdentityMatrix, mat3One, mat3Adjoint, mat3Mul,
      complexConj]

theorem su3_identity_matrix_det_one : MatrixDetOne su3IdentityMatrix := by
  apply ℂ.ext <;>
    simp [MatrixDetOne, su3IdentityMatrix, mat3One, mat3Det, complexSub] <;> omega

theorem su3_cycle_matrix_unitary : MatrixUnitary su3CycleMatrix := by
  apply Mat3.ext <;> apply ℂ.ext <;>
    simp [MatrixUnitary, su3CycleMatrix, mat3One, mat3Adjoint, mat3Mul,
      complexConj]

theorem su3_cycle_matrix_det_one : MatrixDetOne su3CycleMatrix := by
  apply ℂ.ext <;>
    simp [MatrixDetOne, su3CycleMatrix, mat3Det, complexSub] <;> omega

theorem su3_cycle2_matrix_unitary : MatrixUnitary su3Cycle2Matrix := by
  apply Mat3.ext <;> apply ℂ.ext <;>
    simp [MatrixUnitary, su3Cycle2Matrix, mat3One, mat3Adjoint, mat3Mul,
      complexConj]

theorem su3_cycle2_matrix_det_one : MatrixDetOne su3Cycle2Matrix := by
  apply ℂ.ext <;>
    simp [MatrixDetOne, su3Cycle2Matrix, mat3Det, complexSub] <;> omega

def su3Identity : SU3Matrix :=
  { matrix := su3IdentityMatrix
    unitary := su3_identity_matrix_unitary
    det_one := su3_identity_matrix_det_one }

def su3Cycle : SU3Matrix :=
  { matrix := su3CycleMatrix
    unitary := su3_cycle_matrix_unitary
    det_one := su3_cycle_matrix_det_one }

def su3Cycle2 : SU3Matrix :=
  { matrix := su3Cycle2Matrix
    unitary := su3_cycle2_matrix_unitary
    det_one := su3_cycle2_matrix_det_one }

inductive SU3Element : Type where
  | identity
  | cycle
  | cycle2
  deriving DecidableEq

def su3ElementCombine : SU3Element → SU3Element → SU3Element
  | .identity, g => g
  | g, .identity => g
  | .cycle, .cycle => .cycle2
  | .cycle, .cycle2 => .identity
  | .cycle2, .cycle => .identity
  | .cycle2, .cycle2 => .cycle

def su3MatrixOf : SU3Element → SU3Matrix
  | .identity => su3Identity
  | .cycle => su3Cycle
  | .cycle2 => su3Cycle2

theorem su3_element_matrix_multiplication :
    ∀ g h : SU3Element,
      (su3MatrixOf (su3ElementCombine g h)).matrix =
        mat3Mul (su3MatrixOf g).matrix (su3MatrixOf h).matrix := by
  intro g h
  cases g <;> cases h
  all_goals
    apply Mat3.ext <;> apply ℂ.ext <;>
      simp [su3ElementCombine, su3MatrixOf, su3Identity, su3Cycle,
        su3Cycle2, su3IdentityMatrix, su3CycleMatrix, su3Cycle2Matrix,
        mat3One, mat3Mul]

theorem su3_element_matrix_is_nontrivial :
    (su3MatrixOf .cycle).matrix ≠ (su3MatrixOf .identity).matrix := by
  intro h
  have h01 := congrArg (fun M : Mat3 => M.a01) h
  have h01' : (1 : ℂ) = 0 := by
    simpa [su3MatrixOf, su3Cycle, su3Identity, su3CycleMatrix,
      su3IdentityMatrix, mat3One] using h01
  have h01re := congrArg (fun z : ℂ => z.re) h01'
  simp at h01re

theorem su3_element_cycle_has_order_three :
    su3ElementCombine (su3ElementCombine .cycle .cycle) .cycle = .identity := by
  rfl

/-! ### G2. Adjoint representation contract -/

structure TracelessMat3 where
  matrix : Mat3
  trace_zero : mat3Trace matrix = 0

theorem TracelessMat3.ext {X Y : TracelessMat3}
    (h : X.matrix = Y.matrix) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

def adjointConjugation (g : SU3Element) (X : TracelessMat3) : Mat3 :=
  mat3Mul
    (mat3Mul (su3MatrixOf g).matrix X.matrix)
    (mat3Adjoint (su3MatrixOf g).matrix)

structure SU3AdjointBridge where
  act : SU3Element → TracelessMat3 → TracelessMat3
  act_formula : ∀ (g : SU3Element) (X : TracelessMat3),
    (act g X).matrix = adjointConjugation g X
  act_identity : ∀ X : TracelessMat3, act .identity X = X
  act_combine : ∀ (g h : SU3Element) (X : TracelessMat3),
    act (su3ElementCombine g h) X = act g (act h X)

theorem adjoint_conjugation_trace_zero (g : SU3Element) (X : TracelessMat3) :
    mat3Trace (adjointConjugation g X) = 0 := by
  have h_re := congrArg (fun z : ℂ => z.re) X.trace_zero
  have h_im := congrArg (fun z : ℂ => z.im) X.trace_zero
  simp [mat3Trace] at h_re h_im
  cases g <;>
    apply ℂ.ext <;>
    simp [adjointConjugation, su3MatrixOf, su3Identity, su3Cycle, su3Cycle2,
      su3IdentityMatrix, su3CycleMatrix, su3Cycle2Matrix, mat3One, mat3Mul,
      mat3Adjoint, mat3Trace, complexConj] <;>
    omega

def c3AdjointAction (g : SU3Element) (X : TracelessMat3) : TracelessMat3 :=
  { matrix := adjointConjugation g X
    trace_zero := adjoint_conjugation_trace_zero g X }

theorem c3_adjoint_action_formula (g : SU3Element) (X : TracelessMat3) :
    (c3AdjointAction g X).matrix = adjointConjugation g X := rfl

theorem c3_adjoint_action_identity (X : TracelessMat3) :
    c3AdjointAction .identity X = X := by
  apply TracelessMat3.ext
  apply Mat3.ext <;> apply ℂ.ext <;>
    simp [c3AdjointAction, adjointConjugation, su3MatrixOf, su3Identity,
      su3IdentityMatrix, mat3One, mat3Mul, mat3Adjoint, complexConj]

theorem c3_adjoint_action_combine (g h : SU3Element) (X : TracelessMat3) :
    c3AdjointAction (su3ElementCombine g h) X =
      c3AdjointAction g (c3AdjointAction h X) := by
  apply TracelessMat3.ext
  apply Mat3.ext <;> apply ℂ.ext <;>
    cases g <;> cases h <;>
      simp [c3AdjointAction, adjointConjugation, su3ElementCombine, su3MatrixOf,
        su3Identity, su3Cycle, su3Cycle2, su3IdentityMatrix, su3CycleMatrix,
        su3Cycle2Matrix, mat3One, mat3Mul, mat3Adjoint, complexConj]

def c3AdjointBridge : SU3AdjointBridge :=
  { act := c3AdjointAction
    act_formula := c3_adjoint_action_formula
    act_identity := c3_adjoint_action_identity
    act_combine := c3_adjoint_action_combine }

end ProjectionPhysics
