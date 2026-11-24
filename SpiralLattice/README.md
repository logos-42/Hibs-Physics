# SpiralLattice — dependency-free Lean 4 package (v1.7 of paper3)

Strong-coupling lattice theorems for the spiral-divergence reading of the flowing-space
framework.  **Lean 4.36 core only — no Mathlib.**  Full build ≈ 3 s.

```bash
cd SpiralLattice
lake build                 # builds all modules
lake env lean Audit.lean   # prints the axioms of every main theorem
```

Every main theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
There is no `sorry`, `admit`, `native_decide` or custom `axiom` in the package.

## Postulates (`SpiralLattice/Postulates.lean`)

| | Postulate | Encoding |
|---|---|---|
| P1 | Every site is a spiral: integer divergence (charge) + compact hidden angle; outward and inward spirals alternate | `Bipartite p c` |
| P2 | Link flux is the conjugate of the compact angle, hence an integer | `flux : Int` (the step "compact ⟹ integer" is input, **not formalised**) |
| P3 | Gauss law: net outflow at a site = its divergence | `div c x = ρ x` |
| P4 | Strong-coupling energy H_E = (g²/2a) Σ flux² | `energy c` (units of g²/2a) |

## Theorems

| ID | Statement | Lean name | File |
|---|---|---|---|
| GL1 | Lattice Gauss law for any region of any finite graph | `gauss_region` | `Gauss.lean` |
| GL2 | Charges ±1 only ⟹ a region with the source but not the sink emits exactly 1 | `netOut_eq_one` | `Gauss.lean` |
| ST2 | R regions each emitting 1, no link crossing two boundaries ⟹ energy ≥ R | `cut_bound_energy` | `StringTheorem.lean` |
| HC1 | **String theorem** on ℤ^d: energy ≥ Manhattan distance of the charges | `string_theorem` | `Hypercubic.lean` |
| HC2 | A straight string attains equality (R = 3 example) | `string_attained` | `Hypercubic.lean` |
| GP1 | Alternating chiralities ⟹ divergence-free flux has even energy | `energy_even` | `GapTheorem.lean` |
| GP2 | Non-zero divergence-free flux on a simple lattice uses ≥ 3 links | `energy_ge_three` | `GapTheorem.lean` |
| GP3 | **Gap theorem**: energy ∈ {0} ∪ {4, 6, 8, …} | `gap_theorem` | `GapTheorem.lean` |
| GP4 | One plaquette attains 4 | `gap_attained` | `GapTheorem.lean` |
| CP1 | Colour precession supplies exactly the [A, A] term of F (any commutative ring) | `precession_gives_commutator` | `ColourPrecession.lean` |
| CP2 | Precession preserves the colour-charge norm | `precession_preserves_norm` | `ColourPrecession.lean` |
| CP3 | The colour force does no work | `force_does_no_work` | `ColourPrecession.lean` |
| CP4 | Jacobi identity of the su(2) bracket | `jacobi` | `ColourPrecession.lean` |

## Scope (honest boundary)

Leading order in strong coupling, on a lattice, finite volume, integer (U(1)-type) flux.
Not included: the magnetic term's dynamics, weak coupling, the continuum limit, SU(3), the
step "compact ⟹ integer".  The physics of HC1/GP3 is classical lattice gauge theory
(Wilson 1974; Kogut–Susskind 1975; Osterwalder–Seiler 1978; Münster 1981); what is new is
the dependency-free formalisation and the spiral-divergence reading.  **This is not a proof of
the Clay Yang–Mills problem.**

## Scripts (`scripts/`)

| Script | What it checks |
|---|---|
| `nonabelian_flow_check.py` | holonomy = exp(a²F) with [A,A]; gauge covariance; Wong trajectories independent of hidden labelling only with precession + [A,A] |
| `lattice_divergence_check.py` | exhaustive enumeration of the string and gap theorems; exact diagonalisation of 2+1D compact U(1) |
| `predictions_audit.py` | glueball ratios vs ladder and strong coupling (Athenodorou–Teper 2020), null-model p-value, scale problem vs LHAASO bound |

Authors of v1.7 additions: Love, with Claude (Anthropic).
