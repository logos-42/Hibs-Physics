# ProjectionPhysics — Algebraic Emergent Physics

**Physics as a representation of algebra.** Starting from the three axioms of HIBS
(*The Hidden-space Bridge System*, Liu & Xu), this project formalizes — in Lean 4
(core, no mathlib) — the claim that all physical quantities (metric, energy,
momentum, mass, spin) are *necessary representations* of a non-injective
projection π and its kernel ker π, not objects we are free to define.

- **中文版**: [README.zh-CN.md](README.zh-CN.md) · 数学草案细节: [SPEC.md](SPEC.md)
- **Repository**: [github.com/logos-42/Hibs-Physics](https://github.com/logos-42/Hibs-Physics)
- **Source material**: HIBS paper (Liu & Xu) + a six-round derivation dialogue
  with Gemini (archived at `../HIBS/gemini/` in the sibling repository).

---

## 1. The big picture

Hilbert's sixth problem asks for an *axiomatic* derivation of physics. HIBS
postulates a hidden space S whose elements are "hidden numbers", with three axioms:

- **(A1)** There are non-injective projections f : S → R, g : S → iR (no left inverses — information is irreversibly lost under projection).
- **(A2)** S is closed under + and −; multiplication ⊗ and division force the result onto R.
- **(A3)** The square root maps onto the imaginary axis (chiral split into iR⁺ / iR⁻).

The classical complex plane ℂ is then *not* fundamental: it is the observable
slice of S under π (π ∘ ι = id, HIBS Thm 6.5).

**ProjectionPhysics** generalizes this into a research program:

> **Every observable quantity is a function of exactly two objects:**
> the **Image** (a quadratic form Q on π(S)) and the **Kernel** (a scalar
> invariant κ of ker π). There is no third degree of freedom.

If this *Representation Completeness* holds, then — the conjecture goes —
mass is the scalar representation of the kernel, the metric is the bilinear
form induced by Q, momentum is the projection of a multiplicative flow, and
spin/Dirac structure is the Clifford representation of Q. Known physics
(Newton, Maxwell, Schrödinger, Dirac, Einstein) would reappear as limiting
cases, and genuinely new predictions (kernel mass-melting, causal fingerprints)
would follow from the parts of the kernel that standard physics ignores.

---

## 2. The mathematical argument, step by step

### 2.1 Setup (Definitions.lean)

| Concept | Definition | Lean |
|---|---|---|
| Kernel | ker π := { s : S \| π s = 0 } | `KernelOf` |
| Image | im π := { v : V \| ∃ s, π s = v } | `ImageOf` |
| Information conservation | π(σ_S s) = σ_V(π s) (Aut-equivariance) | `InfoPreserving` |
| Observable | constant on observation-equivalence classes | `IsObservable` |
| Null cone | Q(p) = 0 | `OnNullCone` |
| Projection pair | ι : A → S, π : S → A, π ∘ ι = id | `ProjectionPair` |

The projection is deliberately non-injective (A1): different micro-states can
give the same observable value. Everything else is derived from this.

### 2.2 Proven theorems (Kernel.lean, Completeness.lean, Mass.lean)

The following are **fully proved in Lean 4** (compiled, zero `sorry`):

| # | Theorem | Statement | Why it matters |
|---|---|---|---|
| K1 | `kernel_add_closed` | if π preserves +, ker π is closed under + | the kernel is a subspace |
| K2 | `kernel_contains_zero` | π 0 = 0 ⟹ 0 ∈ ker π | the kernel is nonempty |
| K3 | `observables_depend_only_on_image` | π(s_im + s_ker) = π s_im | **the kernel is unobservable** — the foundation of completeness |
| K4 | `nontrivial_kernel_gives_internal_degree` | nontrivial kernel ⟹ ∃ two distinct kernel elements | the kernel carries hidden internal structure (first step of the Null argument) |
| K5 | `left_inverse_of_injective` | injective embedding ⟹ ∃ left-inverse projection | **projections exist because embeddings are injective** (generalizes HIBS Thm 6.5) |
| K6 | `pair_embed_injective` | ProjectionPair ⟹ embedding is injective | dual of K5 |
| C1 | `invariant_factor_through_projection` | every observable I factors as I = J ∘ π | **"Q comes from the Image" made precise** |
| C2 | `invariant_factor_iff` | observable ⟺ factors through π | completeness, equivalently stated |
| C3 | `factor_preserves_add` | I additive ⟹ J additive (morphism on the image) | structure is preserved by factorization |
| M1 | `kernel_mass_zero_on_trivial_kernel` | trivial kernel ⟹ kernel mass normalizable to 0 | **first half of Kernel Null** |
| N1/N2 | `trivial_kernel_iff_no_internal_degree` etc. | trivial kernel ⟺ no internal degree ⟹ no kernel mass | the Null argument chain |
| B1 | `infoLoss_zero_on_observable` | I = J ∘ π ⟹ information loss vanishes on pure observables | energy-as-information-loss is consistent |

**The central proof idea (C1).** An observable is a quantity that cannot
distinguish micro-states with the same π-value. Formally: π s₁ = π s₂ ⟹ I s₁ = I s₂.
Given such an I, define J(v) := I(choose s with π s = v). Then I = J ∘ π follows
by the very property above. So:

> **Everything observable is a function of the projected value π(s).**
> The kernel contributes nothing to what we can see — it can only contribute
> *scalar* degrees of freedom (like dimension), which is exactly what the
> mass conjecture needs.

**The central proof idea (K5).** If ι : S → V is injective, then every v in the
image has a unique preimage; choosing it gives a projection π with π ∘ ι = id.
Projections are not assumed — they are *forced* by the injectivity of embeddings.
This is the general form of HIBS Thm 6.5 (π ∘ ι = id_ℂ).

### 2.3 Draft statements (structures, not yet theorems)

| Draft | Statement | Status |
|---|---|---|
| `RepresentationCompleteness` | I(s) = F(Q(π s), κ(ζ_κ s)) for every observable I; no third freedom | **Q-half proved** (C1); κ-half open (kernel representation theory) |
| `KernelRepresentation` | a scalar that is Image-invisible, Aut(ker)-invariant, rank-independent depends only on dim(ker π) — so mass m = Φ(ker π) is a theorem, not a definition | open |
| `KernelNullTheorem` | kernel capacity → 0 ⟹ projected momentum p lies on the null cone Q(p) = 0 | first half proved (N1/N2); the Q(p)=0 step needs the metric representation |

---

## 3. The physical argument, step by step

The physics is a *mapping* of the algebra onto standard concepts — with the
discipline (insisted on throughout the design dialogue) that **no physical
conclusion may be smuggled into an axiom**. Each physical quantity must be a
*derived representation*, not a definition.

### 3.1 Mass = the scalar representation of the kernel

A state ζ decomposes (relative to π) into an observable part ζ_obs and a kernel
part ζ_κ. Since π(ζ_κ) = 0, the kernel part is invisible to measurement. But it
is not nothing: by K4 a nontrivial kernel carries internal degrees of freedom,
and any scalar invariant of the kernel automorphism group Aut(ker π) can only
depend on dim(ker π) (or its rank) — the conjecture `KernelRepresentation`.
Define:

    m² := κ(ζ_κ)      (κ a kernel invariant)

Then mass is not an input parameter: it is the *residual algebraic information
that the projection cannot export to the observable image*. Photons would be the
states whose kernel component vanishes (m = 0); massive particles are those with
nontrivial kernel content. The proved theorem M1 is the boundary case: a trivial
kernel forces the kernel mass to zero.

### 3.2 Metric = the bilinear form induced by the projection

A projection π induces a quadratic form Q on the image; by polarization
(Jordan–von Neumann) Q gives a unique bilinear form B. The *signature* of B —
whether Minkowski (1,3) or Euclidean (4,0) — is then a property to be proved
from the algebraic structure of S, not assumed. **This is the weakest link of
the program** (see §5): no current derivation produces the minus sign honestly.
The draft `MetricRepresentation` is deliberately absent as a structure until
this is settled.

### 3.3 Momentum = the projection of a multiplicative flow

Define the flow F as iterated application of ⊗ (a multiplicative chain). Then
momentum P := π(F(ζ)) is the projected flow (`Bridges.momentumOf`). If ⊗ is
associative, conservation of P would follow from associativity alone — no
Noether theorem, no spacetime symmetry. This is the algebraic origin of
conservation laws in the program.

### 3.4 Energy = information loss under projection

E := I(ζ) − J(π(ζ)) — the invariant content of ζ that the projection fails to
export (`Bridges.infoLoss`). B1 shows this is consistent: on pure observables
(where I = J ∘ π) the loss vanishes; the loss is carried entirely by the kernel
degrees of freedom.

### 3.5 Spin & the Dirac equation = Clifford representation of Q

A quadratic form of signature (p,q) has a unique Clifford algebra Cℓ(p,q);
γ-matrices and Dirac spinors are *representations* of that algebra, not
primitive objects. Whether A3's chiral square-root split (iR⁺/iR⁻) forces the
Weyl decomposition is the open question `CliffordEmergence`.

### 3.6 The "five bridges" (Bridges.lean)

| Physics | Algebraic definition |
|---|---|
| Invariant | I(ζ) constant under Aut(S) |
| Energy | information loss E = I(ζ) − J(π(ζ)) |
| Momentum | P = π(Flow(ζ)) |
| Mass | m = κ(ζ_κ), κ a kernel scalar invariant |
| Interaction | ζ₁ ⊗ ζ₂ (A2b: result flows to R) |

---

## 4. Relation to the sibling projects

- **HIBS** ([github.com/logos-42/Lean_HIBS](https://github.com/logos-42/Lean_HIBS),
  local `/Users/apple/lean/HIBS/`): the source theory. K5 ↔ HIBS Thm 6.5
  (π ∘ ι = id); `ProjectionPair` is exactly the HIBS embedding–projection pair.
  This project is the *physics program* built on top of HIBS's axioms.
- **DengYu** (`/Users/apple/lean/DengYu/`): formalization of Deng–Hani–Ma,
  *Hilbert's Sixth Problem* (hard spheres → Boltzmann → fluids). The Boltzmann
  collision operator Q has **collision invariants** (1, v, |v|²) — mass,
  momentum, energy — which are precisely the *kernel* of Q. "The kernel
  determines mass" in this project corresponds to "collision invariants
  determine the fluid conservation laws" there; the coarse-graining projection
  (microscopic → macroscopic) is a physical instance of the abstract π here.

---

## 5. Honest assessment (what is NOT claimed)

1. **Drafts are drafts.** `RepresentationCompleteness`, `KernelRepresentation`,
   `KernelNullTheorem` are well-typed *statements* with all assumptions listed;
   Lean guarantees they are coherent, not that they are true. Proving them is
   the research program.
2. **The (1,3) signature is not derived.** Every attempt in the source dialogue
   that "derives" the Minkowski minus sign either smuggles in a continuous
   spacetime (∂_μ), borrows the mass-shell condition, or hand-waves. Until a
   proof exists, the metric representation is honestly absent.
3. **"Derivations" of KG/Schrödinger/Dirac from the axioms are not independent
   derivations.** They presuppose continuous spacetime and the field-theoretic
   framework; they are reformulations, not first-principle results.
4. **Numerology is excluded.** Numerical "matches" of particle mass ratios by
   powers of π (e.g. 6π⁵ ≈ 1836.118) are numerology and are deliberately not
   part of this repository.

---

## 6. Build & verify

```bash
elan override set v4.28.0    # pinned in lean-toolchain
lake build                   # 18 jobs, no errors, no sorry
.lake/build/bin/projphys     # prints the theorem inventory
```

Layout:

```
ProjectionPhysics/
├── SPEC.md                 # detailed math spec (Chinese): theorem inventory, proof status
├── README.md               # this file (English)
├── README.zh-CN.md         # Chinese overview
├── ProjectionPhysics.lean   # root module
├── Main.lean                # executable
└── ProjectionPhysics/
    ├── Definitions.lean     # projection / kernel / image / invariants / quadratic forms
    ├── Kernel.lean          # kernel algebra (K1–K6, all proved)
    ├── Completeness.lean    # invariant factorization (proved) + completeness draft
    ├── Mass.lean            # kernel mass (trivial-kernel case proved) + representation draft
    ├── NullTheorem.lean     # Kernel Null draft + algebraic core
    └── Bridges.lean         # the five bridges (algebraic definitions)
```

## 7. Next steps

1. Polarization identity (Jordan–von Neumann) in core Lean — the first real
   piece of the metric representation.
2. Kernel representation theory: uniqueness of the scalar invariant of
   Aut(ker π) on a finite kernel.
3. Associativity of ⊗ ⟹ algebraic conservation of the projected flow.

---

*Formalized in Lean 4 (core, no mathlib). Proofs: `omega`, `simp`, `rw`,
`ac_rfl`, classical choice. See [SPEC.md](SPEC.md) for the full theorem
inventory and proof-status ledger.*
