# ProjectionPhysics — Algebraic Emergent Physics

**Physics as a representation of algebra.** Starting from the three axioms of HIBS
(*The Hidden-space Bridge System*, Liu & Xu), this project formalizes — in Lean 4
(core, no mathlib) — the claim that all physical quantities (metric, energy,
momentum, mass, spin) are *necessary representations* of a non-injective
projection π and its kernel ker π, not objects we are free to define.

- **中文版**: [README.zh-CN.md](README.zh-CN.md) · 数学草案细节: [SPEC.md](SPEC.md)
- **Paper**: [paper/projection-physics.tex](paper/projection-physics.tex) —
  single-column REVTeX preprint (PRD style), 20+ pp; Chinese version:
  [projection-physics-zh.tex](paper/projection-physics-zh.tex); both
  compiled to PDF via tectonic. §8 covers four recent explorations
  (spin emergence, double-slit as space-helix interference, fractal cosmos
  with the KBC void, glueball three-direction coupling).
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
| A1–A4 | `comp_additive`, `comp_assoc`, `matMul_assoc`, `matMul_add_right` | End(S) is a ring; 2×2 complex matrix multiplication is associative & distributive | **matrix arithmetic emerges from composition** (A2a ⟹ additive group ⟹ endomorphism ring ⟹ matrices) |
| C1–C5 | `sigma*_sq`, `sigma*_anticommute`, `i_emerges_from_clifford`, `sigma3_from_sigma1_sigma2`, `spinor_rep_hom` | σᵢ² = I; σᵢσⱼ+σⱼσᵢ = 0; **(σ₁σ₂)² = −1**; σ₃ = i·σ₁σ₂; (MN)ψ = M(Nψ) | **spin from Clifford**: the imaginary unit i emerges from anticommutation — ℂ is not primitive, exactly as HIBS claims |
| C6 | `sigma1_sigma2_eq` … `sigma3_sigma2_eq` (×6) | σᵢσⱼ = δᵢⱼI − iεᵢⱼₖσₖ | **complete 9-entry multiplication table** of the Clifford generators |
| L1 | `cVecSpace`, `intVecSpace` | VecSpace axioms; ℂ is a 2-dim real vector space, Int is 1-dim | the vector structure of the hidden space |
| L2 | `reProj_linear` | Re : ℂ → Int preserves + and scalar mult | the linear map (HIBS f : S → R) |
| L3 | `kernel_smul_closed`, `kernel_is_subspace` | kernel closed under scalar multiplication | completes K1 (kernel is a subspace) |
| L4 | `complexBasisInst`, `kerReBasisInst`, `imReBasisInst` | bases {1,i} of ℂ, {i} of ker(Re), {1} of im(Re) | spanning + linear independence |
| L5 | `rank_nullity_complex_re` | **dim ℂ = dim ker(Re) + dim im(Re) = 1+1** | ★ **rank-nullity instance: the imaginary axis iR is the kernel of the real-part projection** — the iR of HIBS A3, made precise |
| L6 | `polarization`, `quad_zero` | 2B(x,y) = Q(x+y) − Q(x) − Q(y); Q(0) = 0 | ★ polarization identity: the metric is determined by the quadratic form (heart of Metric Representation) |
| H1–H5 | `projection_generates_state` … `direction_emerges_from_projection` | state-less vectors via Option tags; **projection generates state** (state = observed value); different projections give different states (Re vs Im on cI); idempotent projection Π = ι∘Re (kernel = imaginary axis); direction = Re·1 + Im·i | **the hidden space**: "no state" = `observed = none`; "collapse" = the Option none → some v transition; the algebraic skeleton of quantum measurement |
| Q1–Q7 | `quat_i_sq` … `cliffordHiddenUnit` | **i² = j² = k² = ijk = -1 from Clifford anticommutation**; Φ: ℍ ⊂ Mat2 = Cℓ(3) (ring homomorphism); ℂ ⊂ ℍ; HiddenUnit instances (ℍ ring + Mat2 matrices) | **quaternions as comparison object**: the hidden space, if it has internal multiplication, necessarily produces non-commutative structure (ij ≠ ji) — not a new axiom, a necessary representation |
| PA1–PA6 | `comp_of_commuting_projections_is_projection` … `pvm_skeleton` | projection = idempotent endomap (P²=P); complementary projection pair (idempotent/orthogonal/complete); composition table re∘re=re, re∘im=0, … = **semigroup**; **semigroup, not group** (Π_re not injective); PVM skeleton | ★ **hidden projection algebra (main line)**: the first principle of the hidden space is P² = P (state generation mechanism), **not** i² = -1; determinism comes from information loss (K3) |
| PA7 | `cI_sq_neg_one`, `kernel_mul_leaks_to_image`, `kernelLeak_i` | **kernel not closed under multiplication**: i·i = -1, Re(i²) = -1 ≠ 0 | ★ **kernel mass-melting**: the kernel is an additive subspace (K1) but not a multiplicative ideal — the algebraic prototype of "Goldstone eaten" and mass emerging from the kernel |
| PA8 | `cKernelBiForm`, `kernelBiForm_quad_kernel`, `kernelBiForm_nondegenerate` | bilinear form on the kernel B(x,y) = Im(x)·Im(y); quadratic form Q(k) = κ(k) = kernelInvC; nondegenerate on ker | ★ **kernel tensorization**: the (0,2) tensor on ker π — first physical link m² = κ(ζ_κ) as a kernel metric |

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
lake build                  # ~4140 jobs, no errors, no sorry/admit
make test                   # canonical gate: lake build + 8 verify scripts
                            #   + regression assertions (all reports in artifacts/)
make fast                   # gate without re-running the numeric scripts
python3 scripts/wiki_check.py   # wiki integrity (links + frontmatter)
```

Layout:

```
ProjectionPhysics/
├── SPEC.md                 # detailed math spec (Chinese): theorem inventory, proof status
├── README.md               # this file (English)
├── README.zh-CN.md         # Chinese overview
├── paper/                  # 2026-08-14: first paper (REVTeX 4.2, single-column preprint)
│   ├── projection-physics.tex    # English version (20 pp, tectonic-compiled PDF included)
│   ├── projection-physics-zh.tex # Chinese version (content-equivalent)
│   └── projection-physics.bib    # references (18 real entries)
├── ProjectionPhysics.lean   # root module
├── Main.lean                # executable
├── Makefile                 # canonical test command (make test → verify_all.py)
├── scripts/                 # verification & visualization (8 verify_*.py in gate)
│   ├── verify_all.py            # unified gate (lake build + zero-sorry scan + scripts + assertions)
│   ├── verify_maxwell_space.py  # electromagnetic = kinematics of C (MS1–MS5)
│   ├── verify_spacefield3d.py   # 3D vector calculus: div(curl C)=0 automatic (SF1–SF5)
│   ├── verify_spin_from_space.py# spin = emergence of three-direction structure (SFS1–SFS5)
│   ├── verify_fractal_flow.py   # fractal cosmos: KBC void + Hubble tension (δ* = −0.25)
│   ├── verify_double_slit.py    # double-slit = space-helix harmonics (DS1–DS4)
│   ├── verify_glueball_coupling.py # glueball 3-dir coupling + massification (GC1–GC4)
│   ├── verify_maxwell_flow.py   # Maxwell × flow postulates (MF1–MF6, P1–P4)
│   ├── verify_entanglement_helix.py # CHSH local bound (EH1–EH4)
│   ├── verify_blackhole_wormhole.py # Gordon black hole / wormhole (BH1–WH1)
│   └── wiki_check.py            # wiki integrity
└── ProjectionPhysics/                    # 主线 + 探索（见 README 正文）
    ├── SpaceLightSpeed.lean     # ★ main line: vector light speed — c = space's own
    │                            #   equivalent velocity; photon=comoving⟹m=0; electron=spin⟹m>0 (SLS1–SLS6)
    ├── SpaceMetric.lean         # ★ main line: space-flow metric — dτ²=dt²−dx²/c²; photon
    │                            #   dx=c·dt ⟹ dτ=0 (no time); mass=deviation ⟹ dτ>0 (SM1–SM6)
    ├── SpaceGravity.lean        # ★ main line: GR from momentum conservation — Gordon metric
    │                            #   g=[[1−v²/c²,v/c²],[v/c²,−1/c²]]; Φ=½v² matches weak-field GR (SG1–SG11)
    ├── RelativityDeviation.lean # main line: velocity-difference term — (c−v)/(1−cv/c²)=c;
    │                            #   γ²(u)=1/(2u/c−u²/c²) (RD1–RD7)
    ├── LorentzRebuild.lean      # main line (mathlib): boost preserves Minkowski η; rapidity
    │                            #   additivity; velocity addition; β<1 (LR1–LR5)
    ├── PauliMathlib.lean        # main line (mathlib): Clifford rewrite (C1'–C4')
    ├── DiracMathlib.lean        # main line (mathlib): Dirac bridge — γ⁰²=1, γⁱ²=−1;
    │                            #   mass=chiral coupling (DB1'–DB6')
    ├── MinimalCoreMathlib.lean  # main line (mathlib): mass=anchoring — m²=|ψ₁|²+|ψ₀|²;
    │                            #   nonzero spinor ⟹ m>0 (MC1'–MC6')
    ├── Explorations/            # 探索线（2026-08-14 后活跃）：新方向结果
    │   ├── EntanglementHelix.lean    # CHSH local bound (EH1–EH4)
    │   ├── BlackHoleWormhole.lean    # Gordon black hole / wormhole (BH1–WH1)
    │   ├── MaxwellFlow.lean          # Maxwell × flow postulates (MF1–MF6, PH1–PH2)
    │   ├── MaxwellSpace.lean         # EM = kinematics of C (MS1–MS5)
    │   ├── SpaceField3D.lean         # 3D vector calculus (SF1–SF5)
    │   ├── SpinFromSpace.lean        # spin = 3-direction emergence (SFS1–SFS5)
    │   ├── DoubleSlit.lean           # double-slit = helix harmonics (DS1–DS4)
    │   ├── GlueballCoupling.lean     # glueball 3-dir coupling (GC1–GC4)
    │   ├── SpinStatistics.lean       # spin-statistics hard constraint (SS1–SS8)
    │   ├── CliffordSix.lean          # Cℓ(6) 8-dim representation (CS1–CS3)
    │   ├── ColorOctetMathlib.lean    # 3⊗3=8⊕1 trace decomposition (CM1–CM3)
    │   ├── SphericalHarmonics.lean   # glueball force = spherical harmonics (SH1–SH5)
    │   ├── SU3Bridge.lean            # SU(3) cyclic subgroup
    │   └── GlueballBridge.lean       # SU(3) color action, glueball mass
    └── Archive/                 # deprecated (pre-08-06 hidden-number line + core dual-track):
                                # Definitions/Kernel/Completeness/Mass/NullTheorem/Bridges/
                                # Algebra/Clifford/LinearAlgebra/Differential/SymmetryBreaking/
                                # HiddenSpace/Quaternion/ProjectionAlgebra/HiddenSpacePhysics/
                                # HIBSPhysicalBridges/HiddenOnlyHiggs/HiddenHiggsFlowInterface/
                                # HiddenAxisConversions/HiddenMassTimeEvents/HiddenEventClocks/
                                # FlowConservation/DiracBridge/MinimalCore
```

## 7. Next steps

1. **Kernel representation theory**: uniqueness of the scalar invariant of
   Aut(ker π) — the missing half of mass (D2).
2. **Metric signature (D4)**: the weakest link; no honest derivation of the
   Minkowski minus sign exists yet.
3. **The "second input"** (deepest open problem): the origin of ℏ, e, M₀,
   and the electron's choice of the 2-dim representation — all remain
   inputs, not consequences (see paper §9).
4. **Continuum 3D calculus**: the discrete 3D curl/divergence identities
   (SF1–SF5) are formalized; the continuum version and continuity remain
   open.
5. **Falsifiable exits from reinterpretation**: inhomogeneous-flow Lorentz
   violation; lattice checks of the glueball √N·M₀ higher channels
   (n = 4, 5, 6).

---

*Formalized in Lean 4 (core, no mathlib). Proofs: `omega`, `simp`, `rw`,
`ac_rfl`, classical choice. See [SPEC.md](SPEC.md) for the full theorem
inventory and proof-status ledger.*
