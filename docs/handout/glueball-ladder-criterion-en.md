---
title: Glueball Mass Ladder — Criterion Sheet (falsification handout)
date: 2026-11-03
status: draft
audience: lattice QCD collaboration
numbers_source: artifacts/glueball_ladder/report.json (2026-11-01)
scripts: scripts/verify_glueball_ladder_prediction.py
lean: ProjectionPhysics/Explorations/GlueballLadder.lean (LAD1–LAD7, zero sorry)
---

# One number, please

## The single question we are asking

> **Pure-gauge SU(3) lattice: give the mass-level table between 4.0 and 6.5 GeV (position + uncertainty for each confirmed level, J^PC not required), target uncertainty ≤ ±1% (±40 MeV at 4.07 GeV).**

This is worth computing on its own terms: the published systematic spectrum stops at 3.6–3.7 GeV, and above that the region is empty. Whatever number you get is publishable. For us it is a verdict.

## Where the number comes from (a rule, not a fitting freedom)

- Spectrum = ladder: $m = \sqrt{N}\,M_0$, $N = \sum_i n_i^2 + |\bar\mu_3|$, $n_i \in \mathbb{Z}\setminus\{0\}$, $\bar\mu_3 \in \{0,1\}$ only when $\max|n_i| \ge 2$ (variant II, $R=6$).
- $M_0$ has exactly one source: the single anchor state $0^{++}$, one division, $M_0 := m(0^{++})/\sqrt3$.
  - TABLE XXI convention: 1710/√3 = **987.3 MeV**
  - Athenodorou–Teper 2020: 1619/√3 = **934.7 MeV**
  - No per-state recalibration afterwards (that was precisely the old disease: every state got its own private scale, hence zero predictive power).
- Reachable set (R=6) has 78 values of $N$; the only unreachable ones in 3–60 are **4, 5, 8, 16, 32, 40**. **All six are unconditionally unreachable** (machine-checked in Lean: `four/five/eight/sixteen/thirtytwo/forty_not_ladder`) — for 32/40 the bound comes from the equation itself ($n_i^2\le N-2$, so only 5/6 need be enumerated), **independent of the $R$ cut-off**.

## Prediction (TABLE XXI convention; AT2020 in brackets)

**Between 4.0 and 6.5 GeV: 25 levels (28 levels)**

| Quantity | Value |
|---|---|
| First level | 4070.6 MeV (4074.4) |
| Last level | 6474.0 MeV (6476.0) |
| Mean spacing | 1.95% (1.73%) ≈ 100 MeV |
| Minimum spacing | 1.18% (1.06%) ≈ 78 MeV |

## Decision rule (judge by this, not by our prose)

**One correction of our own first.** The ladder is not the integers (3→6→7→9→10→…); it skips. The parameter-free law is therefore

$$s=\sqrt{N_2/N_1}-1,\qquad N_2=\text{the next reachable }N,$$

**not** $\sqrt{(N+1)/N}-1$. At the skipping points the two differ by a factor two (31→33: 3.18% vs 1.60%; 39→41: 2.53% vs 1.27%), and those points lie inside 4.0–6.5 GeV. With the wrong formula a perfect ladder would be killed by our own tolerance.

**Allowed adjacent spacings in 4.0–6.5 GeV (24 values, %):**

1.18, 1.21, 1.31, 1.34, 1.38, 1.42, 1.46, 1.50, 1.65, 1.71, 1.77, 1.84, 1.90, 1.98, 2.06, 2.15, 2.25, 2.35, 2.47, 2.53, 2.60, 2.74, 2.90, 3.18

Level by level (TABLE XXI convention, $M_0=987.3$ MeV):

| $N_1\to N_2$ | $m_1$ (MeV) | spacing | ratio $\sqrt{N_2/N_1}$ |
|---|---|---|---|
| 17→18 | 4071 | 2.90% | 1.0290 |
| 18→19 | 4189 | 2.74% | 1.0274 |
| 19→20 | 4303 | 2.60% | 1.0260 |
| 20→21 | 4415 | 2.47% | 1.0247 |
| 21→22 | 4524 | 2.35% | 1.0235 |
| 22→23 | 4631 | 2.25% | 1.0225 |
| 23→24 | 4735 | 2.15% | 1.0215 |
| 24→25 | 4837 | 2.06% | 1.0206 |
| 25→26 | 4936 | 1.98% | 1.0198 |
| 26→27 | 5034 | 1.90% | 1.0190 |
| 27→28 | 5130 | 1.84% | 1.0184 |
| 28→29 | 5224 | 1.77% | 1.0177 |
| 29→30 | 5317 | 1.71% | 1.0171 |
| 30→31 | 5407 | 1.65% | 1.0165 |
| 31→33 *gap* | 5497 | 3.18% | 1.0318 |
| 33→34 | 5671 | 1.50% | 1.0150 |
| 34→35 | 5757 | 1.46% | 1.0146 |
| 35→36 | 5841 | 1.42% | 1.0142 |
| 36→37 | 5924 | 1.38% | 1.0138 |
| 37→38 | 6005 | 1.34% | 1.0134 |
| 38→39 | 6086 | 1.31% | 1.0131 |
| 39→41 *gap* | 6165 | 2.53% | 1.0253 |
| 41→42 | 6322 | 1.21% | 1.0121 |
| 42→43 | 6398 | 1.18% | 1.0118 |

**Verdict table:**

| Outcome | Verdict |
|---|---|
| every adjacent spacing equals one of the tabulated values (within 20%) and each rung is resolvable | strong support |
| adjacent rungs unresolvable (spacing < 2× error) | no verdict (resolution insufficient) |
| rungs resolvable, but a spacing matches **none** of the tabulated values (> 20% off) | ladder rule dead |
| any pure-gauge level inside one of the three forbidden windows | **independently fatal (the hard test)** |

**Counting levels alone carries no discriminating power.** The random baseline in `report.json` is 100%: any sufficiently dense spectrum yields ≥ 20 levels. A count is only the entry ticket for the spacing test.

**Scope note.** This sheet tests only the *enumeration rule* for $N$ ($N=\sum n_i^2+|\bar\mu_3|$). It does **not** test the mechanism "mass count = sum of squared windings over three directions". If it dies, we learn that the enumeration is wrong; if it lives, the winding story is still untested.

## Precision (read this before agreeing to take it on)

To resolve two adjacent rungs the uncertainty must be ≤ 1/3 of the spacing:

| Region | Adjacent spacing | Required uncertainty | Current published |
|---|---|---|---|
| 4.07 GeV | 118 MeV | **±39 MeV (1.0%)** | — |
| 5.13 GeV | 94 MeV | **±31 MeV (0.6%)** | ±130–150 MeV (3.5–4%) at 3.7 GeV |
| 6.09 GeV | 80 MeV | **±27 MeV (0.4%)** | — |

⟹ This is not a re-check. It demands roughly 12× the statistics plus a finer lattice spacing: order 10³–10⁴ GPU·h.

**One convention must be kept apart.** The "±130–150 MeV at 3.7 GeV" above is the **inter-group spread in a review compilation (systematics included)**, not the statistical error of any single group. If your group is already at 1–2% at that mass, the marginal cost is far below the "12× statistics" estimate — that one assumed a 4% baseline; a 2% baseline needs 4–9×.

**Minimal viable slice** (do this if the full range is too expensive): **3.75–4.15 GeV**, three positions.

| Position | Status | Ratio to 0++ |
|---|---|---|
| 3824 MeV | allowed rung ($N=15$) | 2.2361 |
| **3949 MeV** | **forbidden ($N=16$, unreachable)** | **2.3094** |
| 4071 MeV | allowed rung ($N=17$) | 2.3805 |

0.4 GeV wide, three positions, identical decision rule: **a single level inside the forbidden window kills the rule.**


## Free by-product: three forbidden windows

Judge these in **ratio** form ($m/M_0$), never in MeV — the anchor itself carries ~5% uncertainty, while the N=32/40 windows are only 2.5–3.1% wide.

| Missing N | in units of $M_0$: $\sqrt{N-1}$–$\sqrt{N+1}$ | **ratio to 0++** (judge on this) | Width | TABLE XXI | AT2020 |
|---|---|---|---|---|---|
| 16 | 3.8730 – 4.1231 | **2.2361 – 2.3805** | 6.1% | 3824 – 4071 MeV | 3620 – 3854 MeV |
| 32 | 5.5678 – 5.7446 | **3.2146 – 3.3166** | 3.1% | 5497 – 5671 MeV | 5204 – 5370 MeV |
| 40 | 6.2450 – 6.4031 | **3.6056 – 3.6969** | 2.5% | 6166 – 6322 MeV | 5837 – 5985 MeV |

**Death condition:** one confirmed pure-gauge level **strictly inside** a window ⟹ the reachable set is wrong, the ladder rule dies.

**Two execution details, or this test shoots itself:**

1. Judge on an **open interval with a margin**, never a closed one. The window endpoints $\sqrt{N\mp1}$ are exactly where the model's own adjacent rungs sit (TABLE XXI: the N=17 rung at 4070.6 MeV *is* the upper end of the N=16 window; N=31/33 and N=39/41 likewise sit on the edges). On a closed interval, "a level inside the window" flags our own prediction ⟹ death triggers by construction, independent of any measurement.
2. What survives after a 2σ margin:

| Missing N | Window width | Decidable core at σ=1% | Verdict at current precision |
|---|---|---|---|
| 16 | 6.5% | ≈2.3% | decidable |
| 32 | 3.2% | < 0 | needs σ ≤ 0.6% |
| 40 | 2.5% | < 0 | **not decidable** |

⟹ Only the N=16 window is decidable today; N=32/40 must be labelled "pending" and kept off the death list.

## Four checks already done (don't repeat them)

1. **Integrality of mass ratios — already negative.** $m_p/m_e = 1836.15267343(11)$; the nearest integer 1836 deviates by $8.3\times10^{-5}=1.4\times10^6\sigma$; all denominators $q\le60$ tried, best still off by $1.3\times10^5\sigma$. The "all masses = integer strand count × one unit price" version is dead.
2. **Current-spectrum matching**: strict alignment 5/7 (TABLE XXI; failures $3^{+-}$ −9.0%, $3^{++}$ −6.8%); 5/5 in AT2020 (all ≤2.8%).
3. **Near-degenerate pairs**: the lattice spectrum contains ~2% splittings ($1^{+-}/2^{-+}$, $3^{+-}/3^{++}$) in the 1.6–3.7 GeV region, while the ladder's smallest splitting **in that region** is 3.8% ⟹ √N spacing is not the spectrum's real spacing. This is the model's current structural defect, stated up front so it cannot be mistaken for something hidden.
4. **α-decay prefactor**: framework gives 1.5×10²⁴ s⁻¹ vs the nuclear scale 1.5×10²¹ s⁻¹, a factor 1500 (log 7.31); in Gamow-exponent terms G must be 7.7% smaller, while double-folded potentials carry 5–10% uncertainty on G ⟹ **buried in noise, no verdict**. This one is "marginal", not a test.

## Explicitly no experimental interface (listed so it is not read as an omission)

| Claim | Why no interface |
|---|---|
| Antimatter = reversed flow | C symmetry gives zero net charge; the framework produces no asymmetry, no measurable prediction |
| Decay rates | Missing ~1 MeV nuclear scale (factor 1500), no rate computable |
| 4D gauge structure | Lattice measures spectra, not whether winding equals strand count |
| ALIGN conjecture (colour basis ↔ spatial basis) | Internal-structure assertion, not directly observable |
| J^PC quantum numbers | 256 linear rules exhaustively checked, zero match all 7 states (RT-F) ⟹ **this sheet compares level counts, not J^PC** |

## Four honest boundaries that ship with this sheet

1. $M_0$ remains an input (the framework carries no scale content; ratios cannot output a number in MeV, SC6).
2. The forbidden windows are comparable in width to the lattice uncertainty ⟹ "pending", not "decided".
3. The two conventions give different scores (5/7 vs 5/5) — the model is not yet sharpened to a unique prediction.
4. The old absolute threshold "minimum spacing ≥ 1.1%" is withdrawn: it sat exactly between the two conventions' minima, 1.18% (TABLE XXI) and 1.06% (AT2020), which turned "pick an anchor" into a life-or-death switch. Replaced by the parameter-free law $s=\sqrt{N_2/N_1}-1$ ($N_2$ the next reachable $N$), so both conventions are judged with one ruler.

## How to send it

- Target: IHEP lattice QCD group, or ITP-CAS theory.
- Do not write "please validate our theory". Ask for one number plus one decision line.
- Deliverable: this page + three tables + "≤10 dead / ≥20 alive".

## Internal consistency memo (not for external circulation)

- All MeV values here come from `artifacts/glueball_ladder/report.json` (2026-11-01, TABLE XXI convention, M₀ = 987.27 MeV).
- `verify_glueball_ladder_prediction.py` reports `needed_lattice_err_MeV = 78` under a "spacing/2" convention; this sheet uses "spacing/3" (39/31/27 MeV). **The two conventions disagree and must be unified at the stricter 1/3**, otherwise the decision line is relaxed by our own precision target.
- Difference from `江木复盘笔记/可证伪性实验.md`: that draft asked for "25 independent 0++ levels". Here it is "25 independent mass levels, regardless of J^PC", because J^PC is not derivable and asking for 0++ would put an unpredictable quantity into the criterion.