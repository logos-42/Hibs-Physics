"""
Predictions audit for the flowing-space / spiral-lattice framework.
Data: Athenodorou & Teper, JHEP 11 (2020) 172 [arXiv:2007.06422], Table 14 (continuum M/sqrt(sigma)).
Ratios to 0++ are scale-free, so no choice of sqrt(sigma) or r0 enters.
"""
import numpy as np, itertools, math
rng = np.random.default_rng(2026)

# continuum values (units of sqrt(sigma)) and J^PC reading of the cubic irreps
AT = {"0++": (3.405, 0.021),
      "2++": (None, None),            # average of E++ 4.904(20) and T2++ 4.884(19)
      "0-+": (5.276, 0.045),
      "0++*": (5.855, 0.041),
      "1+-": (6.065, 0.040),
      "2-+": (None, None)}            # average of E-+ 6.211(56) and T2-+ 6.393(45)
def wavg(a, b):
    (x1, s1), (x2, s2) = a, b
    w1, w2 = 1/s1**2, 1/s2**2
    return (w1*x1 + w2*x2)/(w1+w2), (w1+w2)**-0.5
AT["2++"] = wavg((4.904, 0.020), (4.884, 0.019))
AT["2-+"] = wavg((6.211, 0.056), (6.393, 0.045))
spread_2mp = abs(6.393-6.211)  # E vs T2 split: lattice-artefact / rotational-symmetry check
m0, s0 = AT["0++"]
states = ["2++", "0-+", "0++*", "1+-", "2-+"]
ratios = {}
for st in states:
    m, s = AT[st]
    r = m/m0; sr = r*math.hypot(s/m, s0/m0)
    ratios[st] = (r, sr)

print("Scale-free ratios m/m(0++) from AT2020 (Table 14):")
for st in states: print(f"  {st:5s} {ratios[st][0]:.4f} +- {ratios[st][1]:.4f}")
print(f"  (2-+ : E-+ and T2-+ differ by {spread_2mp:.3f} sqrt(sigma) = {spread_2mp/m0:.3f} in ratio)")

# ---------- A. old ladder m = sqrt(N) M0, N = sum n_i^2 (+1 variant II), anchor N(0++)=3 ----------
def reachable(maxN=60, variant_plus1=True):
    S = set()
    R = range(-8, 9)
    for n in itertools.product([k for k in R if k != 0], repeat=3):
        base = sum(k*k for k in n)
        if base <= maxN: S.add(base)
        if variant_plus1 and max(abs(k) for k in n) >= 2 and base+1 <= maxN: S.add(base+1)
    return sorted(S)
LAD = reachable()
rungs = np.array([math.sqrt(N/3) for N in LAD])
print("\nA. Ladder (variant II) reachable N up to 20:", [N for N in LAD if N <= 20])
def chi2_nearest(rs, ss, rungs):
    tot = 0; picks = []
    for r, s in zip(rs, ss):
        i = np.argmin(np.abs(rungs - r)); tot += ((r - rungs[i])/s)**2; picks.append(i)
    return tot, picks
rs = np.array([ratios[s][0] for s in states]); ss = np.array([ratios[s][1] for s in states])
chi_obs, picks = chi2_nearest(rs, ss, rungs)
print("   nearest-rung assignment:")
for st, r, s, i in zip(states, rs, ss, picks):
    print(f"     {st:5s} obs {r:.4f}  ladder N={LAD[i]:2d} -> {rungs[i]:.4f}  pull {(r-rungs[i])/s:+.2f} sigma")
print(f"   chi2 = {chi_obs:.2f} for {len(states)} ratios (no free parameter after anchoring 0++)")
# strict (ascending) assignment as in the repo: k-th state above 0++ <-> k-th rung above N=3
order = np.argsort(rs); strict_rungs = rungs[1:1+len(states)]
chi_strict = sum(((rs[j]-strict_rungs[k])/ss[j])**2 for k, j in enumerate(order))
print(f"   strict ascending assignment: chi2 = {chi_strict:.1f}")
# null model: random spectra with the same errors, uniform over the same window
lo, hi = rs.min()-0.1, rs.max()+0.1
NS = 200000
null = np.empty(NS)
for t in range(NS):
    rr = rng.uniform(lo, hi, size=len(rs))
    d = np.min(np.abs(rr[:, None] - rungs[None, :]), axis=1)
    null[t] = np.sum((d/ss)**2)
p_null = np.mean(null <= chi_obs)
print(f"   null model (uniform random spectra in [{lo:.2f},{hi:.2f}]): P(chi2_null <= chi2_obs) = {p_null:.3f}")
print(f"   median chi2 of random spectra = {np.median(null):.1f}")

# forbidden windows of the ladder inside the measured range
gaps = [(N, math.sqrt((N-1)/3) if (N-1) in LAD else None) for N in range(4, 20) if N not in LAD]
print("   forbidden N in 4..19:", [N for N in range(4, 20) if N not in LAD])
w8 = (math.sqrt(7/3), math.sqrt(9/3))
print(f"   N=8 window (ratio): {w8[0]:.4f} - {w8[1]:.4f};  0++* = {ratios['0++*'][0]:.4f}+-{ratios['0++*'][1]:.4f}, 1+- = {ratios['1+-'][0]:.4f}")

# ---------- B. strong-coupling leading order (new Lean theorems): energy = (g^2/2a) C2 * #links ----------
print("\nB. Strong-coupling leading order (gap_theorem): loop lengths 4,6,8,...; lowest 0++ and 2++ degenerate")
for st in ["2++"]:
    r, s = ratios[st]
    print(f"   {st}: LO predicts ratio 1.000, observed {r:.4f}+-{s:.4f}  -> {(r-1)/s:.0f} sigma")
r, s = ratios["2++"]
print(f"   even if 2++ is put on the 6-link level (ratio 1.5): pull {(r-1.5)/s:+.1f} sigma")

# ---------- C. scale problem: lattice spacing implied by a strong-coupling gap ----------
hbarc = 0.1973269804  # GeV fm
mG = 1.6              # GeV, rough 0++ mass (AT2020: 3.405 sqrt(sigma) with sqrt(sigma) ~ 0.44-0.49 GeV)
CF = 4/3
a_min_fm = 4*CF*0.5*1.0*hbarc/mG    # Delta = 4 links * (g^2/2a) * C_F with g^2 >= 1
print(f"\nC. Strong coupling (g^2>=1) with Delta = m(0++) ~ {mG} GeV requires a >= {a_min_fm:.2f} fm = {a_min_fm*1e-15:.1e} m")
EPl = 1.22089e19  # GeV
EQG2 = 6e-8*EPl   # LHAASO GRB 221009A, quadratic LIV, 95% CL
a_max_m = math.sqrt(12)*hbarc*1e-15/EQG2
print(f"   LHAASO (GRB 221009A) quadratic LIV bound E_QG,2 > 6e-8 E_Pl = {EQG2:.2e} GeV")
print(f"   naive lattice photon dispersion v = c cos(ka/2) => a < sqrt(12) hbar c / E_QG,2 = {a_max_m:.1e} m")
print(f"   tension: required/allowed = {a_min_fm*1e-15/a_max_m:.1e}  (~10^{math.log10(a_min_fm*1e-15/a_max_m):.1f})")

# ---------- D. conditional: Regge slope from a linear potential (Nambu string) ----------
for sq in (0.44, 0.475):
    sigma = sq**2
    print(f"\nD. sqrt(sigma) = {sq} GeV: Nambu string Regge slope alpha' = 1/(2 pi sigma) = {1/(2*math.pi*sigma):.3f} GeV^-2")
