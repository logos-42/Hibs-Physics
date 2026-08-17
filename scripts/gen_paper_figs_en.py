#!/usr/bin/env python3
"""Generate English versions of the paper figures (for the English paper).

leo (2026-08-17): the English paper must have English figure captions/labels.
Output: paper/figures_en/ (fig_triple_rank, fig_tilted_lightcone,
fig_charge_helix, fig_photon_models, fig_photon_turns,
fig_circumference_wavelength).
"""
import os

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = os.path.join(os.path.dirname(__file__), "..", "paper", "figures_en")
os.makedirs(OUT, exist_ok=True)

rng = np.random.default_rng(42)

# ---- 1. fig_triple_rank: Cauchy-Binet identity + rank scan ----
fig, ax = plt.subplots(1, 2, figsize=(12, 4.6))
dets_P, dets_A = [], []
for _ in range(200):
    P = [rng.standard_normal(3) + 1j * rng.standard_normal(3) for _ in range(3)]
    A = np.array(P, dtype=complex)
    dets_P.append(abs(np.linalg.det(sum(np.outer(p, np.conj(p)) for p in P))))
    dets_A.append(abs(np.linalg.det(A)) ** 2)
ax[0].scatter(dets_A, dets_P, s=14, alpha=0.6)
lim = [0, max(max(dets_P), max(dets_A)) * 1.05]
ax[0].plot(lim, lim, "r--", lw=1.2, label="y = x (identity)")
ax[0].set_xlabel(r"$|\det_3[\pi_1\pi_2\pi_3]|^2$")
ax[0].set_ylabel(r"$\det_3(\sum_i \pi_i\otimes\bar\pi_i)$")
ax[0].set_title("GQ2: three-twistor det identity (Cauchy-Binet)")
ax[0].legend(fontsize=8)
ax[0].grid(alpha=0.3)
ts = np.linspace(0, 1, 101)
e1 = np.array([1.0, 0.0, 0.0])
e2 = np.array([0.0, 1.0, 0.0])
e3 = np.array([0.0, 0.0, 1.0])
m2_scan = [abs(np.linalg.det(np.array([e1, e2, (1 - t) * e2 + t * e3]))) ** 2 for t in ts]
ax[1].plot(ts, m2_scan, "b-", lw=1.6)
ax[1].axhline(0, color="k", ls=":", lw=0.8)
ax[1].set_xlabel("t ($\\pi_3$ from degenerate $e_2$ to independent $e_3$)")
ax[1].set_ylabel(r"$m^2 = \det_3(P)$")
ax[1].set_title("GQ5: rank criterion — independent third direction excites")
ax[1].grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_triple_rank.png"), dpi=130)
plt.close(fig)

# ---- 2. fig_tilted_lightcone ----
Tmax = 30
cone_grid = np.zeros((Tmax, Tmax))
for t in range(Tmax):
    for d in range(Tmax):
        if abs(d - 1.5 * t) <= t:
            cone_grid[t, d] = 1
fig, axc = plt.subplots(figsize=(5.6, 4.6))
axc.imshow(cone_grid.T, origin="lower", aspect="auto", cmap="viridis")
axc.set_xlabel("Time t (steps)")
axc.set_ylabel("Rest-frame position d (sites)")
axc.set_title("Tilted light cone: flow v=1.5, equivalent speed 2.5\n"
              "in the flow frame signals stay $\\leq$ 1 per step (local causality)")
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_tilted_lightcone.png"), dpi=130)
plt.close(fig)

# ---- 3. fig_charge_helix ----
th = np.linspace(0, 4 * np.pi, 200)
z = np.linspace(0, 2, 200)
r_plus = 0.3 + 0.6 * z / 2
r_minus = 1.0 - 0.4 * z / 2
fig, axq = plt.subplots(1, 2, figsize=(10, 4.4), subplot_kw={"projection": "3d"})
for ax, r, name in [(axq[0], r_plus, "Positive charge: diverging right-handed helix (source)"),
                    (axq[1], r_minus, "Negative charge: converging right-handed helix (sink)")]:
    ax.plot(r * np.cos(th), r * np.sin(th), z, lw=1.4)
    ax.set_title(name)
    ax.set_xlabel("x"); ax.set_ylabel("y"); ax.set_zlabel("z (axial flow)")
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_charge_helix.png"), dpi=130)
plt.close(fig)

# ---- 4. fig_photon_models ----
tq = np.linspace(0, 4 * np.pi, 300)
rq, om = 0.8, 1.0
fig, axp = plt.subplots(1, 2, figsize=(10, 4.4), subplot_kw={"projection": "3d"})
axp[0].plot(rq * np.cos(om * tq), rq * np.sin(om * tq), tq, lw=1.5, color="tab:blue")
axp[0].set_title("Model A: single excited-electron helix\n(axial speed = c)")
axp[0].set_xlabel("x"); axp[0].set_ylabel("y"); axp[0].set_zlabel("z (propagation)")
axp[1].plot(rq * np.cos(om * tq), rq * np.sin(om * tq), tq, lw=1.2,
            color="tab:red", label="excited electron 1 (+azimuthal)")
axp[1].plot(rq * np.cos(om * tq), -rq * np.sin(om * tq), tq, lw=1.2,
            color="tab:green", ls="--", label="excited electron 2 (-azimuthal)")
axp[1].set_title("Model B: two symmetric helices\n(azimuthal cancellation, massless)")
axp[1].set_xlabel("x"); axp[1].set_ylabel("y"); axp[1].set_zlabel("z")
axp[1].legend(fontsize=8)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_photon_models.png"), dpi=130)
plt.close(fig)

# ---- 5. fig_photon_turns ----
tq2 = np.linspace(0, 6 * np.pi, 400)
fig, axt = plt.subplots(figsize=(5.6, 4.6), subplot_kw={"projection": "3d"})
axt.plot(0.8 * np.cos(tq2), 0.8 * np.sin(tq2), tq2, lw=1.4, color="tab:blue")
axt.set_title("Counting the strands: photon helix\n"
              "each turn = one frequency period = angular momentum h\n"
              r"$E = h\cdot f$ (angular momentum per turn $\times$ turns/s)")
axt.set_xlabel("x"); axt.set_ylabel("y"); axt.set_zlabel("z (propagation)")
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_photon_turns.png"), dpi=130)
plt.close(fig)

# ---- 6. fig_circumference_wavelength ----
h_SI = 6.62607015e-34
hbar_SI = 1.054571817e-34
c_SI = 299792458.0
lam_vis = 500e-9
r_helix = lam_vis / (2 * np.pi)
p_deb = h_SI / lam_vis
hbar_geo = r_helix * p_deb
err = abs(hbar_geo - hbar_SI) / hbar_SI
E_pc = p_deb * c_SI
f_ph = c_SI / lam_vis
E_hf = h_SI * f_ph
fig, axc2 = plt.subplots(1, 2, figsize=(10, 4.4))
axc2[0].plot(np.cos(tq2), np.sin(tq2), lw=1.6, color="tab:blue")
axc2[0].set_aspect("equal")
axc2[0].set_title(f"Helix cross-section (radius r = $\\lambda/2\\pi$ = {r_helix*1e9:.2f} nm)\n"
                  f"circumference 2$\\pi$r = $\\lambda$ = 500 nm")
axc2[0].grid(alpha=0.3)
axc2[1].axis("off")
chain_txt = ("Derivation chain (physical constants)\n"
             f"r = $\\lambda/2\\pi$ = {r_helix*1e9:.2f} nm\n"
             f"circumference 2$\\pi$r = {2*np.pi*r_helix*1e9:.1f} nm = $\\lambda$  ok\n"
             f"p = h/$\\lambda$ = {p_deb:.4e} kg m/s\n"
             f"$\\hbar$ = r*p = {hbar_geo:.4e} J s\n"
             f"measured $\\hbar$ = {hbar_SI:.4e} J s\n"
             f"rel. error = {err:.2e}\n"
             f"E = pc = {E_pc:.4e} J = hf  ok")
axc2[1].text(0.05, 0.95, chain_txt, va="top", fontsize=11, family="monospace",
             bbox=dict(boxstyle="round", facecolor="lightyellow", alpha=0.9))
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_circumference_wavelength.png"), dpi=130)
plt.close(fig)

print("English figures written to", OUT)
for f in sorted(os.listdir(OUT)):
    print(" ", f)
