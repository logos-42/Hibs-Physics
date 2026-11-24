"""
The framework's gravity functional (GCA2) applied to an ionic crystal.
Sites of a cubic lattice carry divergences q = +-1 (sources/sinks); each makes the radial flow
q r/|r|^3.  Q_A = sum over sample points in region A of |C - mean C|^2.
eta = 1 - Q_A(crystal)/Q_A(disordered), where 'disordered' = the same ions on the same sites with
randomly permuted signs (a frozen 'solution').  Under MUFC/AMC1 (one step) the weight of the
crystal relative to the solution would be (1 - eta).
Two sampling schemes are shown because the result depends on where Q_A is evaluated.
"""
import numpy as np
rng = np.random.default_rng(7)
L = 10
g = np.arange(L)
X, Y, Z = np.meshgrid(g, g, g, indexing='ij')
sites = np.stack([X.ravel(), Y.ravel(), Z.ravel()], 1).astype(float)
q_cry = np.where((X + Y + Z).ravel() % 2 == 0, 1.0, -1.0)   # rock-salt alternation
QA = lambda C: np.sum((C - C.mean(0)) ** 2)
def run(P, label):
    d = P[:, None, :] - sites[None, :, :]
    r = np.linalg.norm(d, axis=2)
    W = d / (r ** 3)[:, :, None]
    flow = lambda q: np.einsum('psk,s->pk', W, q)
    Qc = QA(flow(q_cry))
    Qr = np.array([QA(flow(rng.permutation(q_cry))) for _ in range(20)])
    eta = 1 - Qc / Qr.mean()
    print(f"{label:38s} eta = {eta:.3f}  -> naive weight change crystal vs solution ~ {100*eta:.0f}%")
c = np.arange(3, L - 4) + 0.5
run(np.stack(np.meshgrid(c, c, c, indexing='ij'), -1).reshape(-1, 3), "cell centres (symmetric points)")
P = rng.uniform(3, L - 4, size=(2000, 3))
P = P[np.linalg.norm(P[:, None, :] - sites[None], axis=2).min(1) > 0.25]
run(P, "random points (0.25 a away from ions)")
