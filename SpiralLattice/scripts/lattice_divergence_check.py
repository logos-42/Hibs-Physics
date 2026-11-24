"""
Checks for the section "From two opposite divergences: a lattice theorem of space".
Strong-coupling (electric) energy on a lattice: H_E = (g^2/2) * sum_links E_l^2, E_l integer,
Gauss law: div E = rho at every site.
"""
import itertools, numpy as np
from scipy.sparse import lil_matrix, csr_matrix, diags
from scipy.sparse.linalg import eigsh

# ---------- Check A: two opposite divergences -> flux string, energy = lattice distance ----------
def grid_links(nx, ny):
    links = []
    for x in range(nx):
        for y in range(ny):
            if x+1 < nx: links.append(((x,y),(x+1,y)))
            if y+1 < ny: links.append(((x,y),(x,y+1)))
    return links
nx = ny = 3
links = grid_links(nx, ny)
sites = [(x,y) for x in range(nx) for y in range(ny)]
idx = {s:i for i,s in enumerate(sites)}
D = np.zeros((len(sites), len(links)), int)      # divergence matrix: out minus in
for l,(a,b) in enumerate(links): D[idx[a],l] += 1; D[idx[b],l] -= 1
confs = np.array(list(itertools.product([-1,0,1], repeat=len(links))), dtype=np.int8)   # 3^12
div = confs @ D.T
energy = (confs.astype(int)**2).sum(1)
print("Check A: source +1 at (0,0), sink -1 at target; minimal sum E^2 and number of minimal configurations")
for tgt in [(1,0),(1,1),(2,1),(2,2)]:
    rho = np.zeros(len(sites), int); rho[idx[(0,0)]] = 1; rho[idx[tgt]] = -1
    ok = np.all(div == rho, axis=1)
    e = energy[ok]; emin = e.min()
    print(f"  target {tgt}: lattice distance {tgt[0]+tgt[1]}, min sum E^2 = {emin}, #ground configs = {(e==emin).sum()}")
ok0 = np.all(div == 0, axis=1)
lv = sorted(set(energy[ok0].tolist()))
print("  no charges (closed loops only), |E|<=1: allowed energy levels =", lv[:8])

# ---------- Check B: closed flux loops = heights on plaquettes; full spectrum of sum E^2 ----------
# planar patch of P x P plaquettes, outside height 0; E on each link = difference of the two adjacent heights
P = 3
def link_pairs(P):
    pairs = []
    for i in range(P):
        for j in range(P):
            p = i*P+j
            for (di,dj) in [(1,0),(0,1),(-1,0),(0,-1)]:
                ii, jj = i+di, j+dj
                if 0 <= ii < P and 0 <= jj < P:
                    q = ii*P+jj
                    if q > p: pairs.append((p,q))
                else:
                    pairs.append((p,-1))   # link on the outer boundary
    return pairs
pairs = link_pairs(P)
H = 2
hs = np.array(list(itertools.product(range(-H,H+1), repeat=P*P)), dtype=np.int8)
def elec(hs):
    e = np.zeros(len(hs), int)
    for p,q in pairs:
        d = hs[:,p].astype(int) - (hs[:,q].astype(int) if q >= 0 else 0)
        e += d*d
    return e
E = elec(hs)
levels, counts = np.unique(E, return_counts=True)
print("\nCheck B: divergence-free integer flux on a 3x3-plaquette patch, |h|<=2")
print("  lowest energy levels (units of g^2/2):", levels[:8].tolist())
print("  odd levels present below 20?", any(l % 2 for l in levels if l < 20))

# ---------- Check C: exact diagonalisation with the magnetic (plaquette) term ----------
# H = (g^2/2) sum E^2 - (1/(2 g^2)) sum_p (U_p + U_p^dagger), U_p shifts h_p by +1
def spectrum(P, g2, H, k=3):
    pairs = link_pairs(P); n = P*P
    states = np.array(list(itertools.product(range(-H, H+1), repeat=n)), dtype=np.int8)
    base = 2*H+1
    code = lambda s: ((s.astype(np.int64)+H) * base**np.arange(n-1,-1,-1)).sum(-1)
    N = len(states)
    diag = np.zeros(N)
    for p,q in pairs:
        d = states[:,p].astype(int) - (states[:,q].astype(int) if q >= 0 else 0)
        diag += 0.5*g2*d*d
    rows, cols = [], []
    for p in range(n):
        up = states.copy(); up[:,p] += 1
        good = up[:,p] <= H
        rows.append(np.nonzero(good)[0]); cols.append(code(up[good]))
    r = np.concatenate(rows); c = np.concatenate(cols)
    off = csr_matrix((np.full(len(r), -1.0/(2*g2)), (r, c)), shape=(N,N))
    Hm = (diags(diag) + off + off.T).tocsr()
    w = eigsh(Hm, k=k, which='SA', return_eigenvectors=False, tol=1e-10)
    w = np.sort(w); return w[1]-w[0]
print("\nCheck C: gap of compact U(1) (2+1 dimensions) with the magnetic term, vs strong-coupling value 2 g^2")
print("  patch  g^2   gap(H=1)  gap(H=2)  gap(H=3)  gap(H=4)  2g^2")
for P, Hs in [(2,(1,2,3,4)), (3,(1,))]:
    for g2 in [4.0, 2.0, 1.0, 0.5]:
        gaps = [spectrum(P, g2, Hc) for Hc in Hs]
        txt = "  ".join(f"{x:8.4f}" for x in gaps) + "  " + "        "*(4-len(gaps))
        print(f"  {P}x{P}   {g2:<4}  {txt}  {2*g2:6.2f}", flush=True)
