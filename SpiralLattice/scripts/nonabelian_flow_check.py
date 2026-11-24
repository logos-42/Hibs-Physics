"""
Numerical checks for the note "Deriving a non-abelian gauge field from flowing space".
Convention: su(2) basis T_a = -i sigma_a / 2 (anti-Hermitian), [T_a, T_b] = eps_abc T_c.
Components: X^a = -2 tr(X T_a);  <X, Y> = sum_a X^a Y^a.
"""
import numpy as np
from scipy.linalg import expm, logm, expm_frechet
from scipy.integrate import solve_ivp

sig = [np.array([[0,1],[1,0]],complex), np.array([[0,-1j],[1j,0]],complex), np.array([[1,0],[0,-1]],complex)]
T = [-0.5j*s for s in sig]
def mat(v): return sum(v[a]*T[a] for a in range(3))
def comp(X): return np.array([(-2*np.trace(X@T[a])).real for a in range(3)])

rng = np.random.default_rng(7)
# smooth hidden-direction flow field A_i^a(x) = c0 + c1.x + amplitude*sin(k.x + phi), 3 space dims
C0 = rng.normal(size=(3,3)); C1 = rng.normal(size=(3,3,3))*0.5
K = rng.normal(size=(3,3,3)); PHI = rng.uniform(0,2*np.pi,size=(3,3)); AMP = rng.normal(size=(3,3))*0.8
def A_comp(x):          # shape (i, a)
    return C0 + np.einsum('iak,k->ia', C1, x) + AMP*np.sin(np.einsum('iak,k->ia', K, x)+PHI)
def dA_comp(x):         # shape (j, i, a) = d_j A_i^a
    ph = np.einsum('iak,k->ia', K, x)+PHI
    return np.einsum('iaj->jia', C1) + np.einsum('ia,iaj->jia', AMP*np.cos(ph), K)
def F_comp(x, with_comm=True):   # shape (i, j, a)
    A = A_comp(x); dA = dA_comp(x)
    F = np.einsum('ija->ija', dA.transpose(1,0,2)) * 0
    for i in range(3):
        for j in range(3):
            F[i,j] = dA[i,j] - dA[j,i] + (np.cross(A[i],A[j]) if with_comm else 0)
    return F

# ---------- Check 1: holonomy of a small loop = exp(a^2 F) with the commutator term ----------
print("Check 1: holonomy around a small square (plane x0-x1) vs field strength")
x0 = np.array([0.3,-0.2,0.5]); e = np.eye(3)
for a in [0.1, 0.05, 0.025, 0.0125]:
    U = lambda x, mu: expm(a*mat(A_comp(x + 0.5*a*e[mu])[mu]))
    P = U(x0,0) @ U(x0+a*e[0],1) @ np.linalg.inv(U(x0+a*e[1],0)) @ np.linalg.inv(U(x0,1))
    L = comp(logm(P))/a**2
    xc = x0 + 0.5*a*(e[0]+e[1])
    Fw = F_comp(xc, True)[0,1]; Fn = F_comp(xc, False)[0,1]
    print(f"  a={a:<7} |log(P)/a^2 - F(with [A,A])| = {np.linalg.norm(L-Fw):.2e}   |... - F(no [A,A])| = {np.linalg.norm(L-Fn):.2e}")

# ---------- gauge transformation (relabelling the hidden fibre point by point) ----------
G0 = rng.normal(size=3); G1 = rng.normal(size=(3,3))*0.7
def Theta(x): return mat(G0 + G1@x + 0.5*np.sin(x))
def dTheta(x, i): return mat(G1[:,i] + 0.5*np.cos(x[i])*np.eye(3)[i])
def g(x): return expm(Theta(x))
def dg(x, i): return expm_frechet(Theta(x), dTheta(x,i), compute_expm=False)
def Aprime_comp(x):
    gx = g(x); gi = np.linalg.inv(gx); A = A_comp(x)
    return np.array([comp(gx@mat(A[i])@gi - dg(x,i)@gi) for i in range(3)])
def Fprime_comp(x, with_comm=True, h=1e-5):
    Ap = Aprime_comp(x)
    dAp = np.array([(Aprime_comp(x+h*e[j]) - Aprime_comp(x-h*e[j]))/(2*h) for j in range(3)])
    F = np.zeros((3,3,3))
    for i in range(3):
        for j in range(3):
            F[i,j] = dAp[i,j] - dAp[j,i] + (np.cross(Ap[i],Ap[j]) if with_comm else 0)
    return F

print("\nCheck 2: F transforms covariantly (F' = g F g^-1) only with the commutator term")
for xx in [np.array([0.1,0.2,0.3]), np.array([-0.7,0.4,1.1])]:
    gx = g(xx); gi = np.linalg.inv(gx)
    for wc in (True, False):
        F = F_comp(xx, wc); Fp = Fprime_comp(xx, wc)
        rot = np.array([[comp(gx@mat(F[i,j])@gi) for j in range(3)] for i in range(3)])
        print(f"  x={xx}, with [A,A]={wc!s:5}: max|F' - gFg^-1| = {np.abs(Fp-rot).max():.2e}")

# ---------- Check 3: Wong particle (anchored point carrying a hidden charge Q) ----------
def make_rhs(Afun, Ffun, precess=True, with_comm=True, m=1.0):
    def rhs(t, y):
        x, v, Q = y[:3], y[3:6], y[6:9]
        F = Ffun(x, with_comm); A = Afun(x)
        acc = np.array([sum(Q@F[i,j]*v[j] for j in range(3)) for i in range(3)])/m
        Qdot = sum(np.cross(Q, A[j])*v[j] for j in range(3)) if precess else np.zeros(3)
        return np.concatenate([v, acc, Qdot])
    return rhs

x_init = np.array([0.1,0.2,0.3]); v_init = np.array([0.6,-0.3,0.4]); Q_init = np.array([1.0,0.5,-0.8])
gx = g(x_init); gi = np.linalg.inv(gx); Qp_init = comp(gx@mat(Q_init)@gi)
tspan = (0, 4.0); teval = np.linspace(0,4,9)
print("\nCheck 3: Wong trajectory is independent of the hidden labelling only with precession + [A,A]")
for precess, wc, label in [(True, True, "full (precession + [A,A])"),
                           (False, True, "no colour precession"),
                           (True, False, "no [A,A] in F"),
                           (False, False, "abelian-style (neither)")]:
    s1 = solve_ivp(make_rhs(A_comp, F_comp, precess, wc), tspan, np.concatenate([x_init,v_init,Q_init]), t_eval=teval, rtol=1e-10, atol=1e-12)
    s2 = solve_ivp(make_rhs(Aprime_comp, Fprime_comp, precess, wc), tspan, np.concatenate([x_init,v_init,Qp_init]), t_eval=teval, rtol=1e-9, atol=1e-11)
    dx = np.abs(s1.y[:3]-s2.y[:3]).max()
    E = 0.5*np.sum(s1.y[3:6]**2,axis=0); Qn = np.linalg.norm(s1.y[6:9],axis=0)
    print(f"  {label:28s}: max |x(t) - x'(t)| = {dx:.2e} ; energy drift {np.ptp(E):.1e} ; |Q| drift {np.ptp(Qn):.1e}")
