"""
R015: independent (coordinator) check of the P-TM proof chain, own code:
 Lemma 1: ||[|<a_i|X|b_j>|^2]||_1 <= sqrt(IC_a(|X^dag|) IC_b(|X|))  for ARBITRARY vector families a, b
 Lemma 2: IC_e(A) <= Tr A^2 + (m-1)(Tr A)^2/d for m MUBs, A >= 0 Hermitian
 Theorem: ||Q_m||_1 <= ||X||_F^2 + (m-1)||X||_1^2/d ; tightness at X = Pi_S/sqrt(r).
MUBs: prime d from Weylâ€“Heisenberg (computational + quadratic-phase bases), random subsets of size m, both parties
may use DIFFERENT MUB sets (rotated by independent unitaries applied to the whole set).
"""
import itertools
import numpy as np
from scipy.linalg import sqrtm

rng = np.random.default_rng(12345)


def mubs(d):
    om = np.exp(2j * np.pi / d)
    B = [np.eye(d, dtype=complex)]
    for k in range(d):
        B.append(np.array([[om ** (k * j * j + a * j) for a in range(d)] for j in range(d)]) / np.sqrt(d))
    for i, j in itertools.combinations(range(d + 1), 2):
        assert np.allclose(np.abs(B[i].conj().T @ B[j]) ** 2, 1 / d), (d, i, j)
    return B


def haar(d):
    Z = (rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def IC(vecs, A):
    return sum(np.real(np.vdot(v, A @ v)) ** 2 for v in vecs)


def absm(X):
    w, V = np.linalg.eigh(X)
    return (V * np.sqrt(np.clip(w, 0, None))) @ V.conj().T


worst1 = worst2 = worst3 = -np.inf
for trial in range(3000):
    d = int(rng.choice([3, 5, 7]))
    m = int(rng.integers(1, d + 2))
    allB = mubs(d)
    idxA = rng.choice(d + 1, m, replace=False); idxB = rng.choice(d + 1, m, replace=False)
    UA, UB = haar(d), haar(d)
    A = [UA @ allB[i] for i in idxA]; B = [UB @ allB[i] for i in idxB]
    avecs = [b[:, a] for b in A for a in range(d)]
    bvecs = [b[:, a] for b in B for a in range(d)]
    r = int(rng.integers(1, d + 1))
    X = (rng.normal(size=(d, r)) + 1j * rng.normal(size=(d, r))) @ (rng.normal(size=(r, d)) + 1j * rng.normal(size=(r, d)))
    X /= np.linalg.norm(X)
    Q = np.array([[abs(np.vdot(a, X @ b)) ** 2 for b in bvecs] for a in avecs])
    lhs = np.linalg.svd(Q, compute_uv=False).sum()
    AXd = absm(X @ X.conj().T); AX = absm(X.conj().T @ X)
    l1 = np.sqrt(IC(avecs, AXd) * IC(bvecs, AX))
    N = np.linalg.norm(X) ** 2; tau = np.linalg.svd(X, compute_uv=False).sum()
    bound = N + (m - 1) * tau ** 2 / d
    worst1 = max(worst1, lhs - l1)
    worst2 = max(worst2, IC(avecs, AXd) - (np.trace(AXd @ AXd).real + (m - 1) * np.trace(AXd).real ** 2 / d))
    worst3 = max(worst3, lhs - bound)
print(f"Lemma 1 max(lhs - sqrt(IC IC)) = {worst1:.2e}   (must be <= ~1e-12)")
print(f"Lemma 2 max(IC - bound)        = {worst2:.2e}")
print(f"Theorem max(||Q||_1 - (N + (m-1)tau^2/d)) = {worst3:.2e}")

# tightness: X = Pi_S / sqrt(r), same MUB set both sides
for d in (3, 5, 7):
    B = mubs(d)
    for m in range(1, d + 2):
        for r in range(1, d + 1):
            S = list(range(r))
            X = sum(np.outer(B[0][:, a], B[0][:, a].conj()) for a in S) / np.sqrt(r)
            vecs = [b[:, a] for b in B[:m] for a in range(d)]
            Q = np.array([[abs(np.vdot(u, X @ v)) ** 2 for v in vecs] for u in vecs])
            val = np.linalg.svd(Q, compute_uv=False).sum()
            assert abs(val - (1 + (m - 1) * r / d)) < 1e-10, (d, m, r, val)
print("tightness 1+(m-1)r/d attained exactly for d=3,5,7, all m<=d+1, all r: OK")

