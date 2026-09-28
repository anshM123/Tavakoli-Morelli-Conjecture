"""simplex_projectors.py -- numerical check of the claim: span_R{P_a} of the simplex EAM (n=d+1) contains a rank-r
projector iff r in {0,1,d-1,d}.  span = {compression of real diagonal D to 1^perp}; minimise the distance of the
compression spectrum to (1^r,0^(d-r)) over D (many restarts)."""
import numpy as np
from scipy.optimize import minimize
rng = np.random.default_rng(0)


def spec(D):
    n = len(D)
    Jb = np.linalg.qr(np.eye(n) - np.ones((n, n)) / n)[0][:, :n - 1]   # orthonormal basis of 1^perp
    return np.sort(np.linalg.eigvalsh(Jb.T @ np.diag(D) @ Jb))[::-1]


for d in (3, 4, 5, 6):
    n = d + 1
    out = []
    for r in range(0, d + 1):
        target = np.array([1.0] * r + [0.0] * (d - r))
        f = lambda D: np.sum((spec(D) - target) ** 2)
        best = min(minimize(f, rng.normal(size=n) * 2, method='Nelder-Mead',
                            options={'xatol': 1e-12, 'fatol': 1e-14, 'maxiter': 20000}).fun for _ in range(40))
        out.append(f"r={r}: {best:.1e}")
    print(f"d={d}:", "  ".join(out))
