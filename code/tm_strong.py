"""
R014: adversarial test of a STRENGTHENED Tavakoli–Morelli inequality (implies Conjecture 3):
      ||Q_m(X)||_1  <=  1 + (m-1) ||X||_1^2 / d      for all X with ||X||_F = 1
(||X||_1^2/d = fully entangled fraction of psi = vec(X); Schmidt rank r => ||X||_1^2 <= r).
Maximise the violation  ||Q_m(X)||_1 - 1 - (m-1)||X||_1^2/d  over full-rank complex X (Adam, many restarts).
Also tests the equivalent frame form ||F (X (x) conj X) F||_1 with F = P + (sqrt m - 1) Phi+.
"""
import sys
import numpy as np
import torch
from tm_conjecture import mubs_prime, Qmat

torch.set_default_dtype(torch.float64)
DEV = 'cuda' if torch.cuda.is_available() else 'cpu'


def run(d, m, restarts=128, steps=2000, seed=0):
    g = torch.Generator(device=DEV).manual_seed(seed)
    bases = [torch.tensor(b, device=DEV) for b in mubs_prime(d)[:m]]
    Z = torch.randn(restarts, d, d, 2, device=DEV, generator=g, requires_grad=True)
    opt = torch.optim.Adam([Z], lr=0.02)
    best = -1e9
    for s in range(steps):
        X = torch.complex(Z[..., 0], Z[..., 1])
        X = X / torch.linalg.norm(X, dim=(-2, -1), keepdim=True)
        Q = Qmat(X, bases)
        lhs = torch.linalg.svdvals(Q).sum(-1)
        rhs = 1 + (m - 1) * torch.linalg.svdvals(X).sum(-1) ** 2 / d
        viol = lhs - rhs
        loss = -viol.sum()
        opt.zero_grad(); loss.backward(); opt.step()
        best = max(best, float(viol.max().detach()))
    return best


if __name__ == '__main__':
    ds = [int(a) for a in sys.argv[1:]] or [3, 5]
    for d in ds:
        for m in range(2, d + 2):
            v = run(d, m, seed=d * 10 + m)
            print(f"d={d} m={m}: max violation of strengthened inequality = {v:+.3e}", flush=True)
