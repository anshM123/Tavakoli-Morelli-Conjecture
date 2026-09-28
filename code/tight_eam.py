"""
tight_eam.py -- is the (now proven) Conjecture-2 bound attained at intermediate Schmidt rank r?
First run (adversarial.py C): tight for all r for simplex3, H(7,3), H(7,4), SIC3, H(13,4), but simplex4 (n=5,d=4) r=2
gave 0.69496 < 0.7.  Here: heavier search (more restarts, lr decay, several seeds) over rank-r X, both aligned Bob frame
(f = e) and generic; report the best value and the singular values / structure of the maximiser.
"""
import os
os.environ["OMP_NUM_THREADS"] = "4"
import sys
import numpy as np
import torch
from tmlib import etf_simplex, etf_harmonic

torch.set_num_threads(4)
torch.set_default_dtype(torch.float64)


def search(V, r, restarts=256, steps=4000, seed=0, lr=0.05):
    d, n = V.shape
    w = d / n
    g = torch.Generator().manual_seed(seed)
    Vt = torch.tensor(V)
    A = torch.randn(restarts, d, r, 2, generator=g, requires_grad=True)
    B = torch.randn(restarts, d, r, 2, generator=g, requires_grad=True)
    opt = torch.optim.Adam([A, B], lr=lr)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, steps, eta_min=1e-4)
    for s in range(steps):
        X = torch.complex(A[..., 0], A[..., 1]) @ torch.complex(B[..., 0], B[..., 1]).conj().transpose(-1, -2)
        X = X / torch.linalg.norm(X, dim=(-2, -1), keepdim=True)
        P = w * w * (Vt.conj().T @ X @ Vt).abs() ** 2
        val = torch.linalg.svdvals(P).sum(-1)
        opt.zero_grad(); (-val.sum()).backward(); opt.step(); sched.step()
    i = int(val.argmax())
    return float(val[i].detach()), X[i].detach().numpy()


if __name__ == '__main__':
    # key cases: simplex d=4 r=2 (predicted strict), d=5 r=2,3 (strict) and r=4 (tight), d=6 r=3 (strict), r=5 (tight)
    cases = [('simplex4', etf_simplex(4), [2]), ('simplex5', etf_simplex(5), [2, 3, 4]), ('simplex6', etf_simplex(6), [3, 5])]
    for name, V, rs in cases:
        d, n = V.shape
        for r in rs:
            bound = (d * (d - 1) + r * (n - d)) / (n * (n - 1))
            best, Xb = -1, None
            for seed in range(2):
                v, X = search(V, r, restarts=128, steps=3000, seed=seed)
                if v > best:
                    best, Xb = v, X
            sv = np.linalg.svd(Xb, compute_uv=False)[:r]
            print(f"{name} (n={n},d={d}) r={r}: best={best:.10f} bound={bound:.10f} gap={bound-best:+.3e} "
                  f"svals^2={np.round(sv**2, 4)}", flush=True)
