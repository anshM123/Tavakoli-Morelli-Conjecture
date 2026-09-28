"""
R009: numerical test of Tavakoli–Morelli Conjecture 3 (arXiv:2402.09972):
   for every state of Schmidt number <= r and m < d+1 MUBs:  ||Q_m||_tr <= 1 + (m-1) r / d,
   Q_{(k,a),(l,b)} = |<e^k_a| X |e^l_b>|^2,   psi = vec(X), ||X||_F = 1, rank X <= r  (Bob measures conjugate bases).
Convexity of the trace norm => pure states suffice.  Maximise over X = A B^dag (A, B: d x r) with Adam on GPU.
MUBs for prime d: computational + {omega^{k j^2 + a j}/sqrt d : k = 0..d-1}.
"""
import argparse
import itertools
import math
import time

import numpy as np
import torch

torch.set_default_dtype(torch.float64)
DEV = 'cuda' if torch.cuda.is_available() else 'cpu'


def mubs_prime(d):
    om = np.exp(2j * np.pi / d)
    B = [np.eye(d, dtype=complex)]
    for k in range(d):
        B.append(np.array([[om ** (k * j * j + a * j) for a in range(d)] for j in range(d)]) / np.sqrt(d))
    for i, j in itertools.combinations(range(d + 1), 2):          # sanity: unbiased
        assert np.allclose(np.abs(B[i].conj().T @ B[j]) ** 2, 1 / d)
    return B


def Qmat(X, bases):
    # blocks |E_k^dag X E_l|^2
    rows = []
    for Ek in bases:
        rows.append(torch.cat([(Ek.conj().T @ X @ El).abs() ** 2 for El in bases], dim=-1))
    return torch.cat(rows, dim=-2)


def run(d, m, r, restarts, steps, seed):
    g = torch.Generator(device=DEV).manual_seed(seed)
    bases = [torch.tensor(b, device=DEV) for b in mubs_prime(d)[:m]]
    A = torch.randn(restarts, d, r, 2, device=DEV, generator=g)
    B = torch.randn(restarts, d, r, 2, device=DEV, generator=g)
    A.requires_grad_(True); B.requires_grad_(True)
    opt = torch.optim.Adam([A, B], lr=0.03)
    best = 0.0
    for s in range(steps):
        Ac = torch.complex(A[..., 0], A[..., 1]); Bc = torch.complex(B[..., 0], B[..., 1])
        X = Ac @ Bc.conj().transpose(-1, -2)
        X = X / torch.linalg.norm(X, dim=(-2, -1), keepdim=True)
        Q = Qmat(X, bases)
        val = torch.linalg.svdvals(Q).sum(-1)
        loss = -val.sum()
        opt.zero_grad(); loss.backward(); opt.step()
        best = max(best, float(val.max()))
    return best


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--d', type=int, nargs='+', default=[3, 5])
    ap.add_argument('--restarts', type=int, default=64)
    ap.add_argument('--steps', type=int, default=1500)
    a = ap.parse_args()
    for d in a.d:
        for m in range(2, d + 1):
            for r in range(1, d):
                t0 = time.time()
                best = run(d, m, r, a.restarts, a.steps, seed=d * 100 + m * 10 + r)
                bound = 1 + (m - 1) * r / d
                flag = "VIOLATION" if best > bound + 1e-6 else ("tight" if best > bound - 1e-4 else "")
                print(f"d={d} m={m} r={r}: max ||Q||_tr = {best:.6f}   conj bound {bound:.6f}   {flag}  ({time.time()-t0:.0f}s)", flush=True)
