"""
adversarial.py -- gradient-based attempts to BREAK the proven inequalities (sanity check against algebra slips),
and exploration of tightness of Conjecture 2 for intermediate r.

(A) max over X of  ||Q(X)||_1 - [ ||X||_F^2 + (m-1)||X||_1^2/d ]   (strengthened ineq.)  -- expect max = 0 (attained)
    for non-prime d (4: Pauli-class MUBs, 6: product MUBs), independent Alice/Bob MUB sets (Bob rotated by Haar U).
(B) same for the sharper Hoelder form  ||Q||_1 / sqrt(IC_e(|X^dag|) IC_f(|X|))  <= 1.
(C) EAMs: max over Schmidt-rank-r X of ||P_n||_1 vs Conjecture-2 bound (is it attained for 1 < r < d?).
CPU only, 4 threads.
"""
import os
os.environ["OMP_NUM_THREADS"] = "4"
import sys
import numpy as np
import torch
from tmlib import mub_set, haar_unitary, etf_harmonic, etf_simplex, sic_qutrit

torch.set_num_threads(4)
torch.set_default_dtype(torch.float64)


def Qt(X, EA, FB):
    return torch.cat([torch.cat([(Ek.conj().T @ X @ Fl).abs() ** 2 for Fl in FB], dim=-1) for Ek in EA], dim=-2)


def psd_parts(X):
    U, s, Vh = torch.linalg.svd(X)
    absXd = (U * s.unsqueeze(-2).to(U.dtype)) @ U.conj().transpose(-1, -2)
    absX = (Vh.conj().transpose(-1, -2) * s.unsqueeze(-2).to(U.dtype)) @ Vh
    return absXd, absX, s


def ICt(A, bases):
    return sum((torch.einsum('ia,...ij,ja->...a', B.conj(), A, B).real ** 2).sum(-1) for B in bases)


def attack_strong(d, m, rotate_bob, restarts=64, steps=1500, seed=0, mode='strong'):
    g = torch.Generator().manual_seed(seed)
    rng = np.random.default_rng(seed)
    B = mub_set(d)[:m]
    EA = [torch.tensor(b) for b in B]
    Ub = haar_unitary(d, rng) if rotate_bob else np.eye(d)
    FB = [torch.tensor(Ub @ b) for b in B]
    Z = torch.randn(restarts, d, d, 2, generator=g, requires_grad=True)
    opt = torch.optim.Adam([Z], lr=0.02)
    best = -1e9
    for s in range(steps):
        X = torch.complex(Z[..., 0], Z[..., 1])
        X = X / torch.linalg.norm(X, dim=(-2, -1), keepdim=True)
        lhs = torch.linalg.svdvals(Qt(X, EA, FB)).sum(-1)
        if mode == 'strong':
            rhs = 1 + (m - 1) * torch.linalg.svdvals(X).sum(-1) ** 2 / d
            obj = lhs - rhs
        else:
            absXd, absX, _ = psd_parts(X)
            obj = lhs / torch.sqrt(ICt(absXd, EA) * ICt(absX, FB)) - 1
        loss = -obj.sum()
        opt.zero_grad(); loss.backward(); opt.step()
        best = max(best, float(obj.max().detach()))
    return best


def attack_eam(V, r, restarts=64, steps=2000, seed=0):
    d, n = V.shape
    w = d / n
    g = torch.Generator().manual_seed(seed)
    Vt = torch.tensor(V)
    A = torch.randn(restarts, d, r, 2, generator=g, requires_grad=True)
    Bm = torch.randn(restarts, d, r, 2, generator=g, requires_grad=True)
    opt = torch.optim.Adam([A, Bm], lr=0.03)
    best = 0
    for s in range(steps):
        X = torch.complex(A[..., 0], A[..., 1]) @ torch.complex(Bm[..., 0], Bm[..., 1]).conj().transpose(-1, -2)
        X = X / torch.linalg.norm(X, dim=(-2, -1), keepdim=True)
        P = w * w * (Vt.conj().T @ X @ Vt).abs() ** 2
        val = torch.linalg.svdvals(P).sum(-1)
        opt.zero_grad(); (-val.sum()).backward(); opt.step()
        best = max(best, float(val.max().detach()))
    return best


if __name__ == '__main__':
    part = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if part in ('A', 'all'):
        for d, ms in ((4, (2, 3, 4, 5)), (6, (2, 3)), (3, (2, 3))):
            for m in ms:
                for rot in (False, True):
                    v = attack_strong(d, m, rot, seed=100 * d + 10 * m + rot)
                    print(f"(A) d={d} m={m} bob_rotated={rot}: max [||Q||_1 - N - (m-1)t^2/d] = {v:+.3e}", flush=True)
    if part in ('B', 'all'):
        for d, ms in ((4, (2, 3)), (6, (2, 3)), (5, (3,))):
            for m in ms:
                v = attack_strong(d, m, True, seed=7 * d + m, mode='holder', steps=1000)
                print(f"(B) d={d} m={m} bob_rotated=True: max [||Q||_1/sqrt(IC IC) - 1] = {v:+.3e}", flush=True)
    if part in ('C', 'all'):
        etfs = {'simplex3 (n=4,d=3)': etf_simplex(3), 'H(7,3)': etf_harmonic(7, [1, 2, 4]),
                'H(7,4)': etf_harmonic(7, [0, 3, 5, 6]), 'SIC3 (n=9,d=3)': sic_qutrit(),
                'H(13,4)': etf_harmonic(13, [0, 1, 3, 9]), 'simplex4 (n=5,d=4)': etf_simplex(4)}
        for name, V in etfs.items():
            d, n = V.shape
            for r in range(1, d + 1):
                best = attack_eam(V, r, seed=r)
                bound = (d * (d - 1) + r * (n - d)) / (n * (n - 1))
                print(f"(C) {name}: r={r}  max ||P_n||_1 = {best:.8f}   Conj-2 bound = {bound:.8f}   gap = {bound - best:+.2e}", flush=True)
