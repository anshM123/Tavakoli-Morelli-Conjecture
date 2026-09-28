"""
verify_all.py -- numerical verification of every step of the P-TM proof.

T0  constructions (MUB sets d=2..10, ETFs/EAMs, SICs)
T1  coordinator facts (1)-(3): Q = V^dag (X (x) conj X) V, Pi_k Pi_l = Phi+, VV^dag = (m-1)Phi+ + P, ||Q||_1 = ||F Y F||_1, Tr Q formula
T2  Gram factorisation  Q = Xi^dag H  (Lemma 1)
T3  index-of-coincidence (Bessel) bound  IC_e(A) <= ||A||_F^2 + (m-1)(Tr A)^2/d   (Lemma 2)
T4  main chain  ||Q||_1 <= sqrt(IC_e(|X^dag|) IC_f(|X|)) <= sqrt((N+(mA-1)t^2/dA)(N+(mB-1)t^2/dB))  (Theorem 1),
    incl. independent Alice/Bob MUB sets, unequal dimensions, unequal numbers of bases
T5  Conjecture 3 (random Schmidt-rank-r states, mixed states) + equality X = Pi_S/sqrt(r)
T6  Conjecture 2 (EAMs) via the same template + equality cases r = 1 and r = d
T7  Conjecture 1 (SIC vs complete MUBs, arbitrary mixed states)
"""
import sys
import numpy as np
from tmlib import *

rng = np.random.default_rng(20260927)
worst = {}


def rec(name, slack):
    worst[name] = min(worst.get(name, np.inf), slack)


# ------------------------------------------------------------------ T0
MUBS = {d: mub_set(d) for d in (2, 3, 4, 5, 6, 7, 9, 10)}
for d, B in MUBS.items():
    check_mubs(B)
print("T0 MUB sets ok:", {d: len(B) for d, B in MUBS.items()})
ETFS = {
    'SIC2': sic_qubit(), 'SIC3': sic_qutrit(),
    'simplex2': etf_simplex(2), 'simplex3': etf_simplex(3), 'simplex5': etf_simplex(5),
    'H(7,3)': etf_harmonic(7, [1, 2, 4]), 'H(7,4)': etf_harmonic(7, [0, 3, 5, 6]),
    'H(13,4)': etf_harmonic(13, [0, 1, 3, 9]), 'H(11,5)': etf_harmonic(11, [1, 3, 4, 5, 9]),
    'H(11,6)': etf_harmonic(11, [0, 2, 6, 7, 8, 10]), 'H(21,5)': etf_harmonic(21, [3, 6, 7, 12, 14]),
}
for k, V in ETFS.items():
    check_etf(V)
print("T0 ETFs ok:", {k: V.shape for k, V in ETFS.items()})

# ------------------------------------------------------------------ T1 coordinator facts
for d in (3, 4, 5, 6):
    B = MUBS[d]
    for m in range(1, len(B) + 1):
        bases = B[:m]
        V = np.concatenate([np.einsum('ia,ja->ija', E, E.conj()).reshape(d * d, d) for E in bases], axis=1)
        phi = np.eye(d).reshape(-1) / np.sqrt(d)
        Phi = np.outer(phi, phi.conj())
        Pis = [np.einsum('ia,ja->ija', E, E.conj()).reshape(d * d, d) for E in bases]
        Pis = [p @ p.conj().T for p in Pis]
        for k in range(m):
            for l in range(m):
                if k != l:
                    assert np.allclose(Pis[k] @ Pis[l], Phi, atol=1e-10)
        P = V @ V.conj().T - (m - 1) * Phi
        assert np.allclose(P @ P, P, atol=1e-10) and abs(np.trace(P).real - (1 + m * (d - 1))) < 1e-9
        F = P + (np.sqrt(m) - 1) * Phi
        assert np.allclose(F @ F, V @ V.conj().T, atol=1e-10)
        for _ in range(5):
            X = random_X(d, d, rng.integers(1, d + 1), rng)
            Y = np.kron(X, X.conj())
            Q = Qmat(X, bases, bases)
            assert np.allclose(V.conj().T @ Y @ V, Q, atol=1e-12)
            assert abs(trnorm(Q) - trnorm(F @ Y @ F)) < 1e-10
            psi = X.reshape(-1)
            assert abs(np.trace(Q) - psi.conj() @ ((m - 1) * Phi + P) @ psi) < 1e-12
print("T1 coordinator facts (1)-(3) ok")

# ------------------------------------------------------------------ T2 + T4 main chain
def main_chain(X, EA, FB, dA, dB):
    Q = Qmat(X, EA, FB)
    Xi, H, L, W, R = gram_factors(X, EA, FB)
    e2 = np.max(np.abs(Xi.conj().T @ H - Q))
    absXd, absX = psd_abs(X)
    N = np.linalg.norm(X) ** 2
    t = np.linalg.svd(X, compute_uv=False).sum()
    lhs = trnorm(Q)
    b1 = np.sqrt(IC(absXd, EA) * IC(absX, FB))
    b2 = np.sqrt((N + (len(EA) - 1) * t * t / dA) * (N + (len(FB) - 1) * t * t / dB))
    # Hoelder factors
    assert abs(np.linalg.norm(Xi) ** 2 - IC(absXd, EA)) < 1e-10
    assert abs(np.linalg.norm(H) ** 2 - IC(absX, FB)) < 1e-10
    return e2, lhs, b1, b2


cnt = 0
for trial in range(4000):
    dA = int(rng.choice([2, 3, 4, 5, 6, 7]))
    dB = dA if rng.random() < 0.6 else int(rng.choice([2, 3, 4, 5, 6, 7]))
    BA, BB = MUBS[dA], MUBS[dB]
    mA = int(rng.integers(1, len(BA) + 1)); mB = int(rng.integers(1, len(BB) + 1))
    UA = haar_unitary(dA, rng) if rng.random() < 0.5 else np.eye(dA)
    UB = haar_unitary(dB, rng) if rng.random() < 0.5 else np.eye(dB)
    EA = [UA @ B for B in [BA[i] for i in rng.permutation(len(BA))[:mA]]]
    FB = [UB @ B for B in [BB[i] for i in rng.permutation(len(BB))[:mB]]]
    r = int(rng.integers(1, min(dA, dB) + 1))
    X = random_X(dA, dB, r, rng, flat=rng.random() < 0.3) * (rng.random() * 3 + 0.1)
    e2, lhs, b1, b2 = main_chain(X, EA, FB, dA, dB)
    assert e2 < 1e-11, e2
    rec('T4 b1 - ||Q||_1 (Hoelder)', b1 - lhs)
    rec('T4 b2 - b1 (Bessel)', b2 - b1)
    cnt += 1
print(f"T2 Gram factorisation ok on {cnt} random instances; T4 chain slacks:",
      {k: f"{v:.2e}" for k, v in worst.items() if k.startswith('T4')})

# ------------------------------------------------------------------ T3 IC lemma incl. equality
for trial in range(3000):
    d = int(rng.choice([2, 3, 4, 5, 6, 7, 9, 10]))
    B = MUBS[d]
    m = int(rng.integers(1, len(B) + 1))
    U = haar_unitary(d, rng)
    bases = [U @ b for b in B[:m]]
    k = int(rng.integers(1, d + 1))
    G = rng.normal(size=(d, k)) + 1j * rng.normal(size=(d, k))
    A = G @ G.conj().T
    bnd = np.linalg.norm(A) ** 2 + (m - 1) * np.trace(A).real ** 2 / d
    rec('T3 IC bound slack (relative)', (bnd - IC(A, bases)) / bnd)
    # equality: A in span{I} + (+) S_k  (sum of diagonals in the m bases), made PSD by shifting
    Dsum = sum(bb @ np.diag(rng.normal(size=d)) @ bb.conj().T for bb in bases)
    Aeq = Dsum - min(0, np.linalg.eigvalsh(Dsum).min()) * np.eye(d)
    bnd = np.linalg.norm(Aeq) ** 2 + (m - 1) * np.trace(Aeq).real ** 2 / d
    rec('T3 IC equality |gap| (relative, should be ~0)', -abs(bnd - IC(Aeq, bases)) / bnd)
print("T3 IC lemma:", {k: f"{v:.2e}" for k, v in worst.items() if k.startswith('T3')})

# ------------------------------------------------------------------ T5 Conjecture 3
for d in (2, 3, 4, 5, 6, 7):
    B = MUBS[d]
    for m in range(1, len(B) + 1):
        for r in range(1, d + 1):
            bound = 1 + (m - 1) * r / d
            best = 0
            for trial in range(40):
                EA = B[:m]
                Ur = haar_unitary(d, rng)  # ONE unitary for the whole set (keeps it a MUB set)
                FB = [Ur @ b for b in B[:m]] if trial % 4 == 3 else B[:m]
                X = random_X(d, d, r, rng, flat=trial % 2 == 0)
                best = max(best, trnorm(Qmat(X, EA, FB)))
            # mixed state of Schmidt number <= r: average of Q's
            Qm = sum(Qmat(random_X(d, d, r, rng), B[:m], B[:m]) for _ in range(5)) / 5
            best = max(best, trnorm(Qm))
            rec('T5 conj3 slack (random)', bound - best)
            # equality example
            S = rng.permutation(d)[:r]
            X = B[0][:, S] @ B[0][:, S].conj().T / np.sqrt(r)
            val = trnorm(Qmat(X, B[:m], B[:m]))
            rec('T5 conj3 equality |gap| (should be ~0)', -abs(val - bound))
print("T5 Conjecture 3:", {k: f"{v:.2e}" for k, v in worst.items() if k.startswith('T5')})

# ------------------------------------------------------------------ T6 Conjecture 2 (EAM)
for name, V in ETFS.items():
    d, n = V.shape
    c = (n - d) / (d * (n - 1))
    w = d / n
    for trial in range(300):
        r = int(rng.integers(1, d + 1))
        X = random_X(d, d, r, rng, flat=trial % 2 == 0)
        VB = haar_unitary(d, rng) @ V if trial % 3 == 0 else V
        P = Pframe(X, V, VB, w, w)
        absXd, absX = psd_abs(X)
        N = 1.0
        t = np.linalg.svd(X, compute_uv=False).sum()
        lhs = trnorm(P)
        b1 = w * w * np.sqrt(ICframe(absXd, V) * ICframe(absX, VB))
        b2 = (n - d) / (n * (n - 1)) * t * t + d * (d - 1) / (n * (n - 1)) * N
        conj2 = (d * (d - 1) + r * (n - d)) / (n * (n - 1))
        rec('T6 EAM b1 - ||P||_1', b1 - lhs)
        rec('T6 EAM b2 - b1', b2 - b1)
        rec('T6 EAM conj2 - ||P||_1', conj2 - lhs)
    # equality r = 1 (X = |psi_1><psi_1|) and r = d (X = I/sqrt d)
    X1 = np.outer(V[:, 0], V[:, 0].conj())
    rec('T6 EAM equality r=1 |gap|', -abs(trnorm(Pframe(X1, V, V, w, w)) - (d * (d - 1) + (n - d)) / (n * (n - 1))))
    Xd = np.eye(d) / np.sqrt(d)
    rec('T6 EAM equality r=d |gap|', -abs(trnorm(Pframe(Xd, V, V, w, w)) - d / n))
print("T6 Conjecture 2:", {k: f"{v:.2e}" for k, v in worst.items() if k.startswith('T6')})

# ------------------------------------------------------------------ T7 Conjecture 1 (SIC vs complete MUB)
SICS = {2: sic_qubit(), 3: sic_qutrit()}
for dA in (2, 3):
    for dB in (2, 3):
        K = np.sqrt(dA * (dA + 1)) * np.sqrt(dB * (dB + 1))
        for trial in range(200):
            # random mixed state (random rank)
            D = dA * dB
            k = int(rng.integers(1, D + 1))
            G = rng.normal(size=(D, k)) + 1j * rng.normal(size=(D, k))
            rho = G @ G.conj().T; rho /= np.trace(rho).real
            rho4 = rho.reshape(dA, dB, dA, dB)
            # Alice/Bob: independent, randomly rotated complete MUB sets and SICs (physical projectors, no conjugation)
            Ug = haar_unitary(dA, rng); Uh = haar_unitary(dB, rng)  # one unitary per party
            gA = [Ug @ b for b in MUBS[dA]] if trial % 2 else MUBS[dA]
            hB = [Uh @ b for b in MUBS[dB]]
            UA, UB = haar_unitary(dA, rng), haar_unitary(dB, rng)
            sA, sB = UA @ SICS[dA], UB @ SICS[dB]
            GA = np.concatenate(gA, axis=1); HB = np.concatenate(hB, axis=1)
            Q = np.real(np.einsum('ia,jb,ijkl,ka,lb->ab', GA.conj(), HB.conj(), rho4, GA, HB))
            P = np.real(np.einsum('ia,jb,ijkl,ka,lb->ab', sA.conj(), sB.conj(), rho4, sA, sB)) / (dA * dB)
            rec('T7 conj1 |  ||Q|| - K||P||  |', -abs(trnorm(Q) - K * trnorm(P)))
print("T7 Conjecture 1:", {k: f"{v:.2e}" for k, v in worst.items() if k.startswith('T7')})

print("\nALL WORST SLACKS (negative = violation unless marked |gap|):")
for k, v in worst.items():
    print(f"  {k:55s} {v:+.3e}")
