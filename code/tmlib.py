"""
tmlib.py -- constructions and helpers for program P-TM (Tavakoli-Morelli conjectures, arXiv:2402.09972).

Conventions: a basis is a d x d unitary whose COLUMNS are the basis vectors.
For psi = vec(X) = sum X_ij |i>|j>, Alice measuring basis e and Bob measuring basis h gives
    Tr[psi psi^dag (|e><e| (x) |h><h|)] = |<e| X |conj h>|^2,
so the correlation matrix is Q = [ |<e^k_a| X |f^l_b>|^2 ] with f = conj(h) (again a set of MUBs).
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "4")
os.environ.setdefault("MKL_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
import itertools
import numpy as np

# ----------------------------------------------------------------------------------------------
# MUB constructions
# ----------------------------------------------------------------------------------------------
PAULI = {
    'I': np.eye(2, dtype=complex),
    'X': np.array([[0, 1], [1, 0]], dtype=complex),
    'Y': np.array([[0, -1j], [1j, 0]], dtype=complex),
    'Z': np.array([[1, 0], [0, -1]], dtype=complex),
}


def pauli_string(s):
    M = np.array([[1.0 + 0j]])
    for ch in s:
        M = np.kron(M, PAULI[ch])
    return M


def common_eigenbasis(ops, rng):
    """common eigenbasis of commuting Hermitian operators (generic real combination)."""
    coeffs = rng.normal(size=len(ops))
    H = sum(c * O for c, O in zip(coeffs, ops))
    w, U = np.linalg.eigh(H)
    assert np.min(np.diff(w)) > 1e-6, "degenerate combination"
    return U


def mubs_qubit():
    B0 = np.eye(2, dtype=complex)
    B1 = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
    B2 = np.array([[1, 1], [1j, -1j]], dtype=complex) / np.sqrt(2)
    return [B0, B1, B2]


def mubs_prime(d):
    if d == 2:
        return mubs_qubit()
    om = np.exp(2j * np.pi / d)
    B = [np.eye(d, dtype=complex)]
    for k in range(d):
        B.append(np.array([[om ** ((k * j * j + a * j) % d) for a in range(d)] for j in range(d)]) / np.sqrt(d))
    return B


def mubs_two_qubits(seed=0):
    rng = np.random.default_rng(seed)
    classes = [['ZI', 'IZ', 'ZZ'], ['XI', 'IX', 'XX'], ['YI', 'IY', 'YY'], ['XY', 'YZ', 'ZX'], ['YX', 'ZY', 'XZ']]
    return [common_eigenbasis([pauli_string(s) for s in c], rng) for c in classes]


def mubs_product(d1_bases, d2_bases):
    """k-th basis = B1_k (x) B2_k; gives min(m1, m2) MUBs in dimension d1*d2."""
    return [np.kron(a, b) for a, b in zip(d1_bases, d2_bases)]


def mub_set(d):
    """largest readily-constructed MUB set in dimension d (complete for d prime or d = 4)."""
    if d in (2, 3, 5, 7, 11, 13):
        return mubs_prime(d)
    if d == 4:
        return mubs_two_qubits()
    if d == 6:
        return mubs_product(mubs_prime(2), mubs_prime(3))  # 3 MUBs
    if d == 9:
        return mubs_product(mubs_prime(3), mubs_prime(3))  # 4 MUBs
    if d == 10:
        return mubs_product(mubs_prime(2), mubs_prime(5))  # 3 MUBs
    raise ValueError(d)


def check_mubs(bases, tol=1e-10):
    d = bases[0].shape[0]
    for B in bases:
        assert np.allclose(B.conj().T @ B, np.eye(d), atol=tol)
    for B1, B2 in itertools.combinations(bases, 2):
        assert np.allclose(np.abs(B1.conj().T @ B2) ** 2, 1.0 / d, atol=tol)
    return True


def haar_unitary(d, rng):
    Z = (rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) / np.sqrt(2)
    Qm, Rm = np.linalg.qr(Z)
    return Qm * (np.diag(Rm) / np.abs(np.diag(Rm)))


# ----------------------------------------------------------------------------------------------
# Equiangular tight frames (EAMs)
# ----------------------------------------------------------------------------------------------
def etf_harmonic(n, D):
    """harmonic ETF from a (n, k, lambda) difference set D in Z_n: n unit vectors in C^k (columns)."""
    D = list(D)
    k = len(D)
    om = np.exp(2j * np.pi / n)
    return np.array([[om ** ((a * s) % n) for a in range(n)] for s in D]) / np.sqrt(k)


def etf_simplex(d):
    """n = d+1 vectors in C^d: projections of standard basis of C^{d+1} onto 1^perp, normalised."""
    n = d + 1
    F = np.fft.fft(np.eye(n)) / np.sqrt(n)   # unitary DFT
    Vs = F[1:, :]                              # remove the all-ones row -> rows orthonormal, columns in C^d
    Vs = Vs / np.linalg.norm(Vs, axis=0, keepdims=True)
    return Vs.astype(complex)


def sic_qubit():
    # tetrahedron
    vs = []
    th = np.arccos(-1 / 3)
    vs.append(np.array([1, 0], dtype=complex))
    for j in range(3):
        ph = 2 * np.pi * j / 3
        vs.append(np.array([np.cos(th / 2), np.exp(1j * ph) * np.sin(th / 2)]))
    return np.array(vs).T


def sic_qutrit():
    # Hesse SIC: WH orbit of (0, 1, -1)/sqrt2
    om = np.exp(2j * np.pi / 3)
    fid = np.array([0, 1, -1], dtype=complex) / np.sqrt(2)
    Xs = np.roll(np.eye(3), 1, axis=0)
    Zs = np.diag([1, om, om ** 2])
    vs = []
    for p in range(3):
        for q in range(3):
            vs.append(np.linalg.matrix_power(Xs, p) @ np.linalg.matrix_power(Zs, q) @ fid)
    return np.array(vs).T


def check_etf(Vs, tol=1e-10):
    d, n = Vs.shape
    G = np.abs(Vs.conj().T @ Vs) ** 2
    c = (n - d) / (d * (n - 1))
    off = G[~np.eye(n, dtype=bool)]
    assert np.allclose(np.diag(G), 1, atol=tol)
    assert np.allclose(off, c, atol=tol), (off.min(), off.max(), c)
    assert np.allclose(Vs @ Vs.conj().T, (n / d) * np.eye(d), atol=tol)
    return True


# ----------------------------------------------------------------------------------------------
# correlation matrices and the bounds
# ----------------------------------------------------------------------------------------------
def Qmat(X, EA, FB):
    """Q_{(k,a),(l,b)} = |<e^k_a|X|f^l_b>|^2 ; EA, FB lists of unitaries (columns = basis vectors)."""
    return np.block([[np.abs(Ek.conj().T @ X @ Fl) ** 2 for Fl in FB] for Ek in EA])


def Pframe(X, VA, VB, wA, wB):
    """P_{ab} = wA wB |<psi_a|X|phi_b>|^2 for frames VA (dA x nA), VB (dB x nB) (columns = vectors)."""
    return wA * wB * np.abs(VA.conj().T @ X @ VB) ** 2


def trnorm(M):
    return np.linalg.svd(M, compute_uv=False).sum()


def psd_abs(X):
    """|X| = (X^dag X)^{1/2}, |X^dag| = (X X^dag)^{1/2}, via SVD."""
    U, s, Vh = np.linalg.svd(X)
    k = len(s)
    absX = (Vh.conj().T[:, :k] * s) @ Vh[:k, :]
    absXd = (U[:, :k] * s) @ U[:, :k].conj().T
    return absXd, absX


def IC(A, bases):
    """index of coincidence sum_k sum_a <e^k_a|A|e^k_a>^2 (A Hermitian)."""
    return sum(np.sum(np.real(np.einsum('ia,ij,ja->a', B.conj(), A, B)) ** 2) for B in bases)


def ICframe(A, V):
    return np.sum(np.real(np.einsum('ia,ij,ja->a', V.conj(), A, V)) ** 2)


def gram_factors(X, EA, FB):
    """Xi (columns xi_{ka} = x (x) conj x, x = L e) and H (columns y (x) conj y, y = W R f)."""
    U, s, Vh = np.linalg.svd(X, full_matrices=False)
    L = (U * np.sqrt(s)) @ U.conj().T
    R = (Vh.conj().T * np.sqrt(s)) @ Vh
    W = U @ Vh
    xs = np.concatenate([L @ E for E in EA], axis=1)
    ys = np.concatenate([W @ R @ F for F in FB], axis=1)
    Xi = np.einsum('ia,ja->ija', xs, xs.conj()).reshape(-1, xs.shape[1])
    H = np.einsum('ia,ja->ija', ys, ys.conj()).reshape(-1, ys.shape[1])
    return Xi, H, L, W, R


def random_X(dA, dB, rank, rng, flat=False):
    A = rng.normal(size=(dA, rank)) + 1j * rng.normal(size=(dA, rank))
    B = rng.normal(size=(dB, rank)) + 1j * rng.normal(size=(dB, rank))
    if flat:  # equal singular values
        A, _ = np.linalg.qr(A)
        B, _ = np.linalg.qr(B)
    X = A @ B.conj().T
    return X / np.linalg.norm(X)
