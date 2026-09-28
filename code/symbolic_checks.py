"""symbolic_checks.py -- sympy verification of the algebraic identities used in the proof write-up."""
import sympy as sp
d, n, m, r, t2, N = sp.symbols('d n m r tau2 N', positive=True)
c = (n - d) / (d * (n - 1))
# EAM Gram eigenvalues
assert sp.simplify(1 + (n - 1) * c - n / d) == 0
assert sp.simplify(1 - c - n * (d - 1) / (d * (n - 1))) == 0
# Theorem 3 algebra
lhs = (d / n) ** 2 * ((n / d**2) * t2 + n * (d - 1) / (d * (n - 1)) * (N - t2 / d))
assert sp.simplify(lhs - ((n - d) * t2 + d * (d - 1) * N) / (n * (n - 1))) == 0
# Conj-2 at N=1, tau2=r
assert sp.simplify(lhs.subs({N: 1, t2: r}) - (d * (d - 1) + r * (n - d)) / (n * (n - 1))) == 0
# r=1 equality value for X = |psi_1><psi_1|  (d/n)^2 [1 + (n-1) c^2]
assert sp.simplify((d / n) ** 2 * (1 + (n - 1) * c**2) - (d * (d - 1) + (n - d)) / (n * (n - 1))) == 0
# r=d value d/n
assert sp.simplify(lhs.subs({N: 1, t2: d}) - d / n) == 0
# Conj-3 equality value X = Pi_S/sqrt r
assert sp.simplify((r + (m - 1) * d * (r / d) ** 2) / r - (1 + (m - 1) * r / d)) == 0
# template  beta + (alpha - beta) r/d
tmpl = lambda al, be: be + (al - be) * r / d
assert sp.simplify(tmpl(m, 1) - (1 + (m - 1) * r / d)) == 0                                   # MUB
assert sp.simplify(tmpl(d / n, d * (d - 1) / (n * (n - 1))) - (d * (d - 1) + r * (n - d)) / (n * (n - 1))) == 0  # EAM
assert sp.simplify(tmpl(1 / d, 1 / (d * (d + 1))) - (1 + r) / (d * (d + 1))) == 0              # SIC (Result 1)
assert sp.simplify(tmpl(d + 1, 1) - (1 + r)) == 0                                              # complete MUB (Result 2)
# EAM (alpha,beta) from frame: alpha = (d/n)^2 * n/d, beta = (d/n)^2 (1-c)
assert sp.simplify((d / n) ** 2 * n / d - d / n) == 0
assert sp.simplify((d / n) ** 2 * (1 - c) - d * (d - 1) / (n * (n - 1))) == 0
# triangle-inequality bound minus Hoelder bound = (tau2 - N)((d+1)beta - alpha)/d
al, be = sp.symbols('alpha beta', positive=True)
tri = be * t2 + (al - be) * N / d
hol = al * t2 / d + be * (N - t2 / d)
assert sp.simplify(tri - hol - (t2 - N) * ((d + 1) * be - al) / d) == 0
# equal-weight rank-one POVM: Tr S = d^2/n = alpha + sum traceless eigs <= alpha + (d^2-1) beta  => (d+1) beta >= alpha
assert sp.simplify(((d**2 / n - d / n) / (d**2 - 1)) * (d + 1) - d / n) == 0
# Conjecture 1 constant
dA, dB = sp.symbols('d_A d_B', positive=True)
K = sp.sqrt(dA * (dA + 1)) * sp.sqrt(dB * (dB + 1))
assert sp.simplify(1 / (dA * dB) * sp.sqrt(dA / (dA + 1)) * sp.sqrt(dB / (dB + 1)) - 1 / K) == 0
print("all symbolic identities OK")
