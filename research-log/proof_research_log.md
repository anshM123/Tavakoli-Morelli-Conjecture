# P-TM LOG — proof program for Tavakoli–Morelli Conjecture 3 (arXiv:2402.09972)

Started 2026-09-27. Agent: research program agent (proof focus).

## Entry 1 — setup
- Read coordinator numerics: ../schmidt/tm_strong.py, ../schmidt/tm_conjecture.py (prime-d MUBs: computational + omega^{k j^2 + a j}/sqrt d).
- Target (strengthened): ||Q_m(X)||_1 <= ||X||_F^2 + (m-1)||X||_1^2/d for all X in M_d(C).

## Entry 2 — paper definitions (WebFetch of arXiv:2402.09972 html)
- Q_{al,bk} = <g^l_a, h^k_b| rho |g^l_a, h^k_b>, Alice MUBs {g}, Bob MUBs {h} are INDEPENDENT sets (not necessarily conjugate).
  For pure psi = vec(X): Q = |<g|X|conj(h)>|^2, i.e. Q = |<e^k_a|X|f^l_b>|^2 with e = g, f = conj(h) (again a set of MUBs).
- Conj 1: if SIC and complete MUBs exist in d_A, d_B then ||Q||_tr = K ||P||_tr, K = sqrt(d_A(d_A+1)) sqrt(d_B(d_B+1)).
- Conj 2 (EAM): n>d states, sum |psi_a><psi_a| = (n/d) 1, |<psi_a|psi_a'>|^2 = (n-d)/(d(n-1)), E_a = (d/n)|psi_a><psi_a|;
  ||P_n||_tr <= [d(d-1) + r(n-d)]/[n(n-1)] for Schmidt number r.
- Conj 3: ||Q_m||_tr <= 1 + (m-1) r/d for m < d+1 MUBs.  Proven there: ||Q_m||_tr <= (m-1)/d + r (triangle inequality over Schmidt terms).

## Entry 3 — PROOF IDEA (found analytically, to be verified numerically)
Key trick: balanced polar split X = L W R, L = |X^dag|^{1/2}, R = |X|^{1/2}, W partial isometry.
Then <e|X|f> = <x|y> with x = L e, y = W R f, and |<x|y>|^2 = <x (x) conj x | y (x) conj y>.
So Q = Xi^dag H (Gram factorization), Hoelder ||Xi^dag H||_1 <= ||Xi||_2 ||H||_2 gives
   ||Q||_1 <= sqrt( IC_e(|X^dag|) * IC_f(|X|) ),  IC_e(A) := sum_{k,a} <e^k_a|A|e^k_a>^2   (index of coincidence).
MUB/Bessel bound: IC_e(A) <= ||A||_F^2 + (m-1)(Tr A)^2/d, and ||(|X|)||_F^2 = ||X||_F^2, Tr|X| = ||X||_1.
=> ||Q||_1 <= ||X||_F^2 + (m-1)||X||_1^2/d  (strengthened inequality), hence Conj 3.
Same template with the EAM frame operator gives Conj 2 exactly; frame-operator dependence gives Conj 1.
## Entry 4 — numerical verification of every step (verify_all.py, tmlib.py)  [~5 s runtime]
MUB sets: prime d (2,3,5,7), d=4 (Pauli classes, 5 MUBs), d=6,10 (3 product MUBs), d=9 (4 product MUBs); random global
rotations for Alice / Bob independently.  ETFs: SIC2, SIC3 (Hesse), simplex d=2,3,5, harmonic (7,3),(7,4),(13,4),(11,5),(11,6),(21,5).
- T1 coordinator facts (1)-(3): all hold (Pi_k Pi_l = Phi+, P projector of rank 1+m(d-1), ||Q||_1 = ||F Y F||_1, Tr Q formula).
- T2 Gram factorisation Q = Xi^dag H: max entry error < 1e-11 on 4000 random instances (unequal dA,dB, mA,mB, ranks).
- T4 chain ||Q||_1 <= sqrt(IC IC) <= sqrt((N+(mA-1)t^2/dA)(N+(mB-1)t^2/dB)): worst slacks -3.6e-14, -2.1e-14 (rounding; X scaled up to 3).
- T3 IC (Bessel) lemma: worst relative slack -1.6e-15; equality for A in span{I} + sum_k S_k confirmed (gap 2e-15).
- T5 Conj 3 random (pure + mixed) never violated; equality X = Pi_S/sqrt r attains 1+(m-1)r/d for all d<=7, m, r (gap 4e-15).
- T6 Conj 2 (EAM): Hoelder + frame bound verified (slack ~1e-15); equality at r=1 (X=|psi_1><psi_1|) and r=d (X=I/sqrt d).
- T7 Conj 1: | ||Q||_tr - K ||P||_tr | <= 7e-15 for random mixed states, dA,dB in {2,3}, random independent rotations.
NOTE (test bug found & fixed): first run rotated each basis by a DIFFERENT Haar unitary (destroys unbiasedness) -> spurious
"violations" in T5/T7.  With ONE unitary per party all tests pass.  (Sanity: the MUB property is essential.)

## Entry 5 — adversarial.py (Adam, 64 restarts x 1500 steps, CPU 4 threads)
(A) max [||Q||_1 - N - (m-1)||X||_1^2/d] over X: d=4 (m=2..5), d=6 (m=2,3), d=3 (m=2,3), Bob aligned or Haar-rotated:
    all maxima in [+1.8e-15, +4.5e-15] = rounding, i.e. equality attained, never exceeded.
(B) max [||Q||_1/sqrt(IC_e(|X^dag|) IC_f(|X|)) - 1]: d=4 m=2,3 -> +2.4e-15, +2.9e-15 (equality); d=5 m=3 -> -1.9e-10;
    d=6 m=2,3 -> -1e-4, -6e-4 (optimizer not converged; no violation).
(C) Conj-2 tightness, max over Schmidt-rank-r pure states (64 restarts): TIGHT (gap ~1e-15) for all r in
    simplex3 (n=4,d=3), H(7,3), H(7,4), SIC3, H(13,4); simplex4 (n=5,d=4): tight r=1,3,4 but r=2: 0.694962 < 0.7.

## Entry 6 — equality analysis for Conj 2 (analytic)
Equality at Schmidt rank r  <=>  flat spectrum + Bessel equality on both sides + Hoelder equality.
Bessel equality for |X^dag| = Pi_A/sqrt(r) <=> Pi_A in span_R{P_a}.  Sufficient: X = Pi/sqrt(r), Pi a rank-r projector in
span_R{P_a}, Bob aligned (f = e) -> Q is a Gram matrix, equality.
Simplex ETF (n = d+1): span_R{P_a} = compressions J D J of real diagonal D to 1^perp.  Secular-equation/interlacing
argument: the compression has eigenvalues v^(k_v - 1) for each distinct value v of D plus one root strictly inside each gap
=> projector only if #distinct values <= 3 => rank r in {0,1,d-1,d}.  Hence for d >= 4 and 2 <= r <= d-2 the Conj-2
bound is NOT attained (strict) for the simplex EAM.  Harmonic ETFs from (v,k,1) difference sets: span = Hermitian matrices
with constant diagonal -> rank-r projectors exist for all r (Fourier projectors) -> tight for all r.  SIC: span = all -> tight.
MUBs: projector diagonal in basis 1 -> Conj-3 bound tight for all r.
Running tight_eam.py (256 restarts x 3 seeds, cosine lr) to confirm simplex4/5/6 gaps.

NOTE: harness refused creation of REPORT.md by this (sub)agent ("subagents should return findings as text");
the full proof is delivered in the hand-back message to the coordinator instead.

## Entry 7 — confirmations
- symbolic_checks.py (sympy): all algebraic identities of the write-up verified (EAM Gram eigenvalues, Thm-3 algebra,
  equality values r=1, r=d, Conj-3 equality value, template specialisations MUB/EAM/SIC/complete-MUB, triangle-vs-Hoelder
  difference (tau^2-N)((d+1)beta-alpha)/d, K constant of Conj 1).
- simplex_projectors.py: min distance of compression spectrum to a rank-r projector spectrum over D:
  d=3: 0 for all r; d=4: r=2 -> 0.11; d=5: r=2,3 -> 0.075; d=6: r=2,4 -> 0.053, r=3 -> 0.15; 0 (1e-25) for r in {0,1,d-1,d}.
- tight_eam.py (128 restarts x 2 seeds x 3000 steps, cosine lr), max ||P_n||_1 over Schmidt-rank-r states vs Conj-2 bound:
  simplex4 r=2: 0.694962 < 0.700000 (optimal svals^2 0.703/0.297, non-flat)
  simplex5 r=2: 0.731000 < 0.733333;  r=3: 0.760259 < 0.766667;  r=4: 0.800000 = bound (flat)
  simplex6 r=3: 0.782297 < 0.785714;  r=5: 0.833333 = bound (flat)
  => matches the analytic prediction: strict for 2 <= r <= d-2, tight for r in {1, d-1, d}.

## STATUS (final)
PROVEN: strengthened inequality (all d, any m MUBs, independent Alice/Bob sets, unequal dims), Conjecture 3,
Conjecture 2, Conjecture 1 (all states, all SICs/complete MUB sets), Results 1-2 of the paper as special cases.
Proof = balanced polar split X = |X^dag|^{1/2} W |X|^{1/2} + Hoelder + index-of-coincidence (Bessel) bound.
Equality: Conj-3 tight for all (d,m,r); Conj-2 tight iff a rank-r projector lies in span{P_a} (aligned Bob);
simplex EAM: not attained for 2 <= r <= d-2 (d >= 4).
