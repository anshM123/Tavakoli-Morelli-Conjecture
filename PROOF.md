# Proof of the Tavakoli–Morelli Schmidt-number conjectures (arXiv:2402.09972, PRA 110, 062417 (2024))

Status: **PROVEN** and machine-checked in Lean 4 (`lean/TMProof/TM.lean` for Conjecture 3, `lean/TMProof/TM2.lean` for Conjecture 2). Also verified by an independent hand check of every step and by an
independent numerical test (`code/verify_tm_proof.py`, 3000 random instances d ∈ {3,5,7}, random MUB subsets,
independent Alice/Bob sets: Lemma 1 slack ≤ 1.2e-14, Lemma 2 ≤ 4.5e-14, Theorem ≤ 4.2e-14; tightness exact).
Discovery path: coordinator found numerically (R014) the strengthened inequality ‖Q_m(X)‖₁ ≤ ‖X‖_F² + (m−1)‖X‖₁²/d.

## Theorem 1
{e^k_a}_{k≤m_A}: MUBs in C^{d_A}; {f^l_b}_{l≤m_B}: MUBs in C^{d_B}; X ∈ C^{d_A×d_B}; Q = [|⟨e^k_a|X|f^l_b⟩|²].
With N = ‖X‖_F², τ = ‖X‖₁, IC_e(A) = Σ_{k,a}⟨e^k_a|A|e^k_a⟩²:
  ‖Q‖₁ ≤ √(IC_e(|X†|)·IC_f(|X|)) ≤ √((N + (m_A−1)τ²/d_A)(N + (m_B−1)τ²/d_B)).
Equal case: ‖Q_m‖₁ ≤ ‖X‖_F² + (m−1)‖X‖₁²/d.

**Lemma 1.** For any families {a_i} ⊂ C^{d_A}, {b_j} ⊂ C^{d_B}, M_ij = |⟨a_i|X|b_j⟩|² satisfies ‖M‖₁ ≤ IC_a(|X†|)^{1/2} IC_b(|X|)^{1/2}.
Proof. SVD X = Σσ_s|u_s⟩⟨v_s|; L = Σσ_s^{1/2}|u_s⟩⟨u_s|, R = Σσ_s^{1/2}|v_s⟩⟨v_s|, W = Σ|u_s⟩⟨v_s| ⇒ LWR = X, L² = |X†|,
R² = |X|, W†WR = R. x_i = La_i, y_j = WRb_j ⇒ ⟨a_i|X|b_j⟩ = ⟨x_i|y_j⟩. ξ_i = x_i⊗x̄_i, η_j = y_j⊗ȳ_j ⇒ ⟨ξ_i|η_j⟩ = M_ij, M = Ξ†H.
Hölder: ‖Ξ†H‖₁ ≤ ‖Ξ‖₂‖H‖₂; ‖Ξ‖₂² = Σ‖x_i‖⁴ = Σ⟨a_i|L²|a_i⟩² = IC_a(|X†|); ‖H‖₂² = Σ⟨b_j|RW†WR|b_j⟩² = IC_b(|X|). ∎

**Lemma 2.** For m MUBs and Hermitian A: IC_e(A) ≤ TrA² + (m−1)(TrA)²/d (equality iff A − (TrA/d)1 ∈ ⊕_k S_k,
S_k = {Σ_a c_a P^k_a : Σc_a = 0}). Proof: Σ_a⟨e^k_a|A|e^k_a⟩² = (TrA)²/d + ‖Π_{S_k}A₀‖², A₀ = A − (TrA/d)1; for MUBs
the S_k are mutually HS-orthogonal and orthogonal to 1 (Tr[(Σc_aP^k_a)(Σc'_bP^l_b)] = (Σc_a)(Σc'_b)/d = 0); Bessel. ∎

Apply Lemma 2 to |X†| and |X| (Tr = τ, Tr(·)² = N). ∎

## Corollaries
- **Conjecture 3 (PROVEN):** Schmidt number ≤ r ⇒ ‖Q_m‖_tr ≤ 1 + (m−1)r/d (pure states: N = 1, τ² ≤ r by Cauchy–Schwarz; mixed: convexity).
  Generalisation: independent Alice/Bob MUB sets, unequal dimensions: √((1+(m_A−1)r/d_A)(1+(m_B−1)r/d_B)).
  Tight for every (d, m, r): X = Π_S/√r with Π_S = Σ_{a∈S} P^1_a (then Q is a Gram matrix, ‖Q‖₁ = TrQ).
- **Conjecture 2 (PROVEN):** equiangular measurements with n elements (Σ|ψ_a⟩⟨ψ_a| = (n/d)1, |⟨ψ_a|ψ_b⟩|² = c = (n−d)/(d(n−1))):
  Lemma 2′: Σ_a⟨ψ_a|A|ψ_a⟩² ≤ (n/d²)(TrA)² + (1−c)(TrA² − (TrA)²/d)  (frame operator TT† = (n/d)Π_{R1} + (1−c)Π_{T(1⊥)}).
  ⇒ ‖P_n‖₁ ≤ [(n−d)τ² + d(d−1)N]/[n(n−1)] ≤ [d(d−1) + r(n−d)]/[n(n−1)].
  Tight at r = 1 and r = d always; at intermediate r (Bob aligned) iff span_R{P_a} contains a rank-r projector
  (true for SICs, ETFs from (v,k,1) difference sets; false for the simplex EAM n = d+1, where only r ∈ {1, d−1, d} are tight;
  numerically d=4, r=2: max 0.69496 < 0.7).
- **Conjecture 1:** ‖Q(ρ)‖₁ depends on the measurement only through G = Σ|aā⟩⟨aā|: G = 1 + dΦ⁺ (complete MUBs),
  d/(d+1)(1 + dΦ⁺) (SIC) ⇒ ‖Q‖ = K‖P‖ for all states. NOTE: plausibly already implied by Siudzińska, arXiv:2506.18211
  ("Measures from conical 2-designs depend only on two constants") — do NOT claim as new.
- General template: rank-one POVMs w_i|a_i⟩⟨a_i| with frame superoperator S(1) = α1 and largest traceless eigenvalue β give
  ‖P‖_tr ≤ Π_{A,B}[β + (α−β)r/d]^{1/2}  (MUBs (m,1); EAM (d/n, d(d−1)/(n(n−1))); SIC (1/d, 1/(d(d+1)))).
- Why the original paper got stuck: the triangle inequality over Schmidt terms gives τ² + (m−1)N/d, weaker by (τ²−N)(d+1−m)/d.

## Novelty check
- All 21 papers citing 2402.09972 (Semantic Scholar) screened by P-TM (incl. 2608.02439, Aug 2026); closest 2412.10074, 2505.02297 use triangle-inequality bounds; none addresses Conj. 2/3.
- Coordinator: 2506.18211 (Siudzińska) full text — no mention of the conjectures; covers conical 2-designs (complete sets) only.
- WebSearch quota exhausted; Google Scholar not checked.

## Files
`code/`: tmlib.py, verify_all.py, adversarial.py (+ _out.txt), tight_eam.py (+ _out.txt), simplex_projectors.py, symbolic_checks.py; independent check verify_tm_proof.py, tm_strong.py, tm_conjecture.py.
`lean/`: the Lean 4 formalisation.
