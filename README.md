# Proof of the Tavakoli–Morelli Schmidt-number conjectures (machine-checked in Lean 4)

A. Tavakoli and S. Morelli (arXiv:2402.09972, Phys. Rev. A **110**, 062417 (2024)) proposed Schmidt-number witnesses built from the trace norm of correlation (joint-probability) matrices, and conjectured sharp bounds for incomplete sets of mutually unbiased bases (MUBs) and for equiangular measurements (EAMs). We prove **Conjecture 3** and **Conjecture 2**, both with tight bounds, and formalise both proofs in **Lean 4 + Mathlib** with no `sorry` and no axioms beyond Lean's standard three.

## Results

**Theorem (Conjecture 3).** Let e, f be two sets of m ≥ 1 mutually unbiased bases of C^d (one set for Alice, one for Bob), and let ρ be a state on C^d ⊗ C^d with Schmidt number at most r. The md × md matrix of joint outcome probabilities, Q_{(k,a),(l,b)} = ⟨e^k_a ⊗ f^l_b|ρ|e^k_a ⊗ f^l_b⟩, satisfies

```
    ‖Q‖_tr  ≤  1 + (m − 1) r / d .
```

The bound is tight for every (d, m, r).
- **Stronger form:** ‖Q_m(X)‖₁ ≤ ‖X‖_F² + (m−1)‖X‖₁²/d for every coefficient matrix X of a pure state.
- **Unequal sets:** for different MUB sets and dimensions, √((1+(m_A−1)r/d_A)(1+(m_B−1)r/d_B)).

**Theorem (Conjecture 2).** Let ψ, φ be equiangular measurements with n > d elements in C^d, and ρ a state with Schmidt number at most r. The n × n joint probability matrix P satisfies

```
    ‖P‖_tr  ≤  [ d(d − 1) + r(n − d) ] / [ n(n − 1) ] .
```

It is tight at r = 1 and r = d. At intermediate r it is tight whenever the real span of the POVM elements contains a rank-r projector (e.g. SICs), but not for the simplex EAM.

Lean statements (`lean/TMProof/TM.lean`, `lean/TMProof/TM2.lean`, namespace `TMProof`):
```lean
theorem tavakoli_morelli_conjecture_3 (hm : 1 ≤ m) (e f : Fin m → Fin d → Fin d → ℂ)
    (he : IsMUB d m e) (hf : IsMUB d m f) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hρ : HasSchmidtNumberLE ρ r) :
    traceNorm (probMatrix e f ρ) ≤ 1 + ((m : ℝ) - 1) * r / d

theorem tavakoli_morelli_conjecture_2 (hdn : d < n) {ψ φ : Fin n → Fin d → ℂ}
    (hψ : IsEAM d n ψ) (hφ : IsEAM d n φ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hρ : HasSchmidtNumberLE ρ r) :
    traceNorm (eamProbMatrix ψ φ ρ) ≤ ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1))
```
Definitions used in these statements:
- `traceNorm` is the sum of singular values. It is proved equal to max over orthogonal O of Tr(OᵀQ), via an SVD built from Mathlib's spectral theorem.
- `HasSchmidtNumberLE ρ r` means ρ is a finite convex combination of pure states of Schmidt rank ≤ r.
- `IsMUB` and `IsEAM` are the standard definitions, with the bridge `isMUB_of_orthonormalBasis`.
- Non-vacuity checks are included: qubit MUBs and a Bell state.

## Proof idea (full proof: [PROOF.md](PROOF.md))
- **Lemma 1** (Hölder / Gram factorisation). For any vectors a_i, b_j, the matrix M_ij = |⟨a_i|X|b_j⟩|² satisfies ‖M‖₁ ≤ IC_a(|X†|)^{1/2} · IC_b(|X|)^{1/2}.
- **Lemma 2** (Bessel for MUB frames). For m MUBs and Hermitian A: Σ_{k,a} ⟨e^k_a|A|e^k_a⟩² ≤ Tr A² + (m−1)(Tr A)²/d.
- Combining them gives ‖Q‖₁ ≤ ‖X‖_F² + (m−1)‖X‖₁²/d. For Schmidt rank r, ‖X‖₁² ≤ r‖X‖_F², and convexity handles mixed states.
- **Conjecture 2** is the same argument with the EAM frame operator in place of Lemma 2.
- **Why the original approach stalled:** the triangle inequality over Schmidt terms only gives τ² + (m−1)N/d, which is weaker by (τ²−N)(d+1−m)/d.

## Verify
**Lean** (about 4 GB RAM, a few minutes):
```bash
cd lean
lake exe cache get      # prebuilt Mathlib at the pinned revision (0df444a3...)
bash check.sh           # compiles TM.lean and TM2.lean, prints #print axioms, greps for sorry/admit/axiom/native_decide
```
Expected result: every main theorem depends on `[propext, Classical.choice, Quot.sound]`, and the keyword grep prints `none`. The formalisation was checked in the `formal-conjectures` Lake environment with Mathlib at the same pinned revision (see `research-log/LEAN_formalisation_log.md`).

**Numerics** (Python; see `requirements.txt`: numpy/scipy/sympy, torch only for the adversarial searches; independent of the proof):
```bash
cd code
python verify_tm_proof.py      # 3000 random instances (d in {3,5,7}, random MUB subsets): slacks >= -4.2e-14
python verify_all.py           # lemma-by-lemma checks, tightness constructions
python adversarial.py          # adversarial search for violations of the strengthened inequality (max 4e-14)
```

## Status and novelty
- **Proved and machine-checked.** The proof was also checked by hand and numerically on 3000 random instances, with a sensitivity control: a deliberately broken MUB set violates the bound, as it should.
- **Novelty check:** all 21 papers citing arXiv:2402.09972 (Semantic Scholar, through Aug 2026) were screened, plus the full text of arXiv:2506.18211. No resolution of Conjectures 2 or 3 was found.
  - **Conjecture 1** (measurement independence for complete MUBs/SICs) is plausibly implied by Siudzińska, arXiv:2506.18211, and is **not** claimed here.

## Layout
- `PROOF.md`: the full mathematical proof, with corollaries and tightness.
- `lean/`: the Lean project (`TMProof/TM.lean`, `TM2.lean`, `Axioms.lean`, `check.sh`, `lakefile.toml`, `lean-toolchain`).
- `code/`: numerical verification.
- `research-log/`: working logs, including the Lean formalisation log.
