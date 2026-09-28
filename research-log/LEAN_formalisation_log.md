# P-LEAN log: Tavakoli–Morelli Conjecture 3 (Schmidt number bound for incomplete MUB sets)

Check command (from the project root `formal-conjectures/`, with `C:\Users\anshm\.elan\bin` on PATH):

    lake env lean TMProof/TM.lean

Toolchain: `leanprover/lean4:v4.33.1`, Mathlib from the existing `.lake` cache (no rebuild,
no `lake update`). `import Mathlib` takes ~25 s warm (~115 s cold); the whole file checks in
~30–60 s.

## Source check

arXiv:2402.09972v2 (HTML), Conjecture 3: for any bipartite state of Schmidt number `r` and
`m < d+1` MUBs on each side, `‖Q_m‖_tr ≤ 1 + (m−1)r/d`, where `Q_m` is the `md × md` matrix
`[Q_m]_{al,bk} = ⟨g_a^l, h_b^k| ρ |g_a^l, h_b^k⟩` (joint outcome probabilities, no complex
conjugation), and `‖A‖_tr = tr √(A†A)` (sum of singular values).

## Status: COMPLETE (no `sorry`, no new axioms)

`#print axioms` for `schmidt_mub_bound`, `schmidt_mub_bound_mixed`,
`tavakoli_morelli_conjecture_3_dual`, `tavakoli_morelli_conjecture_3`:
`[propext, Classical.choice, Quot.sound]` (Lean's standard axioms only).

## Progress

- 2026-09-27: environment checked (`lake env lean` works with `import Mathlib`, no rebuild).
- Design: vectors are plain functions `Fin d → ℂ`; `ip x y = ∑ i, conj (x i) * y i`
  (physics convention), shown equal to Mathlib's `inner ℂ` on `EuclideanSpace` (`ip_eq_inner`).
  Orthonormal bases are `d` orthonormal vectors in `ℂ^d`; completeness (`∑ₐ eₐ eₐ† = I`) is
  derived via `mul_eq_one_comm` for square matrices.
- DONE: inner-product API, completeness + Parseval, Hilbert–Schmidt lemmas,
  `‖A − (τ/d)I‖² = Σσ² − τ²/d`.
- DONE: **Lemma 2** (`mub_bessel`), in the Hilbert–Schmidt space `Fin d × Fin d → ℂ`, by an
  orthogonal-projection (Pythagoras) argument: with `Y = A − (τ/d) I` and
  `B = Σ_{k,a} α_{ka} P_{ka}`, one has `⟪P_{ka}, Y⟫ = ⟪P_{ka}, B⟫ = α_{ka}` (MUB condition +
  `Σ_a α_{ka} = 0`), hence `⟪B, Y−B⟫ = 0` and `‖Y‖² = ‖Y−B‖² + ‖B‖² ≥ ‖B‖² = Σ α²`.
  (Equivalent to the task's `Tr((A₀ − ΣB_k)†(A₀ − ΣB_k)) ≥ 0` argument.) Holds for all real σ.
- DONE: **Lemma 1** (`orthogonal_weighted_sum_le`), via `|⟨x|y⟩|² = Σ_{s,t} P R`,
  `Real.sum_mul_le_sqrt_mul_sqrt` over `(i,s,t)` and norm preservation by `O`
  (`orthogonal_normSq_sum`). The sum is real; it is bounded by the modulus of its complex cast.
- DONE: **main pure-state theorem** (`schmidt_mub_bound`), no side conditions. Edge cases:
  `d = 0` (empty index sets); `m = 0` needs `r ≤ d`, proved in `card_le_of_isOrthonormal`
  from `‖A − (r/d)I‖² = r − r²/d ≥ 0`.
- DONE: mixed states: `ensembleDensity p Ψ = Σ_t p_t |Ψ_t⟩⟨Ψ_t|`,
  `probMatrix e f ρ = (Re ⟨e_i⊗f_j|ρ|e_i⊗f_j⟩)_{ij}`, `probMatrix_ensembleDensity` (linearity),
  `schmidt_mub_bound_mixed`.
- DONE: Schmidt-number predicate `HasSchmidtNumberLE ρ r` (finite convex combination of
  projectors onto unit vectors with a Schmidt decomposition of `k ≤ r` terms) and the headline
  theorems (need `1 ≤ m`, because for `m = 0` the bound is not monotone in `r`):
  `tavakoli_morelli_conjecture_3_dual` (`Tr(Oᵀ Q) ≤ 1 + (m−1)r/d` for all orthogonal `O`) and
  `tavakoli_morelli_conjecture_3` (`traceNorm Q ≤ 1 + (m−1)r/d`).
- DONE (beyond the task's O-form): trace norm `traceNorm Q = Σᵢ √λᵢ(QᵀQ)` (sum of singular
  values, via `Matrix.IsHermitian.eigenvalues`), SVD `exists_svd` (from Mathlib's spectral
  theorem + `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), and the variational
  formula `isGreatest_traceNorm : ‖Q‖_tr = max_{O ∈ O(n)} Tr(OᵀQ)`. So the conjecture is
  proved literally in trace-norm form, not only in the dual form.
- Bridges/sanity: `isOrthonormal_iff_orthonormal` (= Mathlib `Orthonormal`),
  `isMUB_of_orthonormalBasis`; non-vacuity examples: `qubitMUBs_isMUB` (computational +
  Hadamard bases of `ℂ²`), `bellState : SchmidtState 2 2`, and the main theorem instantiated
  (bound `2`).
- Scratch files (`Draft1.lean`, `Test0.lean`) were moved out of `TMProof/` to the session
  scratchpad; `TMProof/` holds only `TM.lean` and this log.

## Conjecture 2 (equiangular measurements): `TM2.lean` — COMPLETE (2026-09-28)

`TM2.lean` imports `TM.lean`, so compile `TM.lean` to an `.olean` first (from the project root):

    mkdir -p .lake/build/lib/lean/TMProof
    lake env lean -o .lake/build/lib/lean/TMProof/TM.olean -i .lake/build/lib/lean/TMProof/TM.ilean TMProof/TM.lean
    lake env lean TMProof/TM2.lean

About 35 s + 40 s. `TM.lean` is unchanged. `#print axioms` for all main results:
`[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`.

- Convention (arXiv:2402.09972v2, checked): EAM = `n` unit vectors with
  `∑ₐ |ψₐ⟩⟨ψₐ| = (n/d) I` (entrywise in `IsEAM.tight`) and
  `|⟨ψₐ|ψ_b⟩|² = (n−d)/(d(n−1))` (`eamOverlap`); POVM `Eₐ = (d/n)|ψₐ⟩⟨ψₐ|` (`eamPOVM`);
  `P_{ab} = (d/n)² Re⟨ψₐ⊗φ_b|ρ|ψₐ⊗φ_b⟩` (`eamProbMatrix`), proved equal to
  `Re Tr[ρ (Eₐ ⊗ F_b)]` (`eamProbMatrix_eq_trace`, Kronecker product).
- Lemma 2′ `eam_bessel` (needs `n ≥ 2`): Pythagoras-type argument with
  `‖(1−c)Y − B‖² ≥ 0`; the case `c = 1` (`d = 1`) is handled by `B = 0`.
- Main: `schmidt_eam_bound` (pure, Schmidt form, dual), `schmidt_eam_bound_mixed`,
  `tavakoli_morelli_conjecture_2_dual` (`n ≥ 2`), `traceNorm_eamProbMatrix_le` (`n ≥ 2`),
  `tavakoli_morelli_conjecture_2` (`d < n`, as in the paper), plus trace-norm forms for pure
  states and ensembles. `n ≥ d` is derived from the EAM axioms (`IsEAM.le`, from `c ≥ 0`).
- Hypothesis `n ≥ 2` is needed: for `n = d = 1` the bound is `0/0 = 0` in Lean, but `P = 1`.
- Sanity: `trine_isEAM` (qubit trine, `n = 3`, `d = 2`); the main theorem instantiated with
  `bellState` (bound `2/3`); `traceNorm_trine_bellState`: `‖P‖_tr = 2/3` exactly (tight).

## Not formalized (by design)

- "Schmidt rank ≤ r" is defined by the existence of a Schmidt decomposition with at most `r`
  terms (as specified in the task), not as `rank` of the `d × d` coefficient matrix. The two
  agree by the (complex) SVD, which is not formalized here.
