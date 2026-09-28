import TMProof.TM

/-!
# Schmidt-number bound for equiangular measurements (Tavakoli–Morelli, Conjecture 2)

This file gives a machine-checked proof of Conjecture 2 of

* A. Tavakoli and S. Morelli, *Enhanced Schmidt number criteria based on correlation trace
  norms*, arXiv:2402.09972, Phys. Rev. A **110**, 062417 (2024).

It builds on `TMProof/TM.lean` (Conjecture 3) and reuses its definitions and lemmas.

## The conjecture

An equiangular measurement (EAM) with `n` elements on `ℂ^d` is given by `n > d` unit vectors
`ψ_1, …, ψ_n` of `ℂ^d` with `∑ₐ |ψₐ⟩⟨ψₐ| = (n/d) I` and `|⟨ψₐ|ψ_b⟩|² = c = (n - d) / (d (n - 1))`
for `a ≠ b`. Its POVM elements are `Eₐ = (d/n) |ψₐ⟩⟨ψₐ|`. Alice measures an EAM `ψ` and Bob an
EAM `φ` (with the same `d` and `n`). For a state `ρ` of `ℂ^d ⊗ ℂ^d`, `P_n` is the `n × n` matrix
of joint outcome probabilities
`P_{ab} = Tr[ρ (Eₐ ⊗ F_b)] = (d/n)² ⟨ψₐ ⊗ φ_b| ρ |ψₐ ⊗ φ_b⟩`.
Conjecture 2 states: if `ρ` has Schmidt number at most `r`, then
`‖P_n‖_tr ≤ [d (d - 1) + r (n - d)] / [n (n - 1)]`.

## Conventions

We use the conventions of `TMProof/TM.lean`:
* vectors of `ℂ^d` are functions `Fin d → ℂ` and `ip x y = ∑ᵢ conj (x i) * y i`;
* `ℂ^d ⊗ ℂ^d` is `Fin d × Fin d → ℂ` and `tensor x y (p, q) = x p * y q`;
* a pure state of Schmidt rank at most `r` is given in Schmidt form (`SchmidtState d r`), and a
  state of Schmidt number at most `r` is a finite convex combination of projectors onto such
  pure states (`HasSchmidtNumberLE`);
* `traceNorm` is the trace norm (the sum of the singular values).

The frame condition of an EAM (`IsEAM`) is stated entrywise:
`∑ₐ ψₐ(x) conj (ψₐ(y)) = (n/d) δ_{xy}`. The normalisation of `P_n` (`eamProbMatrix`) includes the
POVM weights: `P_{ab} = (d/n)² ⟨ψₐ ⊗ φ_b|ρ|ψₐ ⊗ φ_b⟩`, with no complex conjugation of Bob's
vectors, exactly as in the paper. `eamProbMatrix_eq_trace` checks that
`P_{ab} = Tr[ρ (Eₐ ⊗ F_b)]` for the Kronecker product of the POVM elements (`eamPOVM`), and
`sum_eamPOVM` checks that the `Eₐ` sum to the identity.

## Main results

* `TMProof.eam_bessel` (Lemma 2′): with `wₐ = ∑ₛ σₛ |⟨ψₐ|uₛ⟩|²` and `τ = ∑ₛ σₛ`,
  `∑ₐ wₐ² ≤ n τ² / d² + (1 - c) (∑ₛ σₛ² - τ² / d)`.
* `TMProof.schmidt_eam_bound`: for a pure state in Schmidt form with `r` terms and every real
  orthogonal `O`, `∑_{a,b} O_{ab} P_{ab} ≤ [d(d-1) + r(n-d)] / [n(n-1)]`.
* `TMProof.schmidt_eam_bound_mixed`: the same bound for finite ensembles of such states.
* `TMProof.tavakoli_morelli_conjecture_2_dual`: the dual bound for every state of Schmidt
  number at most `r`.
* `TMProof.tavakoli_morelli_conjecture_2`: Conjecture 2 as stated in the paper (`n > d`),
  `‖P_n‖_tr ≤ [d(d-1) + r(n-d)] / [n(n-1)]`. `TMProof.traceNorm_eamProbMatrix_le` is the same
  bound under the weaker hypothesis `n ≥ 2`.
* Sanity checks: the qubit trine is an EAM (`TMProof.trine_isEAM`, `n = 3`, `d = 2`), and for
  the trine on both sides and the maximally entangled two-qubit state the bound `2/3` is
  attained exactly (`TMProof.traceNorm_trine_bellState`).

## Proof outline

1. As for Conjecture 3, `⟨ψₐ ⊗ φ_b|Ψ⟩ = ⟨xₐ|y_b⟩` with `(xₐ)ₛ = √σₛ conj ⟨ψₐ|uₛ⟩` and
   `(y_b)ₛ = √σₛ ⟨φ_b|vₛ⟩`. Lemma 1 (`orthogonal_weighted_sum_le`) gives
   `∑_{a,b} O_{ab} |⟨xₐ|y_b⟩|² ≤ √(∑ₐ ‖xₐ‖⁴) √(∑_b ‖y_b‖⁴)`, and `‖xₐ‖² = wₐ`.
2. Lemma 2′ in the Hilbert–Schmidt space: let `A = ∑ₛ σₛ |uₛ⟩⟨uₛ|`, `Y = A - (τ/d) I`,
   `Pₐ = |ψₐ⟩⟨ψₐ|`, `αₐ = wₐ - τ/d = ⟨Pₐ, Y⟩` and `B = ∑ₐ αₐ Pₐ`. The frame condition gives
   `∑ₐ αₐ = 0`. The Gram matrix `⟨Pₐ, P_b⟩ = (1 - c) δ_{ab} + c` then gives
   `⟨Pₐ, B⟩ = (1 - c) αₐ`. Hence `⟨B, Y⟩ = ∑ α²`, `‖B‖² = (1 - c) ∑ α²` and
   `0 ≤ ‖(1 - c) Y - B‖² = (1 - c) ((1 - c) ‖Y‖² - ∑ α²)`, so `∑ α² ≤ (1 - c) ‖Y‖²`. (If `c = 1`,
   then `B = 0` and `∑ α² = ⟨B, Y⟩ = 0`.) Finally `∑ w² = ∑ α² + n τ² / d²` and
   `‖Y‖² = ∑ σ² - τ² / d`.
3. With `∑ σ² = 1`: `(d/n)² [n τ² / d² + (1 - c) (1 - τ² / d)] = [d(d-1) + τ²(n-d)] / [n(n-1)]`.
   This is at most the claimed bound, since `τ² ≤ r` and `n ≥ d`.
4. Mixed states follow by linearity. The trace-norm form follows from
   `traceNorm_le_of_forall_orthogonal`.
-/

open scoped BigOperators ComplexConjugate
open Finset

noncomputable section

namespace TMProof

/-! ## Equiangular measurements -/

section EAM

variable {d n r : ℕ}

/-- A vector of zero norm is zero. -/
lemma eq_zero_of_sqNorm_eq_zero {ι : Type*} [Fintype ι] {x : ι → ℂ} (h : sqNorm x = 0) :
    x = 0 := by
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (x j)).mp h i
    (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp hi

/-- The overlap `c = (n - d) / (d (n - 1))` of an equiangular measurement with `n` elements in
`ℂ^d`. -/
def eamOverlap (d n : ℕ) : ℝ := ((n : ℝ) - d) / (d * ((n : ℝ) - 1))

/-- `IsEAM d n ψ`: the `n` vectors `ψ a` of `ℂ^d` form an equiangular measurement. They are unit
vectors, they form a tight frame `∑ₐ |ψₐ⟩⟨ψₐ| = (n/d) I` (stated entrywise), and
`|⟨ψₐ|ψ_b⟩|² = eamOverlap d n = (n - d) / (d (n - 1))` for `a ≠ b`. The POVM elements are
`Eₐ = (d/n) |ψₐ⟩⟨ψₐ|` (`eamPOVM`). -/
structure IsEAM (d n : ℕ) (ψ : Fin n → Fin d → ℂ) : Prop where
  /-- Each `ψₐ` is a unit vector. -/
  unit : ∀ a, sqNorm (ψ a) = 1
  /-- Tight frame: `∑ₐ |ψₐ⟩⟨ψₐ| = (n/d) I`, entrywise. -/
  tight : ∀ x y, ∑ a, ψ a x * conj (ψ a y) = if x = y then (n : ℂ) / d else 0
  /-- Equiangularity: `|⟨ψₐ|ψ_b⟩|² = (n - d) / (d (n - 1))` for `a ≠ b`. -/
  equiangular : ∀ a b, a ≠ b → Complex.normSq (ip (ψ a) (ψ b)) = eamOverlap d n

namespace IsEAM

variable {ψ : Fin n → Fin d → ℂ}

/-- An EAM with at least one element lives in a space of dimension `d ≥ 1`. -/
lemma d_pos (hψ : IsEAM d n ψ) (hn : 1 ≤ n) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have h := hψ.unit ⟨0, hn⟩
    simp [sqNorm] at h
  · exact hd

/-- `n > d` forces `n ≥ 2` for an EAM. -/
lemma two_le_of_lt (hψ : IsEAM d n ψ) (h : d < n) : 2 ≤ n := by
  by_contra hlt
  have := hψ.d_pos (by omega)
  omega

/-- The Gram matrix of the projectors `Pₐ = |ψₐ⟩⟨ψₐ|`: `|⟨ψₐ|ψ_b⟩|² = 1` if `a = b` and `c`
otherwise. -/
lemma normSq_ip (hψ : IsEAM d n ψ) (a b : Fin n) :
    Complex.normSq (ip (ψ a) (ψ b)) = if a = b then 1 else eamOverlap d n := by
  split_ifs with h
  · subst h
    rw [ip_self, Complex.normSq_ofReal, hψ.unit a, mul_one]
  · exact hψ.equiangular a b h

/-- `d ≤ n` for an EAM with at least two elements (because `c ≥ 0`). -/
lemma le (hψ : IsEAM d n ψ) (hn : 2 ≤ n) : d ≤ n := by
  have hd : 0 < d := hψ.d_pos (by omega)
  have h := hψ.equiangular ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
  have h0 : 0 ≤ eamOverlap d n := by rw [← h]; exact Complex.normSq_nonneg _
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) * ((n : ℝ) - 1) := mul_pos hdR (by linarith)
  have hnd : (0 : ℝ) ≤ (n : ℝ) - d := by
    have := mul_nonneg h0 hden.le
    rwa [eamOverlap, div_mul_cancel₀ _ hden.ne'] at this
  have : (d : ℝ) ≤ n := by linarith
  exact_mod_cast this

/-- `c ≤ 1` for an EAM with at least two elements. -/
lemma eamOverlap_le_one (hψ : IsEAM d n ψ) (hn : 2 ≤ n) : eamOverlap d n ≤ 1 := by
  have hd : 0 < d := hψ.d_pos (by omega)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  rw [eamOverlap, div_le_one hden]
  nlinarith

/-- Parseval-type identity for an EAM: `∑ₐ |⟨ψₐ|v⟩|² = (n/d) ‖v‖²`. -/
lemma parseval (hψ : IsEAM d n ψ) (v : Fin d → ℂ) :
    ∑ a, Complex.normSq (ip (ψ a) v) = (n / d : ℝ) * sqNorm v := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← ip_mul_ip_swap]
  rw [← ip_self]
  calc ∑ a, ip (ψ a) v * ip v (ψ a)
      = ∑ a, ∑ x, ∑ y, conj (v y) * v x * (ψ a y * conj (ψ a x)) := by
        simp only [ip, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ x, ∑ y, conj (v y) * v x * ∑ a, ψ a y * conj (ψ a x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = (n / d : ℂ) * ip v v := by
        simp only [hψ.tight, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        simp only [ip, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring

end IsEAM

/-- The weights `wₐ = ∑ₛ σₛ |⟨ψₐ|uₛ⟩|² = ⟨ψₐ| A |ψₐ⟩` of `A = ∑ₛ σₛ |uₛ⟩⟨uₛ|`. -/
def frameWeight (ψ : Fin n → Fin d → ℂ) (σ : Fin r → ℝ) (u : Fin r → Fin d → ℂ) (a : Fin n) :
    ℝ :=
  ∑ s, σ s * Complex.normSq (ip (ψ a) (u s))

/-- `∑ₐ wₐ = (n/d) τ` (frame condition): `∑ₐ ⟨ψₐ|A|ψₐ⟩ = (n/d) Tr A`. -/
lemma sum_frameWeight {ψ : Fin n → Fin d → ℂ} (hψ : IsEAM d n ψ) (σ : Fin r → ℝ)
    {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) :
    ∑ a, frameWeight ψ σ u a = (n / d : ℝ) * ∑ s, σ s := by
  simp only [frameWeight]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, hψ.parseval, hu.sqNorm_eq_one]
  ring

/-- **Lemma 2′ (Bessel inequality for EAMs).** Let `ψ` be an EAM with `n ≥ 2` elements in `ℂ^d`
and `c = eamOverlap d n`. Let `u` be an orthonormal family, `σ` real weights, `τ = ∑ₛ σₛ` and
`wₐ = ∑ₛ σₛ |⟨ψₐ|uₛ⟩|² = ⟨ψₐ|A|ψₐ⟩` with `A = ∑ₛ σₛ |uₛ⟩⟨uₛ|`. Then
`∑ₐ wₐ² ≤ n τ² / d² + (1 - c) (∑ₛ σₛ² - τ² / d)`. -/
theorem eam_bessel (hn : 2 ≤ n) {ψ : Fin n → Fin d → ℂ} (hψ : IsEAM d n ψ) (σ : Fin r → ℝ)
    {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) :
    ∑ a, frameWeight ψ σ u a ^ 2 ≤
      n * (∑ s, σ s) ^ 2 / d ^ 2 +
        (1 - eamOverlap d n) * (∑ s, σ s ^ 2 - (∑ s, σ s) ^ 2 / d) := by
  have hd : 0 < d := hψ.d_pos (by omega)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hc1 : 0 ≤ 1 - eamOverlap d n := sub_nonneg.mpr (hψ.eamOverlap_le_one hn)
  set τ : ℝ := ∑ s, σ s with hτ
  set α : Fin n → ℝ := fun a => frameWeight ψ σ u a - τ / d with hα
  set Y : Fin d × Fin d → ℂ := schmidtOp σ u - ((τ / d : ℝ) : ℂ) • idVec with hY
  set B : Fin d × Fin d → ℂ := ∑ a, (α a : ℂ) • outer (ψ a) with hB
  -- the coefficients `α` sum to zero (frame condition)
  have hα0 : ∑ a, α a = 0 := by
    simp only [hα, Finset.sum_sub_distrib, sum_frameWeight hψ σ hu, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  -- `⟨Pₐ, Y⟩ = αₐ`
  have hPY : ∀ a, ip (outer (ψ a)) Y = (α a : ℂ) := by
    intro a
    rw [hY, ip_sub_right, ip_smul_right, ip_outer_schmidtOp, ip_outer_idVec, hψ.unit a]
    simp [hα, frameWeight]
  -- `⟨Pₐ, B⟩ = (1 - c) αₐ` (Gram matrix `(1 - c) δ + c` and `∑ α = 0`)
  have hPB : ∀ a, ip (outer (ψ a)) B = (((1 - eamOverlap d n) * α a : ℝ) : ℂ) := by
    intro a
    have hreal : ∑ b, α b * Complex.normSq (ip (ψ a) (ψ b)) = (1 - eamOverlap d n) * α a := by
      have h : ∀ b, α b * Complex.normSq (ip (ψ a) (ψ b)) =
          eamOverlap d n * α b + (1 - eamOverlap d n) * (if a = b then α b else 0) := by
        intro b
        rw [hψ.normSq_ip]
        split_ifs <;> ring
      simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hα0, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      ring
    rw [hB, ip_sum_right]
    simp only [ip_smul_right, ip_outer_outer]
    rw [← hreal]
    push_cast
    rfl
  -- `⟨B, Y⟩ = ∑ α²`
  have hBY : ip B Y = ((∑ a, α a ^ 2 : ℝ) : ℂ) := by
    conv_lhs => arg 1; rw [hB]
    simp only [ip_sum_left, ip_smul_left, hPY, Complex.conj_ofReal]
    push_cast
    refine Finset.sum_congr rfl fun a _ => by ring
  have hYB : ip Y B = ((∑ a, α a ^ 2 : ℝ) : ℂ) := by
    rw [← conj_ip, hBY, Complex.conj_ofReal]
  -- `‖B‖² = (1 - c) ∑ α²`
  have hBB : ip B B = (((1 - eamOverlap d n) * ∑ a, α a ^ 2 : ℝ) : ℂ) := by
    conv_lhs => arg 1; rw [hB]
    simp only [ip_sum_left, ip_smul_left, hPB, Complex.conj_ofReal]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring
  -- `‖Y‖² = ∑ σ² - τ² / d`
  have hYY := ip_centered_schmidtOp σ hu hd.ne'
  rw [← hτ, ← hY] at hYY
  -- `0 ≤ ‖(1 - c) Y - B‖² = (1 - c) ((1 - c) ‖Y‖² - ∑ α²)`
  have hZ : ip (((1 - eamOverlap d n : ℝ) : ℂ) • Y - B) (((1 - eamOverlap d n : ℝ) : ℂ) • Y - B) =
      (((1 - eamOverlap d n) * ((1 - eamOverlap d n) * (∑ s, σ s ^ 2 - τ ^ 2 / d) -
        ∑ a, α a ^ 2) : ℝ) : ℂ) := by
    rw [ip_sub_left, ip_sub_right, ip_sub_right, ip_smul_left, ip_smul_left, ip_smul_right,
      ip_smul_right, hYY, hYB, hBY, hBB, Complex.conj_ofReal]
    push_cast
    ring
  rw [ip_self] at hZ
  have hZ' : sqNorm (((1 - eamOverlap d n : ℝ) : ℂ) • Y - B) =
      (1 - eamOverlap d n) * ((1 - eamOverlap d n) * (∑ s, σ s ^ 2 - τ ^ 2 / d) -
        ∑ a, α a ^ 2) := by
    exact_mod_cast hZ
  have hZn := sqNorm_nonneg (((1 - eamOverlap d n : ℝ) : ℂ) • Y - B)
  have hSle : ∑ a, α a ^ 2 ≤ (1 - eamOverlap d n) * (∑ s, σ s ^ 2 - τ ^ 2 / d) := by
    rcases hc1.lt_or_eq with hpos | hzero
    · rw [hZ'] at hZn
      have := (mul_nonneg_iff_of_pos_left hpos).mp hZn
      linarith
    · -- `c = 1`: then `‖B‖² = 0`, so `B = 0` and `∑ α² = ⟨B, Y⟩ = 0`
      rw [← hzero, zero_mul, Complex.ofReal_zero, ip_self] at hBB
      have hB0 : B = 0 := eq_zero_of_sqNorm_eq_zero (by exact_mod_cast hBB)
      have hS : ((∑ a, α a ^ 2 : ℝ) : ℂ) = 0 := by
        rw [← hBY, hB0]
        simp [ip]
      rw [Complex.ofReal_eq_zero.mp hS, ← hzero, zero_mul]
  -- `∑ w² = ∑ α² + n τ² / d²`
  have hw : ∀ a, frameWeight ψ σ u a = α a + τ / d := fun a => by simp [hα]
  have hsum : ∑ a, frameWeight ψ σ u a ^ 2 = ∑ a, α a ^ 2 + n * τ ^ 2 / d ^ 2 := by
    simp only [hw, add_sq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hα0]
    field_simp
    ring
  rw [hsum]
  linarith

end EAM

/-! ## The probability matrix `P_n` -/

section ProbMatrix

variable {d n : ℕ}

/-- The EAM POVM element `Eₐ = (d/n) |ψₐ⟩⟨ψₐ|`, as a `d × d` matrix. -/
def eamPOVM (ψ : Fin n → Fin d → ℂ) (a : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  ((d : ℂ) / n) • Matrix.vecMulVec (ψ a) (star (ψ a))

/-- The POVM elements of an EAM sum to the identity. -/
lemma sum_eamPOVM {ψ : Fin n → Fin d → ℂ} (hψ : IsEAM d n ψ) (hn : 1 ≤ n) :
    ∑ a, eamPOVM ψ a = 1 := by
  have hd : 0 < d := hψ.d_pos hn
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  ext x y
  simp only [eamPOVM, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def, smul_eq_mul, ← Finset.mul_sum, hψ.tight, Matrix.one_apply]
  split_ifs
  · field_simp
  · ring

/-- The matrix `P_n` of Tavakoli–Morelli for a state `ρ`: Alice measures the EAM `ψ` and Bob
the EAM `φ`, and `P_{ab} = Tr[ρ (Eₐ ⊗ F_b)] = (d/n)² ⟨ψₐ ⊗ φ_b| ρ |ψₐ ⊗ φ_b⟩` (real part). -/
def eamProbMatrix (ψ φ : Fin n → Fin d → ℂ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b =>
    ((d : ℝ) / n) ^ 2 * (ip (tensor (ψ a) (φ b)) (ρ.mulVec (tensor (ψ a) (φ b)))).re

/-- The matrix `P_n` for a pure state `Ψ`: `P_{ab} = (d/n)² |⟨ψₐ ⊗ φ_b|Ψ⟩|²`. -/
def eamPureProbMatrix (ψ φ : Fin n → Fin d → ℂ) (Ψ : Fin d × Fin d → ℂ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => ((d : ℝ) / n) ^ 2 * Complex.normSq (ip (tensor (ψ a) (φ b)) Ψ)

/-- `P_{ab} = Tr[ρ (Eₐ ⊗ F_b)]` (real part), with the Kronecker product of the POVM elements. -/
lemma eamProbMatrix_eq_trace (ψ φ : Fin n → Fin d → ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (a b : Fin n) :
    eamProbMatrix ψ φ ρ a b =
      (ρ * Matrix.kroneckerMap (· * ·) (eamPOVM ψ a) (eamPOVM φ b)).trace.re := by
  simp only [eamProbMatrix, Matrix.of_apply]
  rw [← Complex.re_ofReal_mul]
  congr 1
  push_cast
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply, eamPOVM,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, smul_eq_mul, ip,
    tensor, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [map_mul]
  ring

/-- For an ensemble, `P_n` is the average of the pure-state matrices. -/
lemma eamProbMatrix_ensembleDensity {ι : Type*} [Fintype ι] (ψ φ : Fin n → Fin d → ℂ)
    (p : ι → ℝ) (Ψ : ι → Fin d × Fin d → ℂ) (a b : Fin n) :
    eamProbMatrix ψ φ (ensembleDensity p Ψ) a b = ∑ t, p t * eamPureProbMatrix ψ φ (Ψ t) a b := by
  simp only [eamProbMatrix, eamPureProbMatrix, Matrix.of_apply, ensembleDensity_mulVec,
    ip_sum_right, ip_smul_right]
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc, mul_comm (ip (Ψ t) _), ip_mul_ip_swap, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  ring

/-- For a pure state `ρ = |Ψ⟩⟨Ψ|`, `eamProbMatrix` is `eamPureProbMatrix`. -/
lemma eamProbMatrix_pure (ψ φ : Fin n → Fin d → ℂ) (Ψ : Fin d × Fin d → ℂ) :
    eamProbMatrix ψ φ (Matrix.vecMulVec Ψ (star Ψ)) = eamPureProbMatrix ψ φ Ψ := by
  ext a b
  have h := eamProbMatrix_ensembleDensity ψ φ (fun _ : Unit => (1 : ℝ)) (fun _ => Ψ) a b
  simp only [ensembleDensity, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
    one_smul, one_mul] at h
  exact h

end ProbMatrix

/-- If `Q = ∑ₜ pₜ Mₜ` is a convex combination and `∑_{i,j} O_{ij} (Mₜ)_{ij} ≤ B` for every `t`,
then `∑_{i,j} O_{ij} Q_{ij} ≤ B`. -/
lemma sum_mul_le_of_convex {ι κ : Type*} [Fintype ι] [Fintype κ] (O Q : Matrix κ κ ℝ)
    (M : ι → Matrix κ κ ℝ) (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t) (hp1 : ∑ t, p t = 1)
    (hQ : ∀ i j, Q i j = ∑ t, p t * M t i j) (B : ℝ)
    (hB : ∀ t, ∑ i, ∑ j, O i j * M t i j ≤ B) :
    ∑ i, ∑ j, O i j * Q i j ≤ B := by
  simp only [hQ]
  calc ∑ i, ∑ j, O i j * ∑ t, p t * M t i j
      = ∑ i, ∑ t, ∑ j, p t * (O i j * M t i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => by ring
    _ = ∑ t, p t * ∑ i, ∑ j, O i j * M t i j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [Finset.mul_sum]
    _ ≤ ∑ t, p t * B := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hB t) (hp t)
    _ = B := by rw [← Finset.sum_mul, hp1, one_mul]

/-! ## Main theorems -/

section Main

variable {d n r : ℕ}

/-- The bound `[d (d - 1) + r (n - d)] / [n (n - 1)]` is monotone in `r` when `d ≤ n`. -/
lemma eamBound_mono (hdn : d ≤ n) (hn : 2 ≤ n) {k : ℝ} (hk : k ≤ r) :
    ((d : ℝ) * (d - 1) + k * (n - d)) / (n * (n - 1)) ≤
      ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by linarith) (by linarith))
  have := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hdn')
  linarith

/-- **Main theorem (pure states).** Let `ψ`, `φ` be EAMs with `n ≥ 2` elements in `ℂ^d` (Alice's
and Bob's) and let `Ψ` be a pure state in Schmidt form with `r` terms. Then for every real
orthogonal `n × n` matrix `O`,
`∑_{a,b} O_{ab} (d/n)² |⟨ψₐ ⊗ φ_b|Ψ⟩|² ≤ [d (d - 1) + r (n - d)] / [n (n - 1)]`. -/
theorem schmidt_eam_bound (hn : 2 ≤ n) {ψ φ : Fin n → Fin d → ℂ} (hψ : IsEAM d n ψ)
    (hφ : IsEAM d n φ) (Ψ : SchmidtState d r) (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    ∑ a, ∑ b, O a b * eamPureProbMatrix ψ φ Ψ.vec a b ≤
      ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) := by
  have hd : 0 < d := hψ.d_pos (by omega)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  -- Step 1: vectors `x a, y b ∈ ℂ^r` with `⟨ψₐ ⊗ φ_b|Ψ⟩ = ⟨xₐ|y_b⟩`
  set x : Fin n → Fin r → ℂ :=
    fun a s => (√(Ψ.σ s) : ℂ) * conj (ip (ψ a) (Ψ.u s)) with hx
  set y : Fin n → Fin r → ℂ :=
    fun b s => (√(Ψ.σ s) : ℂ) * ip (φ b) (Ψ.v s) with hy
  have hsq : ∀ s, ((√(Ψ.σ s) : ℝ) : ℂ) * ((√(Ψ.σ s) : ℝ) : ℂ) = (Ψ.σ s : ℂ) := by
    intro s
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Ψ.σ_nonneg s)]
  have hamp : ∀ a b, ip (tensor (ψ a) (φ b)) Ψ.vec = ip (x a) (y b) := by
    intro a b
    simp only [SchmidtState.vec, ip_sum_right, ip_smul_right, ip_tensor]
    simp only [ip, hx, hy, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← hsq s]
    ring
  -- `‖xₐ‖² = wₐ` and `‖y_b‖² = w'_b`
  have hxn : ∀ a, sqNorm (x a) = frameWeight ψ Ψ.σ Ψ.u a := by
    intro a
    simp only [sqNorm, hx, frameWeight, Complex.normSq_mul, Complex.normSq_conj,
      Complex.normSq_ofReal, Real.mul_self_sqrt (Ψ.σ_nonneg _)]
  have hyn : ∀ b, sqNorm (y b) = frameWeight φ Ψ.σ Ψ.v b := by
    intro b
    simp only [sqNorm, hy, frameWeight, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Ψ.σ_nonneg _)]
  -- Step 2: Lemma 1
  have hOt : O.transpose * O = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hO
  have h1 := orthogonal_weighted_sum_le O hOt x y
  -- Step 3: Lemma 2′ on both sides (same `τ`, and `∑ σ² = 1`)
  set τ : ℝ := ∑ s, Ψ.σ s with hτ
  set M : ℝ := n * τ ^ 2 / d ^ 2 + (1 - eamOverlap d n) * (1 - τ ^ 2 / d) with hM
  have hX : ∑ a, sqNorm (x a) ^ 2 ≤ M := by
    have h := eam_bessel hn hψ Ψ.σ Ψ.u_orthonormal
    rw [Ψ.σ_sq_sum, ← hτ] at h
    simp only [hxn]
    exact h
  have hY : ∑ b, sqNorm (y b) ^ 2 ≤ M := by
    have h := eam_bessel hn hφ Ψ.σ Ψ.v_orthonormal
    rw [Ψ.σ_sq_sum, ← hτ] at h
    simp only [hyn]
    exact h
  have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun a _ => sq_nonneg _) hX
  -- Step 4: the algebra, `τ² ≤ r` and `n ≥ d`
  have hτr : τ ^ 2 ≤ r := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := Ψ.σ)
    rw [Ψ.σ_sq_sum, Finset.card_univ, Fintype.card_fin, mul_one] at this
    exact this
  have halg : ((d : ℝ) / n) ^ 2 * M = ((d : ℝ) * (d - 1) + τ ^ 2 * (n - d)) / (n * (n - 1)) := by
    rw [hM, eamOverlap]
    field_simp
    ring
  calc ∑ a, ∑ b, O a b * eamPureProbMatrix ψ φ Ψ.vec a b
      = ((d : ℝ) / n) ^ 2 * ∑ a, ∑ b, O a b * Complex.normSq (ip (x a) (y b)) := by
        simp only [eamPureProbMatrix, Matrix.of_apply, hamp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ ≤ ((d : ℝ) / n) ^ 2 * (√(∑ a, sqNorm (x a) ^ 2) * √(∑ b, sqNorm (y b) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ ≤ ((d : ℝ) / n) ^ 2 * (√M * √M) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = ((d : ℝ) / n) ^ 2 * M := by rw [Real.mul_self_sqrt hM0]
    _ = ((d : ℝ) * (d - 1) + τ ^ 2 * (n - d)) / (n * (n - 1)) := halg
    _ ≤ ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) := eamBound_mono (hψ.le hn) hn hτr

/-- **Main theorem (mixed states).** For a finite ensemble `ρ = ∑ₜ pₜ |Ψₜ⟩⟨Ψₜ|` of pure states
in Schmidt form with `r` terms, EAMs `ψ`, `φ` with `n ≥ 2` elements and every real orthogonal
`O`, `∑_{a,b} O_{ab} P_{ab} ≤ [d (d - 1) + r (n - d)] / [n (n - 1)]`. -/
theorem schmidt_eam_bound_mixed {ι : Type*} [Fintype ι] (hn : 2 ≤ n)
    {ψ φ : Fin n → Fin d → ℂ} (hψ : IsEAM d n ψ) (hφ : IsEAM d n φ) (p : ι → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hp1 : ∑ t, p t = 1) (Ψ : ι → SchmidtState d r)
    (O : Matrix (Fin n) (Fin n) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    ∑ a, ∑ b, O a b * eamProbMatrix ψ φ (ensembleDensity p fun t => (Ψ t).vec) a b ≤
      ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) :=
  sum_mul_le_of_convex O _ (fun t => eamPureProbMatrix ψ φ (Ψ t).vec) p hp hp1
    (eamProbMatrix_ensembleDensity ψ φ p _) _ fun t => schmidt_eam_bound hn hψ hφ (Ψ t) O hO

/-- The pure-state bound for any unit vector of Schmidt rank at most `r`. -/
theorem schmidt_eam_bound_of_rankLE (hn : 2 ≤ n) {ψ φ : Fin n → Fin d → ℂ}
    (hψ : IsEAM d n ψ) (hφ : IsEAM d n φ) (Ψ : Fin d × Fin d → ℂ) (hΨ : HasSchmidtRankLE Ψ r)
    (O : Matrix (Fin n) (Fin n) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    ∑ a, ∑ b, O a b * eamPureProbMatrix ψ φ Ψ a b ≤
      ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) := by
  obtain ⟨k, hk, Ψ', rfl⟩ := hΨ
  exact (schmidt_eam_bound hn hψ hφ Ψ' O hO).trans
    (eamBound_mono (hψ.le hn) hn (by exact_mod_cast hk))

/-- **Tavakoli–Morelli, Conjecture 2, dual form.** Let `ψ` and `φ` be equiangular measurements
with `n ≥ 2` elements in `ℂ^d` (for Alice and for Bob), let `ρ` be a state of `ℂ^d ⊗ ℂ^d` with
Schmidt number at most `r`, and let `P = eamProbMatrix ψ φ ρ`,
`P_{ab} = (d/n)² ⟨ψₐ ⊗ φ_b|ρ|ψₐ ⊗ φ_b⟩`. Then
`Tr(Oᵀ P) ≤ [d (d - 1) + r (n - d)] / [n (n - 1)]` for every real orthogonal matrix `O`. -/
theorem tavakoli_morelli_conjecture_2_dual (hn : 2 ≤ n) {ψ φ : Fin n → Fin d → ℂ}
    (hψ : IsEAM d n ψ) (hφ : IsEAM d n φ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hρ : HasSchmidtNumberLE ρ r) (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    (O.transpose * eamProbMatrix ψ φ ρ).trace ≤
      ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) := by
  obtain ⟨T, p, Ψ, hp, hp1, hΨ, rfl⟩ := hρ
  rw [trace_transpose_mul]
  exact sum_mul_le_of_convex O _ (fun t => eamPureProbMatrix ψ φ (Ψ t)) p hp hp1
    (eamProbMatrix_ensembleDensity ψ φ p Ψ) _ fun t =>
      schmidt_eam_bound_of_rankLE hn hψ hφ (Ψ t) (hΨ t) O hO

/-- The trace-norm bound of Conjecture 2 for EAMs with `n ≥ 2` elements. -/
theorem traceNorm_eamProbMatrix_le (hn : 2 ≤ n) {ψ φ : Fin n → Fin d → ℂ}
    (hψ : IsEAM d n ψ) (hφ : IsEAM d n φ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hρ : HasSchmidtNumberLE ρ r) :
    traceNorm (eamProbMatrix ψ φ ρ) ≤ ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) := by
  refine traceNorm_le_of_forall_orthogonal _ _ fun O hO => ?_
  rw [← trace_transpose_mul]
  exact tavakoli_morelli_conjecture_2_dual hn hψ hφ ρ hρ O hO

/-- **Tavakoli–Morelli, Conjecture 2** (arXiv:2402.09972). Let `ψ` and `φ` be equiangular
measurements with `n > d` elements in `ℂ^d` (for Alice and for Bob), with POVM elements
`Eₐ = (d/n) |ψₐ⟩⟨ψₐ|` and `F_b = (d/n) |φ_b⟩⟨φ_b|`, and let `ρ` be a state of `ℂ^d ⊗ ℂ^d` with
Schmidt number at most `r`. Then the `n × n` matrix of joint outcome probabilities
`P_{ab} = Tr[ρ (Eₐ ⊗ F_b)] = (d/n)² ⟨ψₐ ⊗ φ_b|ρ|ψₐ ⊗ φ_b⟩` satisfies
`‖P‖_tr ≤ [d (d - 1) + r (n - d)] / [n (n - 1)]`. -/
theorem tavakoli_morelli_conjecture_2 (hdn : d < n) {ψ φ : Fin n → Fin d → ℂ}
    (hψ : IsEAM d n ψ) (hφ : IsEAM d n φ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hρ : HasSchmidtNumberLE ρ r) :
    traceNorm (eamProbMatrix ψ φ ρ) ≤ ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) :=
  traceNorm_eamProbMatrix_le (hψ.two_le_of_lt hdn) hψ hφ ρ hρ

/-- The trace-norm bound for a pure state in Schmidt form with `r` terms. -/
theorem schmidt_eam_traceNorm_bound (hn : 2 ≤ n) {ψ φ : Fin n → Fin d → ℂ}
    (hψ : IsEAM d n ψ) (hφ : IsEAM d n φ) (Ψ : SchmidtState d r) :
    traceNorm (eamPureProbMatrix ψ φ Ψ.vec) ≤
      ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) :=
  traceNorm_le_of_forall_orthogonal _ _ fun O hO => schmidt_eam_bound hn hψ hφ Ψ O hO

/-- The trace-norm bound for a finite ensemble of pure states in Schmidt form with `r` terms. -/
theorem schmidt_eam_traceNorm_bound_mixed {ι : Type*} [Fintype ι] (hn : 2 ≤ n)
    {ψ φ : Fin n → Fin d → ℂ} (hψ : IsEAM d n ψ) (hφ : IsEAM d n φ) (p : ι → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hp1 : ∑ t, p t = 1) (Ψ : ι → SchmidtState d r) :
    traceNorm (eamProbMatrix ψ φ (ensembleDensity p fun t => (Ψ t).vec)) ≤
      ((d : ℝ) * (d - 1) + r * (n - d)) / (n * (n - 1)) :=
  traceNorm_le_of_forall_orthogonal _ _ fun O hO =>
    schmidt_eam_bound_mixed hn hψ hφ p hp hp1 Ψ O hO

end Main

/-! ## Sanity checks: the qubit trine -/

section Examples

/-- `√3 / 2` as a complex number. -/
def sqrt3Half : ℂ := ((Real.sqrt 3 / 2 : ℝ) : ℂ)

lemma sqrt3Half_mul_self : sqrt3Half * sqrt3Half = 3 / 4 := by
  rw [sqrt3Half, ← Complex.ofReal_mul, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]
  push_cast
  norm_num

lemma conj_sqrt3Half : conj sqrt3Half = sqrt3Half := Complex.conj_ofReal _

lemma normSq_sqrt3Half : Complex.normSq sqrt3Half = 3 / 4 := by
  rw [sqrt3Half, Complex.normSq_ofReal, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The trine: the unit vectors `(1, 0)`, `(-1/2, √3/2)` and `(-1/2, -√3/2)` of `ℂ²`, at angles
of 120°. -/
def trine : Fin 3 → Fin 2 → ℂ := ![![1, 0], ![-1 / 2, sqrt3Half], ![-1 / 2, -sqrt3Half]]

/-- The trine is an EAM with `n = 3` elements in `ℂ²` (with `c = 1/4`). -/
lemma trine_isEAM : IsEAM 2 3 trine := by
  have hc : eamOverlap 2 3 = 1 / 4 := by norm_num [eamOverlap]
  have hq : ∀ z : ℂ, z = -1 / 2 → Complex.normSq z = 1 / 4 := by
    rintro z rfl
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]
    norm_num
  refine ⟨fun a => ?_, fun x y => ?_, fun a b hab => ?_⟩
  · fin_cases a <;> simp [sqNorm, trine, Fin.sum_univ_two, normSq_sqrt3Half, hq] <;> norm_num
  · fin_cases x <;> fin_cases y <;>
      simp [trine, Fin.sum_univ_three, conj_sqrt3Half, sqrt3Half_mul_self, map_ofNat] <;> ring_nf
  · rw [hc]
    apply hq
    fin_cases a <;> fin_cases b <;> simp at hab <;>
      simp [ip, trine, Fin.sum_univ_two, conj_sqrt3Half, sqrt3Half_mul_self, map_ofNat] <;> ring_nf

/-- The main theorem instantiated: the trine for Alice and Bob and the two-qubit maximally
entangled state `bellState`; the bound is `[2 · 1 + 2 · 1] / [3 · 2] = 2/3`. -/
example (O : Matrix (Fin 3) (Fin 3) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    ∑ a, ∑ b, O a b * eamPureProbMatrix trine trine bellState.vec a b ≤ 2 / 3 := by
  have := schmidt_eam_bound (by norm_num) trine_isEAM trine_isEAM bellState O hO
  norm_num at this
  exact this

/-- The bound is attained: for the trine and `bellState`, `‖P‖_tr = 2/3` exactly (the lower
bound is `Tr P = ∑ₐ P_{aa} = 3 · (2/9)`, i.e. `O = 1`). -/
lemma traceNorm_trine_bellState :
    traceNorm (eamPureProbMatrix trine trine bellState.vec) = 2 / 3 := by
  apply le_antisymm
  · have := schmidt_eam_traceNorm_bound (by norm_num) trine_isEAM trine_isEAM bellState
    norm_num at this
    exact this
  · have hip : ∀ a, ip (tensor (trine a) (trine a)) bellState.vec =
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
      intro a
      simp only [SchmidtState.vec, bellState, ip_sum_right, ip_smul_right, ip_tensor]
      fin_cases a <;>
        simp [ip, stdBasis, trine, Fin.sum_univ_two, conj_sqrt3Half, sqrt3Half_mul_self,
          map_ofNat] <;>
        ring_nf
    have hdiag : ∀ a, eamPureProbMatrix trine trine bellState.vec a a = 2 / 9 := by
      intro a
      rw [eamPureProbMatrix, Matrix.of_apply, hip, Complex.normSq_ofReal, ← mul_inv,
        Real.mul_self_sqrt (by norm_num)]
      norm_num
    have h := (isGreatest_traceNorm (eamPureProbMatrix trine trine bellState.vec)).2
      ⟨1, one_mem _, rfl⟩
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    norm_num at h
    linarith

end Examples

end TMProof

#print axioms TMProof.eam_bessel
#print axioms TMProof.schmidt_eam_bound
#print axioms TMProof.schmidt_eam_bound_mixed
#print axioms TMProof.tavakoli_morelli_conjecture_2_dual
#print axioms TMProof.traceNorm_eamProbMatrix_le
#print axioms TMProof.tavakoli_morelli_conjecture_2
#print axioms TMProof.schmidt_eam_traceNorm_bound
#print axioms TMProof.schmidt_eam_traceNorm_bound_mixed
#print axioms TMProof.eamProbMatrix_eq_trace
#print axioms TMProof.traceNorm_trine_bellState
