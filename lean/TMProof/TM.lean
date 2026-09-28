import Mathlib

/-!
# Schmidt-number bound for incomplete sets of MUBs (Tavakoli–Morelli, Conjecture 3)

This file gives a machine-checked proof of Conjecture 3 of

* A. Tavakoli and S. Morelli, *Enhanced Schmidt number criteria based on correlation trace
  norms*, arXiv:2402.09972, Phys. Rev. A **110**, 062417 (2024).

## The conjecture

Let Alice and Bob each hold a set of `m` mutually unbiased bases (MUBs) of `ℂ^d`,
`{e_{k,a}}` and `{f_{l,b}}` (`k, l < m`, `a, b < d`). For a bipartite state `ρ` on
`ℂ^d ⊗ ℂ^d` let `Q` be the real `md × md` matrix of joint outcome probabilities
`Q_{(k,a),(l,b)} = ⟨e_{k,a} ⊗ f_{l,b}| ρ |e_{k,a} ⊗ f_{l,b}⟩`.
Conjecture 3 states: if `ρ` has Schmidt number at most `r`, then
`‖Q‖_tr ≤ 1 + (m - 1) r / d`.

Here `‖Q‖_tr = Tr √(QᵀQ)` is the trace norm: the sum of the singular values of `Q`
(`traceNorm`). For a real square matrix, `‖Q‖_tr = max_{O orthogonal} Tr(Oᵀ Q)`; this is proved
here as `isGreatest_traceNorm`, via a singular value decomposition built from Mathlib's spectral
theorem. The core result is the dual statement: `Tr(Oᵀ Q) = ∑_{i,j} O_{ij} Q_{ij} ≤
1 + (m - 1) r / d` for every real orthogonal `O` (`Matrix.orthogonalGroup`). The trace-norm form
then follows.

## Conventions

* Vectors of `ℂ^n` are functions `ι → ℂ`. `ip x y = ∑ᵢ conj (x i) * y i` is the standard
  inner product `⟨x|y⟩` (antilinear in the first slot). `ip_eq_inner` identifies it with
  Mathlib's inner product on `EuclideanSpace ℂ ι`.
* `ℂ^d ⊗ ℂ^d` is `Fin d × Fin d → ℂ`, with `tensor x y (p, q) = x p * y q`.
* A basis is a family of `d` orthonormal vectors of `ℂ^d` (`IsOrthonormal`); completeness is
  proved (`IsOrthonormal.complete`). `IsMUB d m e` says that `e : Fin m → Fin d → Fin d → ℂ`
  is a family of `m` pairwise mutually unbiased bases.
* A pure state of Schmidt rank at most `r` is given in Schmidt form (`SchmidtState d r`):
  `ψ = ∑_{s<r} σ_s u_s ⊗ v_s` with orthonormal `u, v`, `σ_s ≥ 0` and `∑ σ_s² = 1`.
* A state of Schmidt number at most `r` is a finite convex combination of projectors onto pure
  states of Schmidt rank at most `r` (`HasSchmidtNumberLE`).
* The measured amplitudes are `⟨e_{k,a} ⊗ f_{l,b}|ψ⟩` with no complex conjugation of Bob's
  basis, exactly as in the paper.

## Main results

* `TMProof.orthogonal_weighted_sum_le` (Lemma 1): for families `x i, y j ∈ ℂ^r` and a real
  orthogonal `O`, `∑_{i,j} O_{ij} |⟨x_i|y_j⟩|² ≤ √(∑ᵢ ‖x_i‖⁴) √(∑ⱼ ‖y_j‖⁴)`.
* `TMProof.mub_bessel` (Lemma 2): with `c_{k,a} = ∑_s σ_s |⟨e_{k,a}|u_s⟩|²`,
  `∑_{k,a} c_{k,a}² ≤ ∑_s σ_s² + (m - 1) (∑_s σ_s)² / d`.
* `TMProof.isGreatest_traceNorm`: `‖Q‖_tr` is the maximum of `Tr(Oᵀ Q)` over real
  orthogonal `O`.
* `TMProof.schmidt_mub_bound`: the dual bound for pure states in Schmidt form.
* `TMProof.schmidt_mub_bound_mixed`: the dual bound for finite ensembles of such states.
* `TMProof.tavakoli_morelli_conjecture_3_dual`: for every state of Schmidt number at most `r`,
  `Tr(Oᵀ Q) ≤ 1 + (m - 1) r / d` for all real orthogonal `O`.
* `TMProof.tavakoli_morelli_conjecture_3`: Conjecture 3 as stated in the paper,
  `‖Q‖_tr ≤ 1 + (m - 1) r / d` for every state of Schmidt number at most `r`.

## Proof outline

1. Write `⟨e_i ⊗ f_j|ψ⟩ = ⟨x_i|y_j⟩` with `x_i, y_j ∈ ℂ^r`,
   `(x_i)_s = √σ_s · conj ⟨e_i|u_s⟩` and `(y_j)_s = √σ_s · ⟨f_j|v_s⟩`.
2. Lemma 1: `|⟨x|y⟩|² = ∑_{s,t} P(s,t) R(s,t)` with `P = conj(x_s) x_t`,
   `R = y_s conj(y_t)`; then Cauchy–Schwarz over `(i,s,t)`, and `O` preserves Euclidean norms.
3. Lemma 2 in the Hilbert–Schmidt space of `d × d` matrices: with `A = ∑ σ_s |u_s⟩⟨u_s|`,
   `τ = ∑ σ_s`, `α_{k,a} = c_{k,a} - τ/d`, `Y = A - (τ/d) I` and
   `B = ∑_{k,a} α_{k,a} |e_{k,a}⟩⟨e_{k,a}|`, the MUB conditions give
   `⟨P_{k,a}, Y⟩ = ⟨P_{k,a}, B⟩ = α_{k,a}`. Hence `B ⟂ Y - B` and
   `∑ α² = ‖B‖² ≤ ‖Y‖² = ∑ σ² - τ²/d`.
4. Since `‖x_i‖² = c_i`, combine with `τ² ≤ r ∑ σ² = r`.
5. Mixed states follow by linearity; the trace-norm form follows from
   `‖Q‖_tr = max_O Tr(Oᵀ Q)`.
-/

open scoped BigOperators ComplexConjugate
open Finset

noncomputable section

namespace TMProof

/-! ## The standard inner product on `ι → ℂ` -/

section InnerProduct

variable {ι : Type*} [Fintype ι]

/-- The standard inner product `⟨x|y⟩ = ∑ᵢ conj (x i) * y i` on `ι → ℂ` (physics convention:
antilinear in the first argument). -/
def ip (x y : ι → ℂ) : ℂ := ∑ i, conj (x i) * y i

/-- The squared Euclidean norm `‖x‖² = ∑ᵢ |x i|²`. -/
def sqNorm (x : ι → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

/-- `ip` is Mathlib's inner product on `EuclideanSpace ℂ ι`. -/
lemma ip_eq_inner (x y : ι → ℂ) :
    ip x y = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y) := by
  simp [ip, PiLp.inner_apply, mul_comm]

lemma ip_add_left (x y z : ι → ℂ) : ip (x + y) z = ip x z + ip y z := by
  simp [ip, add_mul, Finset.sum_add_distrib]

lemma ip_add_right (x y z : ι → ℂ) : ip x (y + z) = ip x y + ip x z := by
  simp [ip, mul_add, Finset.sum_add_distrib]

lemma ip_sub_left (x y z : ι → ℂ) : ip (x - y) z = ip x z - ip y z := by
  simp [ip, sub_mul, Finset.sum_sub_distrib]

lemma ip_sub_right (x y z : ι → ℂ) : ip x (y - z) = ip x y - ip x z := by
  simp [ip, mul_sub, Finset.sum_sub_distrib]

lemma ip_smul_left (c : ℂ) (x y : ι → ℂ) : ip (c • x) y = conj c * ip x y := by
  simp [ip, Finset.mul_sum, mul_assoc]

lemma ip_smul_right (c : ℂ) (x y : ι → ℂ) : ip x (c • y) = c * ip x y := by
  simp [ip, Finset.mul_sum, mul_left_comm]

lemma ip_sum_left {κ : Type*} (s : Finset κ) (x : κ → ι → ℂ) (y : ι → ℂ) :
    ip (∑ t ∈ s, x t) y = ∑ t ∈ s, ip (x t) y := by
  simp only [ip, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ip_sum_right {κ : Type*} (s : Finset κ) (x : ι → ℂ) (y : κ → ι → ℂ) :
    ip x (∑ t ∈ s, y t) = ∑ t ∈ s, ip x (y t) := by
  simp only [ip, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma conj_ip (x y : ι → ℂ) : conj (ip x y) = ip y x := by
  simp [ip, map_sum, mul_comm]

lemma ip_self (x : ι → ℂ) : ip x x = (sqNorm x : ℂ) := by
  simp [ip, sqNorm, Complex.normSq_eq_conj_mul_self]

lemma sqNorm_nonneg (x : ι → ℂ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma ip_mul_ip_swap (x y : ι → ℂ) : ip x y * ip y x = (Complex.normSq (ip x y) : ℂ) := by
  rw [← conj_ip x y, Complex.mul_conj]

end InnerProduct

/-! ## Orthonormal families and mutually unbiased bases -/

/-- A family `u : κ → (ι → ℂ)` is orthonormal: `⟨u s|u t⟩ = δ_{st}`. -/
def IsOrthonormal {κ ι : Type*} [Fintype ι] [DecidableEq κ] (u : κ → ι → ℂ) : Prop :=
  ∀ s t, ip (u s) (u t) = if s = t then 1 else 0

/-- `IsOrthonormal` is Mathlib's `Orthonormal` in `EuclideanSpace ℂ ι`. -/
lemma isOrthonormal_iff_orthonormal {κ ι : Type*} [Fintype ι] [DecidableEq κ]
    (u : κ → ι → ℂ) :
    IsOrthonormal u ↔ Orthonormal ℂ (fun s => (WithLp.toLp 2 (u s) : EuclideanSpace ℂ ι)) := by
  rw [orthonormal_iff_ite]
  simp only [IsOrthonormal, ip_eq_inner]

lemma IsOrthonormal.sqNorm_eq_one {κ ι : Type*} [Fintype ι] [DecidableEq κ]
    {u : κ → ι → ℂ} (hu : IsOrthonormal u) (s : κ) : sqNorm (u s) = 1 := by
  have h := hu s s
  rw [if_pos rfl, ip_self] at h
  exact_mod_cast h

/-- `IsMUB d m e`: `e k` (for `k : Fin m`) is an orthonormal basis of `ℂ^d` (given by its `d`
vectors `e k a`, `a : Fin d`), and bases with `k ≠ l` are mutually unbiased:
`|⟨e k a|e l b⟩|² = 1/d` for all `a, b`. -/
structure IsMUB (d m : ℕ) (e : Fin m → Fin d → Fin d → ℂ) : Prop where
  orthonormal : ∀ k, IsOrthonormal (e k)
  unbiased : ∀ k l, k ≠ l → ∀ a b, Complex.normSq (ip (e k a) (e l b)) = 1 / d

/-- A family of Mathlib `OrthonormalBasis`es of `EuclideanSpace ℂ (Fin d)` that is pairwise
unbiased (`‖⟪b k a, b l a'⟫‖² = 1/d` for `k ≠ l`) is an `IsMUB` family. -/
lemma isMUB_of_orthonormalBasis {d m : ℕ}
    (b : Fin m → OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (hb : ∀ k l, k ≠ l → ∀ a a', ‖inner ℂ (b k a) (b l a')‖ ^ 2 = 1 / d) :
    IsMUB d m (fun k a => (b k a).ofLp) := by
  refine ⟨fun k => ?_, fun k l hkl a a' => ?_⟩
  · -- `simp` reduces `toLp ∘ ofLp` and closes the goal with `OrthonormalBasis.orthonormal`
    rw [isOrthonormal_iff_orthonormal]
    simp
  · rw [ip_eq_inner, Complex.normSq_eq_norm_sq]
    simpa using hb k l hkl a a'

section Completeness

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Completeness of an orthonormal basis: `n` orthonormal vectors `e a` of `n → ℂ` satisfy
`∑ₐ e a x * conj (e a y) = δ_{xy}` (i.e. `∑ₐ |e a⟩⟨e a| = I`). -/
lemma IsOrthonormal.complete {e : n → n → ℂ} (he : IsOrthonormal e) (x y : n) :
    ∑ a, e a x * conj (e a y) = if x = y then 1 else 0 := by
  set E : Matrix n n ℂ := Matrix.of fun x a => e a x with hE
  have h1 : E.conjTranspose * E = 1 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hE, Matrix.of_apply,
      Matrix.one_apply]
    have := he a b
    simpa [ip] using this
  have h2 : E * E.conjTranspose = 1 := mul_eq_one_comm.mp h1
  have := congrFun (congrFun h2 x) y
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hE, Matrix.one_apply] using this

/-- Parseval's identity for an orthonormal basis `e` of `n → ℂ`. -/
lemma IsOrthonormal.parseval {e : n → n → ℂ} (he : IsOrthonormal e) (u : n → ℂ) :
    ∑ a, Complex.normSq (ip (e a) u) = sqNorm u := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← ip_mul_ip_swap]
  rw [← ip_self]
  calc ∑ a, ip (e a) u * ip u (e a)
      = ∑ a, ∑ x, ∑ y, conj (u y) * u x * (e a y * conj (e a x)) := by
        simp only [ip, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ x, ∑ y, conj (u y) * u x * ∑ a, e a y * conj (e a x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = ip u u := by
        simp only [he.complete, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, ip]

end Completeness

/-! ## Operators as vectors of the Hilbert–Schmidt space `n × n → ℂ` -/

section HilbertSchmidt

variable {n : Type*} [Fintype n]

/-- The rank-one operator `|x⟩⟨x|`, as a vector of the Hilbert–Schmidt space `n × n → ℂ`. -/
def outer (x : n → ℂ) : n × n → ℂ := fun p => x p.1 * conj (x p.2)

/-- `Tr(|x⟩⟨x| |y⟩⟨y|) = |⟨x|y⟩|²`. -/
lemma ip_outer_outer (x y : n → ℂ) :
    ip (outer x) (outer y) = (Complex.normSq (ip x y) : ℂ) := by
  rw [← ip_mul_ip_swap]
  simp only [ip, outer, Fintype.sum_prod_type, Finset.sum_mul_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

variable [DecidableEq n]

/-- The identity operator, as a vector of the Hilbert–Schmidt space. -/
def idVec : n × n → ℂ := fun p => if p.1 = p.2 then 1 else 0

lemma ip_outer_idVec (x : n → ℂ) : ip (outer x) idVec = (sqNorm x : ℂ) := by
  rw [← ip_self]
  simp only [ip, outer, idVec, Fintype.sum_prod_type, map_mul, Complex.conj_conj, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ip_idVec_outer (x : n → ℂ) : ip idVec (outer x) = (sqNorm x : ℂ) := by
  rw [← conj_ip, ip_outer_idVec, Complex.conj_ofReal]

lemma ip_idVec_idVec : ip (idVec : n × n → ℂ) idVec = Fintype.card n := by
  simp [ip, idVec, Fintype.sum_prod_type, apply_ite]

end HilbertSchmidt

/-! ## Lemma 2: a Bessel inequality for MUBs -/

section Bessel

variable {d m r : ℕ}

/-- The operator `A = ∑ₛ σₛ |uₛ⟩⟨uₛ|` as a Hilbert–Schmidt vector. -/
def schmidtOp (σ : Fin r → ℝ) (u : Fin r → Fin d → ℂ) : Fin d × Fin d → ℂ :=
  ∑ s, (σ s : ℂ) • outer (u s)

lemma ip_outer_schmidtOp (σ : Fin r → ℝ) (u : Fin r → Fin d → ℂ) (x : Fin d → ℂ) :
    ip (outer x) (schmidtOp σ u) = ((∑ s, σ s * Complex.normSq (ip x (u s)) : ℝ) : ℂ) := by
  simp only [schmidtOp, ip_sum_right, ip_smul_right, ip_outer_outer]
  push_cast
  rfl

lemma ip_idVec_schmidtOp (σ : Fin r → ℝ) {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) :
    ip idVec (schmidtOp σ u) = ((∑ s, σ s : ℝ) : ℂ) := by
  simp only [schmidtOp, ip_sum_right, ip_smul_right, ip_idVec_outer, hu.sqNorm_eq_one]
  push_cast
  simp

lemma ip_schmidtOp_idVec (σ : Fin r → ℝ) {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) :
    ip (schmidtOp σ u) idVec = ((∑ s, σ s : ℝ) : ℂ) := by
  rw [← conj_ip, ip_idVec_schmidtOp σ hu, Complex.conj_ofReal]

lemma ip_schmidtOp_schmidtOp (σ : Fin r → ℝ) {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) :
    ip (schmidtOp σ u) (schmidtOp σ u) = ((∑ s, σ s ^ 2 : ℝ) : ℂ) := by
  conv_lhs => arg 1; rw [schmidtOp]
  rw [ip_sum_left]
  simp only [ip_smul_left, ip_outer_schmidtOp, Complex.conj_ofReal, hu _ _,
    apply_ite Complex.normSq, Complex.normSq_one, Complex.normSq_zero, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  push_cast
  refine Finset.sum_congr rfl fun s _ => by ring

/-- `‖A - (τ/d) I‖²_HS = ∑ σ² - τ²/d` for `A = ∑ σₛ |uₛ⟩⟨uₛ|`, `τ = ∑ σₛ`. -/
lemma ip_centered_schmidtOp (σ : Fin r → ℝ) {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u)
    (hd : d ≠ 0) :
    ip (schmidtOp σ u - (((∑ s, σ s) / d : ℝ) : ℂ) • idVec)
        (schmidtOp σ u - (((∑ s, σ s) / d : ℝ) : ℂ) • idVec) =
      ((∑ s, σ s ^ 2 - (∑ s, σ s) ^ 2 / d : ℝ) : ℂ) := by
  rw [ip_sub_left, ip_sub_right, ip_sub_right, ip_smul_left, ip_smul_left, ip_smul_right,
    ip_smul_right, ip_schmidtOp_schmidtOp σ hu, ip_schmidtOp_idVec σ hu,
    ip_idVec_schmidtOp σ hu, ip_idVec_idVec, Complex.conj_ofReal, Fintype.card_fin]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring

/-- `(∑ σ)² / d ≤ ∑ σ²` for any orthonormal family `u` of `ℂ^d` and any real weights. -/
lemma sq_sum_div_le (σ : Fin r → ℝ) {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) :
    (∑ s, σ s) ^ 2 / d ≤ ∑ s, σ s ^ 2 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [CharP.cast_eq_zero, div_zero]
    exact Finset.sum_nonneg fun s _ => sq_nonneg _
  · have h := ip_centered_schmidtOp σ hu hd.ne'
    rw [ip_self] at h
    have h2 : sqNorm (schmidtOp σ u - (((∑ s, σ s) / d : ℝ) : ℂ) • idVec) =
        ∑ s, σ s ^ 2 - (∑ s, σ s) ^ 2 / d := by exact_mod_cast h
    have := sqNorm_nonneg (schmidtOp σ u - (((∑ s, σ s) / d : ℝ) : ℂ) • idVec)
    linarith

/-- An orthonormal family of `ℂ^d` has at most `d` elements. -/
lemma card_le_of_isOrthonormal {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) : r ≤ d := by
  have h := sq_sum_div_le (fun _ => (1 : ℝ)) hu
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    one_pow] at h
  rcases Nat.eq_zero_or_pos r with hr | hr
  · omega
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have h1 := hu.sqNorm_eq_one ⟨0, hr⟩
    simp [sqNorm] at h1
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : (r : ℝ) ≤ d := by
    rw [div_le_iff₀ hd'] at h
    nlinarith
  exact_mod_cast this

/-- The diagonal weights `c k a = ∑ₛ σₛ |⟨e k a|u s⟩|² = ⟨e k a| A |e k a⟩`. -/
def diagWeight (e : Fin m → Fin d → Fin d → ℂ) (σ : Fin r → ℝ) (u : Fin r → Fin d → ℂ)
    (k : Fin m) (a : Fin d) : ℝ :=
  ∑ s, σ s * Complex.normSq (ip (e k a) (u s))

lemma sum_diagWeight (e : Fin m → Fin d → Fin d → ℂ) (he : ∀ k, IsOrthonormal (e k))
    (σ : Fin r → ℝ) {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) (k : Fin m) :
    ∑ a, diagWeight e σ u k a = ∑ s, σ s := by
  simp only [diagWeight]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, (he k).parseval, hu.sqNorm_eq_one, mul_one]

/-- **Lemma 2 (Bessel inequality for MUBs).** Let `e` be `m` MUBs of `ℂ^d`, `u` an
orthonormal family and `σ` real weights, `τ = ∑ σₛ`, `c_{k,a} = ∑ₛ σₛ |⟨e_{k,a}|uₛ⟩|²`. Then
`∑_{k,a} c_{k,a}² ≤ ∑ σₛ² + (m - 1) τ² / d`. -/
theorem mub_bessel (e : Fin m → Fin d → Fin d → ℂ) (he : IsMUB d m e) (σ : Fin r → ℝ)
    {u : Fin r → Fin d → ℂ} (hu : IsOrthonormal u) :
    ∑ k, ∑ a, diagWeight e σ u k a ^ 2 ≤
      ∑ s, σ s ^ 2 + ((m : ℝ) - 1) * (∑ s, σ s) ^ 2 / d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, Nat.cast_zero,
      div_zero, add_zero]
    positivity
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set τ : ℝ := ∑ s, σ s with hτ
  set α : Fin m → Fin d → ℝ := fun k a => diagWeight e σ u k a - τ / d with hα
  set Y : Fin d × Fin d → ℂ := schmidtOp σ u - ((τ / d : ℝ) : ℂ) • idVec with hY
  set B : Fin d × Fin d → ℂ := ∑ k, ∑ a, (α k a : ℂ) • outer (e k a) with hB
  -- the coefficients `α k ·` of each basis sum to zero
  have hα0 : ∀ k, ∑ a, α k a = 0 := by
    intro k
    simp only [hα, Finset.sum_sub_distrib, sum_diagWeight e he.orthonormal σ hu k,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  -- `⟨P_{ka}, Y⟩ = α k a`
  have hPY : ∀ k a, ip (outer (e k a)) Y = (α k a : ℂ) := by
    intro k a
    rw [hY, ip_sub_right, ip_smul_right, ip_outer_schmidtOp, ip_outer_idVec,
      (he.orthonormal k).sqNorm_eq_one a]
    simp [hα, diagWeight]
  -- `⟨P_{ka}, B⟩ = α k a` (uses orthonormality and unbiasedness)
  have hPB : ∀ k a, ip (outer (e k a)) B = (α k a : ℂ) := by
    intro k a
    have hreal : ∑ l, ∑ b, α l b * Complex.normSq (ip (e k a) (e l b)) = α k a := by
      rw [Finset.sum_eq_single k]
      · simp only [(he.orthonormal k) a, apply_ite Complex.normSq, Complex.normSq_one,
          Complex.normSq_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          if_true]
      · intro l _ hlk
        simp only [he.unbiased k l (Ne.symm hlk), ← Finset.sum_mul, hα0 l, zero_mul]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hB, ip_sum_right]
    simp only [ip_sum_right, ip_smul_right, ip_outer_outer]
    rw [← hreal]
    push_cast
    rfl
  -- `B ⟂ Y - B`
  have hBYB : ip B (Y - B) = 0 := by
    conv_lhs => arg 1; rw [hB]
    simp only [ip_sum_left, ip_smul_left, ip_sub_right, hPY, hPB, sub_self]
  have hYBB : ip (Y - B) B = 0 := by rw [← conj_ip, hBYB, map_zero]
  -- `‖B‖² = ∑ α²`
  have hBB : ip B B = ((∑ k, ∑ a, α k a ^ 2 : ℝ) : ℂ) := by
    conv_lhs => arg 1; rw [hB]
    simp only [ip_sum_left, ip_smul_left, hPB, Complex.conj_ofReal]
    push_cast
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
  -- Pythagoras: `‖Y‖² = ‖Y - B‖² + ‖B‖²`
  have hpyth : ip Y Y = ip (Y - B) (Y - B) + ip B B := by
    have hsplit : Y = (Y - B) + B := by abel
    conv_lhs => rw [hsplit]
    rw [ip_add_left, ip_add_right, ip_add_right, hYBB, hBYB]
    ring
  have hYY := ip_centered_schmidtOp σ hu hd.ne'
  rw [← hτ, ← hY] at hYY
  rw [hYY, hBB, ip_self] at hpyth
  have hreal : ∑ s, σ s ^ 2 - τ ^ 2 / d = sqNorm (Y - B) + ∑ k, ∑ a, α k a ^ 2 := by
    exact_mod_cast hpyth
  have hnn := sqNorm_nonneg (Y - B)
  -- `∑ c² = ∑ α² + m τ² / d`
  have hc : ∀ k a, diagWeight e σ u k a = α k a + τ / d := fun k a => by simp [hα]
  have hsum : ∑ k, ∑ a, diagWeight e σ u k a ^ 2 = ∑ k, ∑ a, α k a ^ 2 + m * τ ^ 2 / d := by
    have hk : ∀ k, ∑ a, diagWeight e σ u k a ^ 2 = ∑ a, α k a ^ 2 + τ ^ 2 / d := by
      intro k
      simp only [hc, add_sq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hα0 k]
      field_simp
      ring
    simp only [hk, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hsum]
  have : ((m : ℝ) - 1) * τ ^ 2 / d = m * τ ^ 2 / d - τ ^ 2 / d := by ring
  rw [this]
  linarith

end Bessel

/-! ## Lemma 1: an orthogonal-matrix Cauchy–Schwarz bound -/

section Lemma1

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- A real orthogonal matrix preserves the Euclidean norm of complex vectors. -/
lemma orthogonal_normSq_sum (O : Matrix n n ℝ) (hO : O.transpose * O = 1) (z : n → ℂ) :
    ∑ i, Complex.normSq (∑ j, (O i j : ℂ) * z j) = ∑ j, Complex.normSq (z j) := by
  have hO' : ∀ j k, ((∑ i, O i j * O i k : ℝ) : ℂ) = if j = k then 1 else 0 := by
    intro j k
    have := congrFun (congrFun hO j) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    rw [this]
    split_ifs <;> simp
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj]
  calc ∑ i, (∑ j, (O i j : ℂ) * z j) * conj (∑ k, (O i k : ℂ) * z k)
      = ∑ i, ∑ j, ∑ k, ((O i j * O i k : ℝ) : ℂ) * (z j * conj (z k)) := by
        simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by push_cast; ring
    _ = ∑ j, ∑ k, ((∑ i, O i j * O i k : ℝ) : ℂ) * (z j * conj (z k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Complex.ofReal_sum, Finset.sum_mul]
    _ = ∑ j, z j * conj (z j) := by
        simp only [hO', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ip_mul_ip_swap_eq (a b : κ → ℂ) :
    ip a b * ip b a = ∑ s, ∑ t, conj (a s) * a t * (b s * conj (b t)) := by
  simp only [ip, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

/-- **Lemma 1.** For families `x i, y j` of vectors of `κ → ℂ` and a real orthogonal matrix
`O`: `∑_{i,j} O_{ij} |⟨x_i|y_j⟩|² ≤ √(∑ᵢ ‖x_i‖⁴) · √(∑ⱼ ‖y_j‖⁴)`. -/
theorem orthogonal_weighted_sum_le (O : Matrix n n ℝ) (hO : O.transpose * O = 1)
    (x y : n → κ → ℂ) :
    ∑ i, ∑ j, O i j * Complex.normSq (ip (x i) (y j)) ≤
      √(∑ i, sqNorm (x i) ^ 2) * √(∑ j, sqNorm (y j) ^ 2) := by
  set P : n × (κ × κ) → ℂ := fun q => conj (x q.1 q.2.1) * x q.1 q.2.2 with hP
  set W : n × (κ × κ) → ℂ := fun q => ∑ j, (O q.1 j : ℂ) * (y j q.2.1 * conj (y j q.2.2))
    with hW
  have key : ((∑ i, ∑ j, O i j * Complex.normSq (ip (x i) (y j)) : ℝ) : ℂ) =
      ∑ q, P q * W q := by
    rw [Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [← ip_mul_ip_swap, ip_mul_ip_swap_eq]
    simp only [hP, hW, Fintype.sum_prod_type, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.sum_congr rfl fun j _ => by ring
  have hPn : ∑ q, ‖P q‖ ^ 2 = ∑ i, sqNorm (x i) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hP, Complex.sq_norm]
    simp only [Complex.normSq_mul, Complex.normSq_conj, Fintype.sum_prod_type, sqNorm, sq,
      Finset.sum_mul_sum]
  have hWn : ∑ q, ‖W q‖ ^ 2 = ∑ j, sqNorm (y j) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [hW, Complex.sq_norm]
    simp_rw [orthogonal_normSq_sum O hO]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.normSq_mul, Complex.normSq_conj, Fintype.sum_prod_type, sqNorm, sq,
      Finset.sum_mul_sum]
  calc ∑ i, ∑ j, O i j * Complex.normSq (ip (x i) (y j))
      ≤ ‖((∑ i, ∑ j, O i j * Complex.normSq (ip (x i) (y j)) : ℝ) : ℂ)‖ := by
        simpa using
          Complex.re_le_norm ((∑ i, ∑ j, O i j * Complex.normSq (ip (x i) (y j)) : ℝ) : ℂ)
    _ = ‖∑ q, P q * W q‖ := by rw [key]
    _ ≤ ∑ q, ‖P q‖ * ‖W q‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ √(∑ q, ‖P q‖ ^ 2) * √(∑ q, ‖W q‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = √(∑ i, sqNorm (x i) ^ 2) * √(∑ j, sqNorm (y j) ^ 2) := by rw [hPn, hWn]

end Lemma1

/-! ## The trace norm of a real matrix and its variational formula -/

section TraceNorm

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm `‖Q‖_tr = Tr √(QᵀQ)` of a real square matrix: the sum of its singular values
`√λᵢ`, where `λᵢ ≥ 0` are the eigenvalues of `QᵀQ` (`Qᴴ = Qᵀ` over `ℝ`). -/
def traceNorm (Q : Matrix n n ℝ) : ℝ :=
  ∑ i, √((Matrix.isHermitian_conjTranspose_mul_self Q).eigenvalues i)

/-- Completeness of a real orthonormal basis: `∑ᵢ vᵢ(z) vᵢ(y) = δ_{zy}`. -/
lemma orthonormalBasis_sum_mul_self (v : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (z y : n) : ∑ i, (v i).ofLp z * (v i).ofLp y = if z = y then 1 else 0 := by
  have hmem := OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
    (EuclideanSpace.basisFun n ℝ) v
  have h1 := Matrix.mem_unitaryGroup_iff.mp hmem
  have := congrFun (congrFun h1 z) y
  simpa [Matrix.mul_apply, Module.Basis.toMatrix_apply, Matrix.one_apply] using this

/-- Singular value decomposition of a real square matrix: with `vᵢ` the orthonormal
eigenvectors of `QᵀQ` and `σᵢ = √λᵢ`, there is an orthonormal basis `bᵢ` with `Q vᵢ = σᵢ bᵢ`. -/
lemma exists_svd (Q : Matrix n n ℝ) :
    ∃ b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n), ∀ i,
      Q *ᵥ ((Matrix.isHermitian_conjTranspose_mul_self Q).eigenvectorBasis i).ofLp =
        √((Matrix.isHermitian_conjTranspose_mul_self Q).eigenvalues i) • (b i).ofLp := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self Q
  set ev : n → ℝ := hH.eigenvalues with hev
  set v := hH.eigenvectorBasis with hv
  have hev0 : ∀ i, 0 ≤ ev i := fun i =>
    (Matrix.posSemidef_conjTranspose_mul_self Q).eigenvalues_nonneg i
  set w : n → n → ℝ := fun i => Q *ᵥ (v i).ofLp with hw
  have hvv : ∀ i j, (v i).ofLp ⬝ᵥ (v j).ofLp = if i = j then 1 else 0 := by
    intro i j
    have := (orthonormal_iff_ite.mp v.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [eq_comm] using this
  -- `⟨Q vᵢ, Q vⱼ⟩ = λⱼ δᵢⱼ`
  have hww : ∀ i j, w i ⬝ᵥ w j = ev j * (if i = j then 1 else 0) := by
    intro i j
    simp only [hw]
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      hH.mulVec_eigenvectorBasis, dotProduct_smul, hvv, smul_eq_mul]
  set σ : n → ℝ := fun i => √(ev i) with hσ
  set s : Set n := {i | ev i ≠ 0} with hs
  set u : n → EuclideanSpace ℝ n := fun i => WithLp.toLp 2 ((σ i)⁻¹ • w i) with hu
  have hσsq : ∀ i, σ i * σ i = ev i := fun i => Real.mul_self_sqrt (hev0 i)
  -- the normalized images `uᵢ = Q vᵢ / σᵢ` (`σᵢ ≠ 0`) are orthonormal ...
  have hu_on : Orthonormal ℝ (s.domRestrict u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.domRestrict_apply, hu, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      smul_dotProduct, dotProduct_smul, hww, smul_eq_mul, Subtype.mk.injEq]
    by_cases hij : j = i
    · subst hij
      have hi' : ev j ≠ 0 := hi
      have hσ0 : σ j ≠ 0 := by
        intro h0; apply hi'; rw [← hσsq j, h0, zero_mul]
      simp only [if_true, mul_one]
      rw [← hσsq j]
      field_simp
    · simp [hij, Ne.symm hij]
  -- ... and extend to an orthonormal basis `b`
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hu_on
  refine ⟨b, fun i => ?_⟩
  change w i = σ i • (b i).ofLp
  by_cases hi : ev i = 0
  · have h0 : w i ⬝ᵥ w i = 0 := by rw [hww]; simp [hi]
    have hw0 : w i = 0 := dotProduct_self_eq_zero.mp h0
    rw [hw0]
    simp [hσ, hi]
  · have hbi : b i = u i := hb i hi
    have hσ0 : σ i ≠ 0 := by
      intro h0; apply hi; rw [← hσsq i, h0, zero_mul]
    rw [hbi]
    simp only [hu, smul_smul, mul_inv_cancel₀ hσ0, one_smul]

/-- `Tr(Oᵀ Q)` through a singular value decomposition `Q vᵢ = σᵢ bᵢ`:
`∑_{x,y} O_{xy} Q_{xy} = ∑ᵢ σᵢ ⟨bᵢ, O vᵢ⟩`. -/
lemma sum_mul_eq_of_svd (Q O : Matrix n n ℝ) (v b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (σ : n → ℝ) (hQ : ∀ i, Q *ᵥ (v i).ofLp = σ i • (b i).ofLp) :
    ∑ x, ∑ y, O x y * Q x y = ∑ i, σ i * ((b i).ofLp ⬝ᵥ (O *ᵥ (v i).ofLp)) := by
  have hQxy : ∀ x y, Q x y = ∑ i, σ i * (b i).ofLp x * (v i).ofLp y := by
    intro x y
    have hx : ∀ i, (Q *ᵥ (v i).ofLp) x = σ i * (b i).ofLp x := fun i => by
      rw [hQ i]; simp
    calc Q x y = ∑ z, Q x z * (if z = y then 1 else 0) := by simp
      _ = ∑ z, Q x z * ∑ i, (v i).ofLp z * (v i).ofLp y := by
          simp only [orthonormalBasis_sum_mul_self]
      _ = ∑ i, (Q *ᵥ (v i).ofLp) x * (v i).ofLp y := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => by ring
      _ = ∑ i, σ i * (b i).ofLp x * (v i).ofLp y := by simp only [hx]
  simp only [hQxy, Finset.mul_sum, Matrix.mulVec, dotProduct]
  calc ∑ x, ∑ y, ∑ i, O x y * (σ i * (b i).ofLp x * (v i).ofLp y)
      = ∑ x, ∑ i, ∑ y, O x y * (σ i * (b i).ofLp x * (v i).ofLp y) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, O x y * (σ i * (b i).ofLp x * (v i).ofLp y) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => by ring

/-- **Variational formula for the trace norm.** `‖Q‖_tr` is the maximum of
`Tr(Oᵀ Q) = ∑_{i,j} O_{ij} Q_{ij}` over real orthogonal matrices `O`. -/
theorem isGreatest_traceNorm (Q : Matrix n n ℝ) :
    IsGreatest {t | ∃ O ∈ Matrix.orthogonalGroup n ℝ, t = ∑ i, ∑ j, O i j * Q i j}
      (traceNorm Q) := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self Q
  set v := hH.eigenvectorBasis with hv
  set σ : n → ℝ := fun i => √(hH.eigenvalues i) with hσ
  obtain ⟨b, hb⟩ := exists_svd Q
  have hvv : ∀ i j, (v i).ofLp ⬝ᵥ (v j).ofLp = if i = j then 1 else 0 := by
    intro i j
    have := (orthonormal_iff_ite.mp v.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [eq_comm] using this
  have hbb : ∀ i j, (b i).ofLp ⬝ᵥ (b j).ofLp = if i = j then 1 else 0 := by
    intro i j
    have := (orthonormal_iff_ite.mp b.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [eq_comm] using this
  have htr : ∀ O : Matrix n n ℝ,
      ∑ x, ∑ y, O x y * Q x y = ∑ i, σ i * ((b i).ofLp ⬝ᵥ (O *ᵥ (v i).ofLp)) :=
    fun O => sum_mul_eq_of_svd Q O v b σ hb
  constructor
  · -- the maximum is attained at `O = U Vᵀ` (columns `bᵢ` and `vᵢ`)
    set U : Matrix n n ℝ := (EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b with hU
    have hUmem : U ∈ Matrix.unitaryGroup n ℝ :=
      OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _
    have hUapp : ∀ x i, U x i = (b i).ofLp x := by
      intro x i
      simp [hU, Module.Basis.toMatrix_apply]
    set V : Matrix n n ℝ := (hH.eigenvectorUnitary : Matrix n n ℝ) with hV
    have hVmem : V ∈ Matrix.unitaryGroup n ℝ := hH.eigenvectorUnitary.2
    have hVapp : ∀ y i, V y i = (v i).ofLp y := hH.eigenvectorUnitary_apply
    refine ⟨U * V.transpose, ?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff]
      have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hUmem
      have h2 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVmem
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        at h1 h2
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
        ← Matrix.mul_assoc V.transpose, h2, Matrix.one_mul, h1]
    · have hOv : ∀ i, (U * V.transpose) *ᵥ (v i).ofLp = (b i).ofLp := by
        intro i
        rw [← Matrix.mulVec_mulVec]
        have : V.transpose *ᵥ (v i).ofLp = Pi.single i 1 := by
          ext j
          have h := hvv j i
          simp only [dotProduct] at h
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hVapp]
          rw [h]
          simp [Pi.single_apply]
        rw [this]
        ext x
        simp [Matrix.mulVec_single, hUapp]
      rw [htr]
      simp only [hOv, hbb, if_true, mul_one]
      rfl
  · -- every orthogonal `O` gives at most `∑ σᵢ`, since `⟨bᵢ, O vᵢ⟩ ≤ 1`
    rintro t ⟨O, hO, rfl⟩
    rw [htr]
    have hOt : O.transpose * O = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hO
    refine Finset.sum_le_sum fun i _ => ?_
    have hσ0 : 0 ≤ σ i := Real.sqrt_nonneg _
    have hOvOv : (O *ᵥ (v i).ofLp) ⬝ᵥ (O *ᵥ (v i).ofLp) = 1 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
        ← Matrix.dotProduct_mulVec, hOt, Matrix.one_mulVec, hvv, if_pos rfl]
    have hle : (b i).ofLp ⬝ᵥ (O *ᵥ (v i).ofLp) ≤ 1 := by
      have h0 : 0 ≤ ((b i).ofLp - O *ᵥ (v i).ofLp) ⬝ᵥ ((b i).ofLp - O *ᵥ (v i).ofLp) :=
        Finset.sum_nonneg fun x _ => mul_self_nonneg _
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hbb, if_pos rfl, hOvOv,
        dotProduct_comm (O *ᵥ (v i).ofLp)] at h0
      linarith
    calc σ i * ((b i).ofLp ⬝ᵥ (O *ᵥ (v i).ofLp)) ≤ σ i * 1 :=
          mul_le_mul_of_nonneg_left hle hσ0
      _ = σ i := mul_one _

/-- If `Tr(Oᵀ Q) ≤ B` for every real orthogonal `O`, then `‖Q‖_tr ≤ B`. -/
theorem traceNorm_le_of_forall_orthogonal (Q : Matrix n n ℝ) (B : ℝ)
    (h : ∀ O ∈ Matrix.orthogonalGroup n ℝ, ∑ i, ∑ j, O i j * Q i j ≤ B) : traceNorm Q ≤ B := by
  obtain ⟨O, hO, hEq⟩ := (isGreatest_traceNorm Q).1
  rw [hEq]
  exact h O hO

end TraceNorm

/-! ## States, measurements and the probability matrix -/

section States

variable {d m r : ℕ}

/-- A pure state of `ℂ^d ⊗ ℂ^d` of Schmidt rank at most `r`, in Schmidt form
`ψ = ∑_{s<r} σₛ uₛ ⊗ vₛ`: `u, v` are orthonormal families of `ℂ^d`, `σₛ ≥ 0` and
`∑ σₛ² = 1`. (Some `σₛ` may vanish, so the Schmidt rank is at most `r`.) -/
structure SchmidtState (d r : ℕ) where
  /-- Schmidt coefficients. -/
  σ : Fin r → ℝ
  /-- Alice's Schmidt vectors. -/
  u : Fin r → Fin d → ℂ
  /-- Bob's Schmidt vectors. -/
  v : Fin r → Fin d → ℂ
  σ_nonneg : ∀ s, 0 ≤ σ s
  σ_sq_sum : ∑ s, σ s ^ 2 = 1
  u_orthonormal : IsOrthonormal u
  v_orthonormal : IsOrthonormal v

/-- The product vector `x ⊗ y` of `ℂ^d ⊗ ℂ^d = (Fin d × Fin d → ℂ)`. -/
def tensor (x y : Fin d → ℂ) : Fin d × Fin d → ℂ := fun p => x p.1 * y p.2

lemma ip_tensor (a b c e : Fin d → ℂ) : ip (tensor a b) (tensor c e) = ip a c * ip b e := by
  simp only [ip, tensor, Fintype.sum_prod_type, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- The state vector `ψ = ∑ₛ σₛ uₛ ⊗ vₛ`. -/
def SchmidtState.vec (ψ : SchmidtState d r) : Fin d × Fin d → ℂ :=
  ∑ s, (ψ.σ s : ℂ) • tensor (ψ.u s) (ψ.v s)

/-- A vector `Ψ` of `ℂ^d ⊗ ℂ^d` is a unit vector of Schmidt rank at most `r`. -/
def HasSchmidtRankLE (Ψ : Fin d × Fin d → ℂ) (r : ℕ) : Prop :=
  ∃ k ≤ r, ∃ ψ : SchmidtState d k, ψ.vec = Ψ

/-- The density matrix `ρ = ∑ₜ pₜ |Ψₜ⟩⟨Ψₜ|` of a finite ensemble. -/
def ensembleDensity {ι : Type*} [Fintype ι] (p : ι → ℝ) (Ψ : ι → Fin d × Fin d → ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ t, (p t : ℂ) • Matrix.vecMulVec (Ψ t) (star (Ψ t))

/-- `ρ` has Schmidt number at most `r`: it is a finite convex combination of projectors onto
unit vectors of Schmidt rank at most `r`. -/
def HasSchmidtNumberLE (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (r : ℕ) : Prop :=
  ∃ (T : ℕ) (p : Fin T → ℝ) (Ψ : Fin T → Fin d × Fin d → ℂ), (∀ t, 0 ≤ p t) ∧
    ∑ t, p t = 1 ∧ (∀ t, HasSchmidtRankLE (Ψ t) r) ∧ ρ = ensembleDensity p Ψ

/-- The probability matrix of a state `ρ` for Alice's bases `e` and Bob's bases `f`:
`Q_{(k,a),(l,b)} = ⟨e_{k,a} ⊗ f_{l,b}| ρ |e_{k,a} ⊗ f_{l,b}⟩` (real part). This is the matrix
`Q_m` of Tavakoli–Morelli. -/
def probMatrix (e f : Fin m → Fin d → Fin d → ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ :=
  Matrix.of fun i j =>
    (ip (tensor (e i.1 i.2) (f j.1 j.2)) (ρ.mulVec (tensor (e i.1 i.2) (f j.1 j.2)))).re

/-- The probability matrix of a pure state `Ψ`: `Q_{(k,a),(l,b)} = |⟨e_{k,a} ⊗ f_{l,b}|Ψ⟩|²`. -/
def pureProbMatrix (e f : Fin m → Fin d → Fin d → ℂ) (Ψ : Fin d × Fin d → ℂ) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ :=
  Matrix.of fun i j => Complex.normSq (ip (tensor (e i.1 i.2) (f j.1 j.2)) Ψ)

lemma ensembleDensity_mulVec {ι : Type*} [Fintype ι] (p : ι → ℝ) (Ψ : ι → Fin d × Fin d → ℂ)
    (φ : Fin d × Fin d → ℂ) :
    (ensembleDensity p Ψ).mulVec φ = ∑ t, ((p t : ℂ) * ip (Ψ t) φ) • Ψ t := by
  ext q
  simp only [ensembleDensity, Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ip,
    RCLike.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q' _ => by ring

/-- For an ensemble, the probability matrix is the average of the pure-state ones. -/
lemma probMatrix_ensembleDensity {ι : Type*} [Fintype ι] (e f : Fin m → Fin d → Fin d → ℂ)
    (p : ι → ℝ) (Ψ : ι → Fin d × Fin d → ℂ) (i j : Fin m × Fin d) :
    probMatrix e f (ensembleDensity p Ψ) i j = ∑ t, p t * pureProbMatrix e f (Ψ t) i j := by
  simp only [probMatrix, pureProbMatrix, Matrix.of_apply, ensembleDensity_mulVec, ip_sum_right,
    ip_smul_right]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc, mul_comm (ip (Ψ t) _), ip_mul_ip_swap, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- For a pure state `ρ = |Ψ⟩⟨Ψ|`, `probMatrix` is `pureProbMatrix`. -/
lemma probMatrix_pure (e f : Fin m → Fin d → Fin d → ℂ) (Ψ : Fin d × Fin d → ℂ) :
    probMatrix e f (Matrix.vecMulVec Ψ (star Ψ)) = pureProbMatrix e f Ψ := by
  ext i j
  have h := probMatrix_ensembleDensity e f (fun _ : Unit => (1 : ℝ)) (fun _ => Ψ) i j
  simp only [ensembleDensity, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
    one_smul, one_mul] at h
  exact h

/-- `Tr(Oᵀ Q) = ∑_{i,j} O_{ij} Q_{ij}`. -/
lemma trace_transpose_mul {n : Type*} [Fintype n] (O Q : Matrix n n ℝ) :
    (O.transpose * Q).trace = ∑ i, ∑ j, O i j * Q i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

end States

/-! ## Main theorems -/

section Main

variable {d m r : ℕ}

/-- **Main theorem (pure states).** Let `e`, `f` be two families of `m` MUBs of `ℂ^d` and let
`ψ` be a pure state in Schmidt form with `r` terms. Then for every real orthogonal
`md × md` matrix `O`, `∑_{i,j} O_{ij} |⟨e_i ⊗ f_j|ψ⟩|² ≤ 1 + (m - 1) r / d`. -/
theorem schmidt_mub_bound (e f : Fin m → Fin d → Fin d → ℂ) (he : IsMUB d m e)
    (hf : IsMUB d m f) (ψ : SchmidtState d r) (O : Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin m × Fin d) ℝ) :
    ∑ i, ∑ j, O i j * pureProbMatrix e f ψ.vec i j ≤ 1 + ((m : ℝ) - 1) * r / d := by
  -- Step 1: vectors `x i, y j ∈ ℂ^r` with `⟨e_i ⊗ f_j|ψ⟩ = ⟨x_i|y_j⟩`
  set x : Fin m × Fin d → Fin r → ℂ :=
    fun i s => (√(ψ.σ s) : ℂ) * conj (ip (e i.1 i.2) (ψ.u s)) with hx
  set y : Fin m × Fin d → Fin r → ℂ :=
    fun j s => (√(ψ.σ s) : ℂ) * ip (f j.1 j.2) (ψ.v s) with hy
  have hsq : ∀ s, ((√(ψ.σ s) : ℝ) : ℂ) * ((√(ψ.σ s) : ℝ) : ℂ) = (ψ.σ s : ℂ) := by
    intro s
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ψ.σ_nonneg s)]
  have hamp : ∀ i j, ip (tensor (e i.1 i.2) (f j.1 j.2)) ψ.vec = ip (x i) (y j) := by
    intro i j
    simp only [SchmidtState.vec, ip_sum_right, ip_smul_right, ip_tensor]
    simp only [ip, hx, hy, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← hsq s]
    ring
  -- `‖x_i‖² = c_i` and `‖y_j‖² = c'_j`
  have hxn : ∀ i, sqNorm (x i) = diagWeight e ψ.σ ψ.u i.1 i.2 := by
    intro i
    simp only [sqNorm, hx, diagWeight, Complex.normSq_mul, Complex.normSq_conj,
      Complex.normSq_ofReal, Real.mul_self_sqrt (ψ.σ_nonneg _)]
  have hyn : ∀ j, sqNorm (y j) = diagWeight f ψ.σ ψ.v j.1 j.2 := by
    intro j
    simp only [sqNorm, hy, diagWeight, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (ψ.σ_nonneg _)]
  -- Step 2: Lemma 1
  have hOt : O.transpose * O = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hO
  have h1 := orthogonal_weighted_sum_le O hOt x y
  have hrd : r ≤ d := card_le_of_isOrthonormal ψ.u_orthonormal
  set Bnd : ℝ := 1 + ((m : ℝ) - 1) * r / d with hBnd
  have hB0 : 0 ≤ Bnd := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd; simp [hBnd]
      · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
        have : (r : ℝ) / d ≤ 1 := by
          rw [div_le_one hd']; exact_mod_cast hrd
        simp only [hBnd, Nat.cast_zero, zero_sub, neg_one_mul, neg_div]
        linarith
    · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have : 0 ≤ ((m : ℝ) - 1) * r / d := by
        apply div_nonneg _ (Nat.cast_nonneg d)
        exact mul_nonneg (by linarith) (Nat.cast_nonneg r)
      linarith
  -- Step 3: Lemma 2 and `τ² ≤ r`
  have hbound : ∀ (g : Fin m → Fin d → Fin d → ℂ), IsMUB d m g →
      ∀ (w : Fin r → Fin d → ℂ), IsOrthonormal w →
        ∑ k, ∑ a, diagWeight g ψ.σ w k a ^ 2 ≤ Bnd := by
    intro g hg w hw
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simpa using hB0
    have hm' : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hL2 := mub_bessel g hg ψ.σ hw
    rw [ψ.σ_sq_sum] at hL2
    have hτ : (∑ s, ψ.σ s) ^ 2 ≤ r := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := ψ.σ)
      rw [ψ.σ_sq_sum, Finset.card_univ, Fintype.card_fin, mul_one] at this
      exact this
    have : ((m : ℝ) - 1) * (∑ s, ψ.σ s) ^ 2 / d ≤ ((m : ℝ) - 1) * r / d := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
      exact mul_le_mul_of_nonneg_left hτ hm'
    linarith
  have hX : ∑ i, sqNorm (x i) ^ 2 ≤ Bnd := by
    simp only [hxn, Fintype.sum_prod_type]
    exact hbound e he ψ.u ψ.u_orthonormal
  have hY : ∑ j, sqNorm (y j) ^ 2 ≤ Bnd := by
    simp only [hyn, Fintype.sum_prod_type]
    exact hbound f hf ψ.v ψ.v_orthonormal
  -- Step 4: combine
  calc ∑ i, ∑ j, O i j * pureProbMatrix e f ψ.vec i j
      = ∑ i, ∑ j, O i j * Complex.normSq (ip (x i) (y j)) := by
        simp only [pureProbMatrix, Matrix.of_apply, hamp]
    _ ≤ √(∑ i, sqNorm (x i) ^ 2) * √(∑ j, sqNorm (y j) ^ 2) := h1
    _ ≤ √Bnd * √Bnd := by
        apply mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = Bnd := Real.mul_self_sqrt hB0

/-- A bound valid for every pure state of an ensemble holds for the ensemble's density matrix. -/
lemma ensemble_bound {ι : Type*} [Fintype ι] (e f : Fin m → Fin d → Fin d → ℂ) (p : ι → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hp1 : ∑ t, p t = 1) (Ψ : ι → Fin d × Fin d → ℂ)
    (O : Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ) (B : ℝ)
    (hB : ∀ t, ∑ i, ∑ j, O i j * pureProbMatrix e f (Ψ t) i j ≤ B) :
    ∑ i, ∑ j, O i j * probMatrix e f (ensembleDensity p Ψ) i j ≤ B := by
  simp only [probMatrix_ensembleDensity]
  calc ∑ i, ∑ j, O i j * ∑ t, p t * pureProbMatrix e f (Ψ t) i j
      = ∑ i, ∑ t, ∑ j, p t * (O i j * pureProbMatrix e f (Ψ t) i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => by ring
    _ = ∑ t, p t * ∑ i, ∑ j, O i j * pureProbMatrix e f (Ψ t) i j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [Finset.mul_sum]
    _ ≤ ∑ t, p t * B := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hB t) (hp t)
    _ = B := by rw [← Finset.sum_mul, hp1, one_mul]

/-- **Main theorem (mixed states).** For a finite ensemble `ρ = ∑ₜ pₜ |ψₜ⟩⟨ψₜ|` of pure states
in Schmidt form with `r` terms, and every real orthogonal `O`,
`∑_{i,j} O_{ij} ⟨e_i ⊗ f_j|ρ|e_i ⊗ f_j⟩ ≤ 1 + (m - 1) r / d`. -/
theorem schmidt_mub_bound_mixed {ι : Type*} [Fintype ι] (e f : Fin m → Fin d → Fin d → ℂ)
    (he : IsMUB d m e) (hf : IsMUB d m f) (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t)
    (hp1 : ∑ t, p t = 1) (ψ : ι → SchmidtState d r)
    (O : Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin m × Fin d) ℝ) :
    ∑ i, ∑ j, O i j * probMatrix e f (ensembleDensity p fun t => (ψ t).vec) i j ≤
      1 + ((m : ℝ) - 1) * r / d :=
  ensemble_bound e f p hp hp1 _ O _ fun t => schmidt_mub_bound e f he hf (ψ t) O hO

/-- The pure-state bound for any unit vector of Schmidt rank at most `r` (needs `m ≥ 1`,
since then the bound is monotone in `r`). -/
theorem schmidt_mub_bound_of_rankLE (hm : 1 ≤ m) (e f : Fin m → Fin d → Fin d → ℂ)
    (he : IsMUB d m e) (hf : IsMUB d m f) (Ψ : Fin d × Fin d → ℂ) (hΨ : HasSchmidtRankLE Ψ r)
    (O : Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin m × Fin d) ℝ) :
    ∑ i, ∑ j, O i j * pureProbMatrix e f Ψ i j ≤ 1 + ((m : ℝ) - 1) * r / d := by
  obtain ⟨k, hk, ψ, rfl⟩ := hΨ
  have hm' : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hk' : (k : ℝ) ≤ r := by exact_mod_cast hk
  calc ∑ i, ∑ j, O i j * pureProbMatrix e f ψ.vec i j ≤ 1 + ((m : ℝ) - 1) * k / d :=
        schmidt_mub_bound e f he hf ψ O hO
    _ ≤ 1 + ((m : ℝ) - 1) * r / d := by
        have : ((m : ℝ) - 1) * k / d ≤ ((m : ℝ) - 1) * r / d :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk' hm') (Nat.cast_nonneg d)
        linarith

/-- **Tavakoli–Morelli, Conjecture 3, dual form.** Let `e` and `f` be two sets of `m ≥ 1`
mutually unbiased bases of `ℂ^d` (for Alice and for Bob), let `ρ` be a state of `ℂ^d ⊗ ℂ^d`
with Schmidt number at most `r`, and let `Q = probMatrix e f ρ`,
`Q_{(k,a),(l,b)} = ⟨e_{k,a} ⊗ f_{l,b}|ρ|e_{k,a} ⊗ f_{l,b}⟩`. Then
`Tr(Oᵀ Q) ≤ 1 + (m - 1) r / d` for every real orthogonal matrix `O`. -/
theorem tavakoli_morelli_conjecture_3_dual (hm : 1 ≤ m) (e f : Fin m → Fin d → Fin d → ℂ)
    (he : IsMUB d m e) (hf : IsMUB d m f) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hρ : HasSchmidtNumberLE ρ r) (O : Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin m × Fin d) ℝ) :
    (O.transpose * probMatrix e f ρ).trace ≤ 1 + ((m : ℝ) - 1) * r / d := by
  obtain ⟨T, p, Ψ, hp, hp1, hΨ, rfl⟩ := hρ
  rw [trace_transpose_mul]
  exact ensemble_bound e f p hp hp1 Ψ O _ fun t =>
    schmidt_mub_bound_of_rankLE hm e f he hf (Ψ t) (hΨ t) O hO

/-- **Tavakoli–Morelli, Conjecture 3** (arXiv:2402.09972). Let `e` and `f` be two sets of
`m ≥ 1` mutually unbiased bases of `ℂ^d` (for Alice and for Bob) and let `ρ` be a state of
`ℂ^d ⊗ ℂ^d` with Schmidt number at most `r`. Then the `md × md` matrix of joint outcome
probabilities `Q_{(k,a),(l,b)} = ⟨e_{k,a} ⊗ f_{l,b}|ρ|e_{k,a} ⊗ f_{l,b}⟩` satisfies
`‖Q‖_tr ≤ 1 + (m - 1) r / d`. -/
theorem tavakoli_morelli_conjecture_3 (hm : 1 ≤ m) (e f : Fin m → Fin d → Fin d → ℂ)
    (he : IsMUB d m e) (hf : IsMUB d m f) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hρ : HasSchmidtNumberLE ρ r) :
    traceNorm (probMatrix e f ρ) ≤ 1 + ((m : ℝ) - 1) * r / d := by
  refine traceNorm_le_of_forall_orthogonal _ _ fun O hO => ?_
  rw [← trace_transpose_mul]
  exact tavakoli_morelli_conjecture_3_dual hm e f he hf ρ hρ O hO

/-- The trace-norm bound for a pure state in Schmidt form (no restriction on `m`). -/
theorem schmidt_mub_traceNorm_bound (e f : Fin m → Fin d → Fin d → ℂ) (he : IsMUB d m e)
    (hf : IsMUB d m f) (ψ : SchmidtState d r) :
    traceNorm (pureProbMatrix e f ψ.vec) ≤ 1 + ((m : ℝ) - 1) * r / d :=
  traceNorm_le_of_forall_orthogonal _ _ fun O hO => schmidt_mub_bound e f he hf ψ O hO

end Main

/-! ## Sanity checks: the hypotheses are satisfiable -/

section Examples

/-- The standard basis of `ℂ^d`. -/
def stdBasis (d : ℕ) : Fin d → Fin d → ℂ := fun a x => if x = a then 1 else 0

lemma stdBasis_isOrthonormal (d : ℕ) : IsOrthonormal (stdBasis d) := by
  intro a b
  rcases eq_or_ne a b with h | h
  · subst h
    simp [ip, stdBasis]
  · simp [ip, stdBasis, h, h.symm]

/-- `1/√2` as a complex number. -/
def invSqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  rw [invSqrt2, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

lemma conj_invSqrt2 : conj invSqrt2 = invSqrt2 := Complex.conj_ofReal _

lemma normSq_invSqrt2 : Complex.normSq invSqrt2 = 1 / 2 := by
  rw [invSqrt2, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The Hadamard basis `{(|0⟩ + |1⟩)/√2, (|0⟩ - |1⟩)/√2}` of `ℂ²`. -/
def hadamardBasis : Fin 2 → Fin 2 → ℂ := ![![invSqrt2, invSqrt2], ![invSqrt2, -invSqrt2]]

lemma hadamardBasis_isOrthonormal : IsOrthonormal hadamardBasis := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [ip, hadamardBasis, Fin.sum_univ_two, conj_invSqrt2, invSqrt2_mul_self] <;> norm_num

/-- The computational and Hadamard bases: a pair of MUBs of `ℂ²`. -/
def qubitMUBs : Fin 2 → Fin 2 → Fin 2 → ℂ := ![stdBasis 2, hadamardBasis]

lemma qubitMUBs_isMUB : IsMUB 2 2 qubitMUBs := by
  refine ⟨fun k => ?_, fun k l hkl a b => ?_⟩
  · fin_cases k
    · exact stdBasis_isOrthonormal 2
    · exact hadamardBasis_isOrthonormal
  · fin_cases k <;> fin_cases l <;> simp at hkl <;> fin_cases a <;> fin_cases b <;>
      simp [ip, qubitMUBs, stdBasis, hadamardBasis, conj_invSqrt2, normSq_invSqrt2]

/-- The two-qubit maximally entangled state `(|00⟩ + |11⟩)/√2` in Schmidt form. -/
def bellState : SchmidtState 2 2 where
  σ := fun _ => (Real.sqrt 2)⁻¹
  u := stdBasis 2
  v := stdBasis 2
  σ_nonneg := fun _ => by positivity
  σ_sq_sum := by
    simp only [Fin.sum_univ_two, inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  u_orthonormal := stdBasis_isOrthonormal 2
  v_orthonormal := stdBasis_isOrthonormal 2

/-- The main theorem instantiated: two qubit MUBs on each side and the maximally entangled
state; the bound is `1 + (2 - 1) · 2 / 2 = 2`. -/
example (O : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin 2 × Fin 2) ℝ) :
    ∑ i, ∑ j, O i j * pureProbMatrix qubitMUBs qubitMUBs bellState.vec i j ≤ 2 := by
  have := schmidt_mub_bound qubitMUBs qubitMUBs qubitMUBs_isMUB qubitMUBs_isMUB bellState O hO
  norm_num at this
  exact this

end Examples

end TMProof

#print axioms TMProof.schmidt_mub_bound
#print axioms TMProof.schmidt_mub_bound_mixed
#print axioms TMProof.tavakoli_morelli_conjecture_3_dual
#print axioms TMProof.tavakoli_morelli_conjecture_3
