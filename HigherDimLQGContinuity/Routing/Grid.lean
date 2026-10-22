import HigherDimLFPP.Frozen.Rd
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Grids, Gram determinants and hyperplane counts (rational general position, R4)

Packet Q2 (ruling N9). Source: planning audit `planning/audits/NA2-section-4.md`, Details (c)
**R4**; blueprint Part B, Lemma `b:lem-gp` ([C] p. 11–12, l. 579–594).

* `OnGrid ν o z`: `z ∈ o + νℤ^d` (the NA2 probe definition); `gridRound ν o x`, the nearest-point
  rounding to the grid, with error `≤ √d ν / 2` (`norm_gridRound_sub_le`).
* **Separation of grid segments** (`grid_segment_sep`): if `p, p′, q, q′ ∈ o + νℤ^d` are affinely
  independent, then every `x ∈ [p, p′]`, `y ∈ [q, q′]` satisfy `ν³ ≤ |x - y| |p′ - p| |q′ - q|`.
  Proof by Gram determinants instead of the blueprint's `3 × 3` minor: with `u = p′ - p`,
  `w = q′ - q`, `b = p - q` (linearly independent), `Γ := det Gram(u, w, b) > 0` is `ν⁶` times a
  positive integer, so `Γ ≥ ν⁶`; for `z = x - y = b + s u - t w`, `det Gram(u, w, z) = Γ`
  (`det_gram_shift`) and `det Gram(u, w, z) ≤ |z|²|u|²|w|²` (`det_gram_le`, from
  `det Gram(u, w, z) = |z|²(|u|²|w|² - ⟪u,w⟫²) - |⟪u,z⟫w - ⟪w,z⟫u|²`).
* Incident segments (`segment_inter_segment_eq`): for affinely independent `P, Q, R`,
  `[P, Q] ∩ [Q, R] = {Q}`, and `{P, Q, R}` is not collinear (`not_collinear_of_indep3`).
* **Hyperplane counts**: `exists_normal` (`d ≥ 3`: two vectors have a common nonzero normal) and
  `card_filter_inner_eq_le` (a hyperplane `⟪a, ·⟫ = c`, `a ≠ 0`, contains at most `M^{d-1}` of the
  `M^d` points `base + ν m`, `m ∈ {0, …, M-1}^d`); hence `exists_onGrid_avoid`: if `M` exceeds the
  number of triples, some grid point within `√d ν M` of `v` avoids every affine plane
  `Y + span(Z - Y, W - Y)` of a finite family of triples.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open scoped InnerProductSpace

namespace HigherDimLQGContinuity.Routing

variable {d : ℕ}

/-! ### The grid `o + νℤ^d` -/

/-- `z` lies on the grid `o + ν ℤ^d`. -/
def OnGrid (ν : ℝ) (o z : Rd d) : Prop := ∃ k : Fin d → ℤ, ∀ i, z i = o i + ν * k i

/-- The nearest-point rounding of `x` to the grid `o + νℤ^d`. -/
def gridRound (ν : ℝ) (o x : Rd d) : Rd d :=
  WithLp.toLp 2 fun i => o i + ν * (round ((x i - o i) / ν) : ℝ)

lemma onGrid_gridRound (ν : ℝ) (o x : Rd d) : OnGrid ν o (gridRound ν o x) :=
  ⟨fun i => round ((x i - o i) / ν), fun i => by simp [gridRound]⟩

/-- A vector with all coordinates bounded by `c` has norm at most `√d c`. -/
lemma norm_le_sqrt_mul_of_abs_le {v : Rd d} {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, |v i| ≤ c) :
    ‖v‖ ≤ √(d : ℝ) * c := by
  rw [EuclideanSpace.norm_eq]
  have hcoord : ∀ j, ‖v.ofLp j‖ ^ 2 ≤ c ^ 2 := by
    intro j
    rw [Real.norm_eq_abs, sq_abs]
    have := hv j
    have h0 := abs_nonneg (v j)
    nlinarith [abs_mul_abs_self (v j)]
  calc √(∑ j, ‖v.ofLp j‖ ^ 2) ≤ √(∑ _j : Fin d, c ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hcoord j)
    _ = √(d : ℝ) * c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc]

/-- The rounding error: `|gridRound ν o x - x| ≤ √d ν / 2`. -/
lemma norm_gridRound_sub_le {ν : ℝ} (hν : 0 < ν) (o x : Rd d) :
    ‖gridRound ν o x - x‖ ≤ √(d : ℝ) * (ν / 2) := by
  refine norm_le_sqrt_mul_of_abs_le (by positivity) fun i => ?_
  have hco : (gridRound ν o x - x) i = ν * ((round ((x i - o i) / ν) : ℝ) - (x i - o i) / ν) := by
    simp only [gridRound, PiLp.sub_apply]
    field_simp
    ring
  rw [hco, abs_mul, abs_of_pos hν, abs_sub_comm]
  have := abs_sub_round ((x i - o i) / ν)
  nlinarith

/-- Differences of grid points have coordinates in `νℤ`. -/
lemma OnGrid.sub {ν : ℝ} {o x y : Rd d} (hx : OnGrid ν o x) (hy : OnGrid ν o y) :
    ∃ k : Fin d → ℤ, ∀ i, (x - y) i = ν * k i := by
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  refine ⟨kx - ky, fun i => ?_⟩
  simp only [PiLp.sub_apply, hkx, hky, Pi.sub_apply, Int.cast_sub]
  ring

/-! ### Gram determinants of three vectors -/

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram determinant of three vectors, expanded. -/
lemma det_gram_three (u w z : E) :
    (Matrix.gram ℝ ![u, w, z]).det =
      ⟪u, u⟫_ℝ * ⟪w, w⟫_ℝ * ⟪z, z⟫_ℝ + 2 * (⟪u, w⟫_ℝ * ⟪w, z⟫_ℝ * ⟪u, z⟫_ℝ)
        - ⟪u, u⟫_ℝ * ⟪w, z⟫_ℝ ^ 2 - ⟪w, w⟫_ℝ * ⟪u, z⟫_ℝ ^ 2 - ⟪z, z⟫_ℝ * ⟪u, w⟫_ℝ ^ 2 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [real_inner_comm w u, real_inner_comm z u, real_inner_comm z w]
  ring

/-- Hadamard-type bound: `det Gram(u, w, z) ≤ |z|² |u|² |w|²`. -/
lemma det_gram_le (u w z : E) :
    (Matrix.gram ℝ ![u, w, z]).det ≤ ‖z‖ ^ 2 * ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
  rw [det_gram_three]
  set X : E := ⟪u, z⟫_ℝ • w - ⟪w, z⟫_ℝ • u with hX
  have hXX : 0 ≤ ⟪X, X⟫_ℝ := real_inner_self_nonneg
  have hXe : ⟪X, X⟫_ℝ = ⟪u, z⟫_ℝ ^ 2 * ⟪w, w⟫_ℝ - 2 * (⟪u, z⟫_ℝ * ⟪w, z⟫_ℝ * ⟪u, w⟫_ℝ)
      + ⟪w, z⟫_ℝ ^ 2 * ⟪u, u⟫_ℝ := by
    rw [hX]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm w u]
    ring
  simp only [real_inner_self_eq_norm_sq] at hXe ⊢
  have h1 : 0 ≤ ‖z‖ ^ 2 * ⟪u, w⟫_ℝ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith

/-- The Gram determinant is unchanged when `z` is moved inside `z + span(u, w)`. -/
lemma det_gram_shift (u w b : E) (s t : ℝ) :
    (Matrix.gram ℝ ![u, w, b + s • u - t • w]).det = (Matrix.gram ℝ ![u, w, b]).det := by
  rw [det_gram_three, det_gram_three]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm w u, real_inner_comm b u, real_inner_comm b w]
  ring

end Gram

/-- The Gram determinant of three vectors of `νℤ^d` is `ν⁶` times an integer. -/
lemma exists_det_gram_eq_int_mul {ν : ℝ} (V : Fin 3 → Rd d) (k : Fin 3 → Fin d → ℤ)
    (hk : ∀ a i, V a i = ν * k a i) :
    ∃ D : ℤ, (Matrix.gram ℝ V).det = ν ^ 6 * D := by
  classical
  let K : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun a b => ∑ i, k a i * k b i
  have hG : Matrix.gram ℝ V = (ν ^ 2) • (Int.castRingHom ℝ).mapMatrix K := by
    ext a b
    simp only [Matrix.gram_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      smul_eq_mul, Int.coe_castRingHom, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hk]
    rw [show ((K a b : ℤ) : ℝ) = ∑ i, (k a i : ℝ) * k b i by simp [K], Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  refine ⟨K.det, ?_⟩
  rw [hG, Matrix.det_smul, ← RingHom.map_det, Fintype.card_fin, Int.coe_castRingHom, ← pow_mul]

/-! ### Separation of grid segments -/

/-- **Separation of grid segments** (R4): if `p, p′, q, q′ ∈ o + νℤ^d` are affinely independent
(in the weight form `hind`), then points `x ∈ [p, p′]`, `y ∈ [q, q′]` satisfy
`ν³ ≤ |x - y| |p′ - p| |q′ - q|`. -/
theorem grid_segment_sep {ν : ℝ} (hν : 0 < ν) {o p p' q q' : Rd d} (hp : OnGrid ν o p)
    (hp' : OnGrid ν o p') (hq : OnGrid ν o q) (hq' : OnGrid ν o q')
    (hind : ∀ a b c e : ℝ, a + b + c + e = 0 → a • p + b • p' + c • q + e • q' = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0)
    {x y : Rd d} (hx : x ∈ segment ℝ p p') (hy : y ∈ segment ℝ q q') :
    ν ^ 3 ≤ dist x y * ‖p' - p‖ * ‖q' - q‖ := by
  set u := p' - p with hu
  set w := q' - q with hw
  set b := p - q with hb
  -- linear independence of `u, w, b`
  have hli : LinearIndependent ℝ ![u, w, b] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hg
    have h := hind (g 2 - g 0) (g 0) (-g 1 - g 2) (g 1) (by ring) (by
      rw [← hg, hu, hw, hb]; module)
    obtain ⟨h1, h2, _, h4⟩ := h
    intro i
    fin_cases i
    · exact h2
    · exact h4
    · simp only [Fin.reduceFinMk, Fin.isValue]
      linarith
  -- the Gram determinant is a positive multiple of `ν⁶`
  have hpos : 0 < (Matrix.gram ℝ ![u, w, b]).det :=
    (Matrix.posDef_gram_of_linearIndependent hli).det_pos
  obtain ⟨ku, hku⟩ := hp'.sub hp
  obtain ⟨kw, hkw⟩ := hq'.sub hq
  obtain ⟨kb, hkb⟩ := hp.sub hq
  obtain ⟨D, hD⟩ := exists_det_gram_eq_int_mul ![u, w, b] ![ku, kw, kb] (by
    intro a i
    fin_cases a
    · exact hku i
    · exact hkw i
    · exact hkb i)
  have hν6 : 0 < ν ^ 6 := by positivity
  have hD1 : (1 : ℝ) ≤ D := by
    have : (0 : ℝ) < D := by
      rw [hD] at hpos
      exact pos_of_mul_pos_right hpos hν6.le
    exact_mod_cast (show (0 : ℤ) < D by exact_mod_cast this)
  have hge : ν ^ 6 ≤ (Matrix.gram ℝ ![u, w, b]).det := by
    rw [hD]; nlinarith
  -- `x - y = b + s u - t w`
  rw [segment_eq_image'] at hx hy
  obtain ⟨s, -, rfl⟩ := hx
  obtain ⟨t, -, rfl⟩ := hy
  have hz : p + s • (p' - p) - (q + t • (q' - q)) = b + s • u - t • w := by
    rw [hb, hu, hw]; abel
  have hle := det_gram_le u w (b + s • u - t • w)
  rw [det_gram_shift] at hle
  rw [dist_eq_norm, hz]
  have hsq : (ν ^ 3) ^ 2 ≤ (‖b + s • u - t • w‖ * ‖u‖ * ‖w‖) ^ 2 := by
    calc (ν ^ 3) ^ 2 = ν ^ 6 := by ring
      _ ≤ _ := hge.trans hle
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 hsq

/-! ### Three affinely independent points -/

/-- Incident segments of three affinely independent points meet only at the common vertex. -/
theorem segment_inter_segment_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {P Q R : E}
    (hind : ∀ a b c : ℝ, a + b + c = 0 → a • P + b • Q + c • R = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    segment ℝ P Q ∩ segment ℝ Q R = {Q} := by
  apply Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    rw [segment_eq_image'] at hx1 hx2
    obtain ⟨s, -, rfl⟩ := hx1
    obtain ⟨t, -, ht⟩ := hx2
    simp only at ht ⊢
    have h := hind (1 - s) (s - 1 + t) (-t) (by ring) (by
      have : P + s • (Q - P) - (Q + t • (R - Q)) = 0 := by rw [ht, sub_self]
      rw [← this]; module)
    have hs : s = 1 := by linarith [h.1]
    rw [hs, one_smul, add_sub_cancel]
    exact mem_singleton _
  · rw [singleton_subset_iff]
    exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩

/-- Three affinely independent points (weight form) are not collinear. -/
theorem not_collinear_of_indep3 {E : Type*} [AddCommGroup E] [Module ℝ E] {P Q R : E}
    (hind : ∀ a b c : ℝ, a + b + c = 0 → a • P + b • Q + c • R = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    ¬ Collinear ℝ {P, Q, R} := by
  classical
  rw [← affineIndependent_iff_not_collinear_set, affineIndependent_iff]
  intro s g hg hgs
  let g' : Fin 3 → ℝ := fun i => if i ∈ s then g i else 0
  have hsum : ∀ f : Fin 3 → E, ∑ i ∈ s, g i • f i = ∑ i, g' i • f i := by
    intro f
    rw [← Finset.sum_subset (Finset.subset_univ s)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [g', hi, ite_true]
    · intro i _ hi
      simp only [g', hi, ite_false, zero_smul]
  have hsum' : ∑ i ∈ s, g i = ∑ i, g' i := by
    rw [← Finset.sum_subset (Finset.subset_univ s)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [g', hi, ite_true]
    · intro i _ hi
      simp only [g', hi, ite_false]
  rw [hsum'] at hg
  rw [hsum] at hgs
  rw [Fin.sum_univ_three] at hg hgs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hgs
  obtain ⟨h0, h1, h2⟩ := hind _ _ _ hg hgs
  intro i hi
  have : g' i = 0 := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  simpa [g', hi] using this

/-! ### Normals and hyperplane counts -/

/-- In `ℝ^d`, `d ≥ 3`, two vectors have a common nonzero normal. -/
lemma exists_normal (hd : 3 ≤ d) (u₁ u₂ : Rd d) :
    ∃ a : Rd d, a ≠ 0 ∧ ⟪a, u₁⟫_ℝ = 0 ∧ ⟪a, u₂⟫_ℝ = 0 := by
  set K : Submodule ℝ (Rd d) := Submodule.span ℝ (Set.range ![u₁, u₂]) with hK
  have hKr : Module.finrank ℝ K ≤ 2 := by
    have := finrank_range_le_card (R := ℝ) ![u₁, u₂]
    simpa [Set.finrank] using this
  have hsum := Submodule.finrank_add_finrank_orthogonal K
  rw [finrank_euclideanSpace_fin] at hsum
  have hne : Kᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h1 : u₁ ∈ K := Submodule.subset_span ⟨0, rfl⟩
  have h2 : u₂ ∈ K := Submodule.subset_span ⟨1, rfl⟩
  refine ⟨a, ha0, ?_, ?_⟩
  · rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal h1 ha
  · rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal h2 ha

/-- The grid vector `(m_1, …, m_d)` of an index `m ∈ {0, …, M-1}^d`. -/
def gridVec {M : ℕ} (m : Fin d → Fin M) : Rd d := WithLp.toLp 2 fun j => ((m j : ℕ) : ℝ)

/-- A hyperplane `⟪a, ·⟫ = c` (`a ≠ 0`) contains at most `M^{d-1}` of the points `base + ν m`,
`m ∈ {0, …, M-1}^d`. -/
lemma card_filter_inner_eq_le {M : ℕ} {ν : ℝ} (hν : ν ≠ 0)
    (base : Rd d) {a : Rd d} (ha : a ≠ 0) (c : ℝ) :
    (Finset.univ.filter fun m : Fin d → Fin M => ⟪a, base + ν • gridVec m⟫_ℝ = c).card ≤
      M ^ (d - 1) := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, a j₀ ≠ 0 := by
    by_contra h
    exact ha (by ext j; by_contra hj; exact h ⟨j, hj⟩)
  let f : (Fin d → Fin M) → ({j // j ≠ j₀} → Fin M) := fun m j => m j
  have hcard : (Finset.univ : Finset ({j // j ≠ j₀} → Fin M)).card = M ^ (d - 1) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
  intro m hm m' hm' hmm'
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm hm'
  have hoff : ∀ j, j ≠ j₀ → m j = m' j := fun j hj => congrFun hmm' ⟨j, hj⟩
  -- the difference of the two equations involves only the coordinate `j₀`
  have hdiff : ⟪a, ν • (gridVec m - gridVec m')⟫_ℝ = 0 := by
    have : ⟪a, base + ν • gridVec m⟫_ℝ - ⟪a, base + ν • gridVec m'⟫_ℝ = 0 := by
      rw [hm, hm', sub_self]
    rw [← this, ← inner_sub_right, smul_sub]
    congr 1
    abel
  have hsum : ⟪a, ν • (gridVec m - gridVec m')⟫_ℝ =
      a j₀ * (ν * (((m j₀ : ℕ) : ℝ) - ((m' j₀ : ℕ) : ℝ))) := by
    rw [PiLp.inner_apply, Finset.sum_eq_single j₀]
    · simp [gridVec, mul_comm]
    · intro j _ hj
      simp [gridVec, hoff j hj]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  rw [hsum] at hdiff
  have hj : ((m j₀ : ℕ) : ℝ) = ((m' j₀ : ℕ) : ℝ) := by
    have := (mul_eq_zero.1 hdiff).resolve_left hj₀
    have := (mul_eq_zero.1 this).resolve_left hν
    linarith
  funext j
  by_cases hjj : j = j₀
  · subst hjj
    exact Fin.ext (by exact_mod_cast hj)
  · exact hoff j hjj

/-- **Avoiding finitely many affine planes on the grid.** If `M` exceeds the number of triples
`(Y τ, Z τ, W τ)`, there is a grid point `x` within `√d ν M` of `v` with
`x - Y τ ∉ span(Z τ - Y τ, W τ - Y τ)` for every `τ` (`d ≥ 3`). -/
theorem exists_onGrid_avoid (hd : 3 ≤ d) {ν : ℝ} (hν : 0 < ν) (o v : Rd d) {T : Type*}
    [Fintype T] (Y Z W : T → Rd d) {M : ℕ} (hM : Fintype.card T < M) :
    ∃ x : Rd d, OnGrid ν o x ∧ ‖x - v‖ ≤ √(d : ℝ) * ν * M ∧
      ∀ τ : T, ∀ b c : ℝ, x - Y τ ≠ b • (Z τ - Y τ) + c • (W τ - Y τ) := by
  classical
  -- a normal for every triple
  have hn : ∀ τ : T, ∃ a : Rd d, a ≠ 0 ∧ ⟪a, Z τ - Y τ⟫_ℝ = 0 ∧ ⟪a, W τ - Y τ⟫_ℝ = 0 :=
    fun τ => exists_normal hd _ _
  choose a ha0 haZ haW using hn
  set base := gridRound ν o v with hbase
  let bad : T → Finset (Fin d → Fin M) := fun τ =>
    Finset.univ.filter fun m => ⟪a τ, base + ν • gridVec m⟫_ℝ = ⟪a τ, Y τ⟫_ℝ
  have hbad : (Finset.univ.biUnion bad).card < (Finset.univ : Finset (Fin d → Fin M)).card := by
    have hd1 : d = (d - 1) + 1 := by omega
    calc (Finset.univ.biUnion bad).card ≤ ∑ τ, (bad τ).card := Finset.card_biUnion_le
      _ ≤ ∑ _τ : T, M ^ (d - 1) :=
          Finset.sum_le_sum fun τ _ => card_filter_inner_eq_le hν.ne' base (ha0 τ) _
      _ = Fintype.card T * M ^ (d - 1) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ < M * M ^ (d - 1) := by
          apply Nat.mul_lt_mul_of_pos_right hM
          exact pow_pos (by omega) _
      _ = (Finset.univ : Finset (Fin d → Fin M)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_succ',
            ← hd1]
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  refine ⟨base + ν • gridVec m, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := onGrid_gridRound ν o v
    have hk' : ∀ i, base i = o i + ν * k i := hk
    refine ⟨fun i => k i + ((m i : ℕ) : ℤ), fun i => ?_⟩
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, gridVec, hk' i,
      Int.cast_add, Int.cast_natCast]
    ring
  · have h1 := norm_gridRound_sub_le hν o v
    have hM0 : (0 : ℝ) ≤ (M : ℝ) - 1 := by
      have : 1 ≤ M := by omega
      rw [sub_nonneg]; exact_mod_cast this
    have h2 : ‖ν • gridVec m‖ ≤ √(d : ℝ) * (ν * ((M : ℝ) - 1)) := by
      refine norm_le_sqrt_mul_of_abs_le (by positivity) fun i => ?_
      simp only [PiLp.smul_apply, smul_eq_mul, gridVec, abs_mul, abs_of_pos hν]
      apply mul_le_mul_of_nonneg_left _ hν.le
      rw [Nat.abs_cast]
      have : (m i : ℕ) + 1 ≤ M := (m i).isLt
      have : ((m i : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast this
      linarith
    calc ‖base + ν • gridVec m - v‖ = ‖(base - v) + ν • gridVec m‖ := by congr 1; abel
      _ ≤ ‖base - v‖ + ‖ν • gridVec m‖ := norm_add_le _ _
      _ ≤ √(d : ℝ) * (ν / 2) + √(d : ℝ) * (ν * ((M : ℝ) - 1)) := add_le_add h1 h2
      _ ≤ √(d : ℝ) * ν * M := by
          have : 0 ≤ √(d : ℝ) * ν := by positivity
          nlinarith
  · intro τ b c heq
    apply hm
    rw [Finset.mem_biUnion]
    refine ⟨τ, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    have : ⟪a τ, base + ν • gridVec m - Y τ⟫_ℝ = 0 := by
      rw [heq, inner_add_right, real_inner_smul_right, real_inner_smul_right, haZ, haW]
      ring
    rw [inner_sub_right, sub_eq_zero] at this
    exact this

end HigherDimLQGContinuity.Routing

end
