/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Heights
import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.ForceWord_ThresholdCondition

/-!
# Boundary heights and force partial sums (Remark 4.1, Lemmas 4.3, 4.5, Aux. lemma 22)

Packet PROVE-SEC4-A (specification §4.1, `source/spec/p097-144.md` L182–L470).

Every proof of §4.1 converts boundary heights of the half-plane chart into cumulative force weights: a left height
`h` is the cumulative weight `−h/Λ − 1`, a right height `h` the weight `h/Λ − 1` (Aux. lemma 22's "conversion").
With the frozen boundary data `forceBoundaryData k ρL ρR xL xR` of a force word this file proves:

* `HasAdmissiblePartialSums`: the hypothesis of Aux. lemma 6, Remark 2.3 and Aux. lemma 7 — after amalgamating
  coincident groups, every nonempty side prefix sum is at least `c = k/2 − 2` — stated through positions: for
  `x < 0` the marks strictly right of `x`, for `x ≥ 0` the marks at or left of `x`;
* `hasAdmissiblePartialSums_iff`: this is exactly Remark 4.1's boundary condition in the chart — the data is at most
  `−Λ + π X` left of `0` and at least `Λ − π X` right of `0`, wherever a mark lies between the point and the seed
  (no condition on an empty initial interval: "One must not insert a zero seed force and demand `0 ≥ k/2 − 2` when
  `k > 4`");
* `hasAdmissiblePartialSums_of_forall_not_mem`: the condition need only be checked off a finite set (the values at
  jump points do not matter);
* `not_thresholdCondition_iff_of_collide`: at a first upper contact the colliding left group carries the cumulative
  weight of the contact point, so the continuation threshold of the frozen `ForceWord.ThresholdCondition` is not
  reached exactly when the height there exceeds the critical value (Lemma 4.3's continuation assertions, with
  (HB1): `ρ_left = k/2 − 3 − a/Λ`, `ρ_right = k/2 − 3 + a/Λ`).
-/

set_option autoImplicit false

noncomputable section

open Real Finset

namespace InteractingSLE

namespace Sec4

open QuantumZipper (chiC)

variable {k : ℝ} {nL nR : ℕ}

/-- The noncollision hypothesis of Aux. lemma 6, Remark 2.3 and Aux. lemma 7 (`c = k/2 − 2`): after amalgamating
coincident groups, every nonempty prefix sum on each side is at least `c`. A left prefix is the set of marks
strictly to the right of some `x < 0`; a right prefix is the set of marks at or to the left of some `x ≥ 0`. -/
def HasAdmissiblePartialSums (k : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) : Prop :=
  (∀ x : ℝ, x < 0 → (∃ i, x < xL i) →
      k / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => x < xL i), ρL i) ∧
    ∀ x : ℝ, 0 ≤ x → (∃ i, xR i ≤ x) → k / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ x), ρR i

theorem forceBoundaryData_of_neg {κ : ℝ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {x : ℝ} (hx : x < 0) :
    forceBoundaryData κ ρL ρR xL xR x =
      -sleLambda κ * (1 + ∑ i ∈ univ.filter (fun i => x < xL i), ρL i) := by
  simp only [forceBoundaryData, hx, ↓reduceIte, sleLambda]

theorem forceBoundaryData_of_nonneg {κ : ℝ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    forceBoundaryData κ ρL ρR xL xR x =
      sleLambda κ * (1 + ∑ i ∈ univ.filter (fun i => xR i ≤ x), ρR i) := by
  simp only [forceBoundaryData, not_lt.2 hx, ↓reduceIte, sleLambda]

/-- The left cumulative weight at `x < 0` is the conversion of the boundary height there. -/
theorem cumWeightLeft_forceBoundaryData (hk : 0 < k) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {x : ℝ} (hx : x < 0) :
    cumWeightLeft k (forceBoundaryData k ρL ρR xL xR x) =
      ∑ i ∈ univ.filter (fun i => x < xL i), ρL i := by
  rw [forceBoundaryData_of_neg ρL ρR xL xR hx, cumWeightLeft_spec hk]

/-- The right cumulative weight at `x ≥ 0` is the conversion of the boundary height there. -/
theorem cumWeightRight_forceBoundaryData (hk : 0 < k) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    cumWeightRight k (forceBoundaryData k ρL ρR xL xR x) =
      ∑ i ∈ univ.filter (fun i => xR i ≤ x), ρR i := by
  rw [forceBoundaryData_of_nonneg ρL ρR xL xR hx, cumWeightRight_spec hk]

/-- **Remark 4.1 in the half-plane chart.** The noncollision hypothesis holds exactly when the boundary data is at
most `−Λ + πX` left of `0` and at least `Λ − πX` right of `0`, at every point separated from the seed by a mark. -/
theorem hasAdmissiblePartialSums_iff (hk : 0 < k) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    HasAdmissiblePartialSums k ρL ρR xL xR ↔
      (∀ x : ℝ, x < 0 → (∃ i, x < xL i) →
          forceBoundaryData k ρL ρR xL xR x ≤ -sleLambda k + π * chiC k) ∧
        ∀ x : ℝ, 0 ≤ x → (∃ i, xR i ≤ x) →
          sleLambda k - π * chiC k ≤ forceBoundaryData k ρL ρR xL xR x := by
  simp only [HasAdmissiblePartialSums]
  refine and_congr (forall_congr' fun x => imp_congr_right fun hx => imp_congr_right fun _ => ?_)
    (forall_congr' fun x => imp_congr_right fun hx => imp_congr_right fun _ => ?_)
  · rw [← le_cumWeightLeft_iff hk, cumWeightLeft_forceBoundaryData hk ρL ρR xL xR hx]
  · rw [← le_cumWeightRight_iff hk, cumWeightRight_forceBoundaryData hk ρL ρR xL xR hx]

/-- A point of the open interval `(a, b)`, `a < b`, outside a finite set. -/
theorem exists_mem_Ioo_not_mem (E : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ y, a < y ∧ y < b ∧ y ∉ E := by
  obtain ⟨y, hy, hyE⟩ := (Set.Ioo_infinite hab).exists_notMem_finset E
  exact ⟨y, hy.1, hy.2, hyE⟩

/-- The left prefix sets are locally constant to the right: for `x < b` there is `x' ∈ (x, b)` outside a finite set
with the same left prefix. -/
theorem exists_left_prefix_eq (xL : Fin nL → ℝ) (E : Finset ℝ) {x b : ℝ} (hxb : x < b) :
    ∃ x', x < x' ∧ x' < b ∧ x' ∉ E ∧
      univ.filter (fun i => x' < xL i) = univ.filter (fun i => x < xL i) := by
  set P : Finset ℝ := insert b ((univ.filter (fun i => x < xL i)).image xL)
  have hPne : P.Nonempty := insert_nonempty _ _
  set m := P.min' hPne
  have hxm : x < m := by
    obtain ⟨p, hp, hpm⟩ := P.exists_min_image id hPne
    have : m = p := le_antisymm (P.min'_le p hp) (P.le_min' hPne p fun q hq => hpm q hq)
    rw [this]
    rcases Finset.mem_insert.1 hp with h | h
    · rw [h]; exact hxb
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
      exact (Finset.mem_filter.1 hi).2
  have hmb : m ≤ b := P.min'_le b (mem_insert_self _ _)
  obtain ⟨x', h1, h2, hE⟩ := exists_mem_Ioo_not_mem E hxm
  refine ⟨x', h1, h2.trans_le hmb, hE, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact h1.trans h
  · intro h
    have : m ≤ xL i := P.min'_le _ (mem_insert_of_mem (Finset.mem_image.2
      ⟨i, Finset.mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩))
    exact h2.trans_le this

/-- The right prefix sets are locally constant to the right. -/
theorem exists_right_prefix_eq (xR : Fin nR → ℝ) (E : Finset ℝ) (x : ℝ) :
    ∃ x', x < x' ∧ x' ∉ E ∧
      univ.filter (fun i => xR i ≤ x') = univ.filter (fun i => xR i ≤ x) := by
  set P : Finset ℝ := insert (x + 1) ((univ.filter (fun i => x < xR i)).image xR)
  have hPne : P.Nonempty := insert_nonempty _ _
  set m := P.min' hPne
  have hxm : x < m := by
    obtain ⟨p, hp, hpm⟩ := P.exists_min_image id hPne
    have : m = p := le_antisymm (P.min'_le p hp) (P.le_min' hPne p fun q hq => hpm q hq)
    rw [this]
    rcases Finset.mem_insert.1 hp with h | h
    · rw [h]; linarith
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
      exact (Finset.mem_filter.1 hi).2
  obtain ⟨x', h1, h2, hE⟩ := exists_mem_Ioo_not_mem E hxm
  refine ⟨x', h1, hE, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hcon
    have : m ≤ xR i := P.min'_le _ (mem_insert_of_mem (Finset.mem_image.2
      ⟨i, Finset.mem_filter.2 ⟨mem_univ _, not_le.1 hcon⟩, rfl⟩))
    linarith
  · intro h; exact h.trans h1.le

/-- **The values at finitely many points do not matter.** Remark 4.1's boundary condition, checked off a finite
set `E`, already gives the noncollision hypothesis. -/
theorem hasAdmissiblePartialSums_of_forall_not_mem (hk : 0 < k) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (E : Finset ℝ)
    (hL : ∀ x : ℝ, x < 0 → x ∉ E → (∃ i, x < xL i) →
      forceBoundaryData k ρL ρR xL xR x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 ≤ x → x ∉ E → (∃ i, xR i ≤ x) →
      sleLambda k - π * chiC k ≤ forceBoundaryData k ρL ρR xL xR x) :
    HasAdmissiblePartialSums k ρL ρR xL xR := by
  refine ⟨fun x hx ⟨i, hi⟩ => ?_, fun x hx ⟨i, hi⟩ => ?_⟩
  · obtain ⟨x', h1, h2, hE, hS⟩ := exists_left_prefix_eq xL E hx
    have hi' : x' < xL i := by
      have : i ∈ univ.filter (fun i => x' < xL i) := by
        rw [hS]; exact Finset.mem_filter.2 ⟨mem_univ _, hi⟩
      exact (Finset.mem_filter.1 this).2
    have := (le_cumWeightLeft_iff hk).2 (hL x' h2 hE ⟨i, hi'⟩)
    rwa [cumWeightLeft_forceBoundaryData hk ρL ρR xL xR h2, hS] at this
  · obtain ⟨x', h1, hE, hS⟩ := exists_right_prefix_eq xR E x
    have hx' : 0 ≤ x' := hx.trans h1.le
    have hi' : xR i ≤ x' := hi.trans h1.le
    have := (le_cumWeightRight_iff hk).2 (hR x' hx' hE ⟨i, hi'⟩)
    rwa [cumWeightRight_forceBoundaryData hk ρL ρR xL xR hx', hS] at this

/-! ### The continuation threshold at a first upper contact (Lemma 4.3) -/

/-- (HB1) in the chart `e^{πz} − 1`: the cumulative left weight of the transformed upper height `a + π X` is
`q₋ = k/2 − 3 − a/Λ`. -/
theorem cumWeightLeft_add_pi_mul_chiC (hk : 0 < k) (a : ℝ) :
    cumWeightLeft k (a + π * chiC k) = endChargeLeft k a := by
  have hl := sleLambda_ne_zero hk
  simp only [cumWeightLeft, endChargeLeft]
  rw [neg_add, add_div, neg_div (sleLambda k) (π * chiC k), pi_mul_chiC_div_sleLambda hk]
  ring

/-- (HB1) in the chart `1 − e^{−πz}`: the cumulative right weight of the transformed upper height `a − π X` is
`q₊ = k/2 − 3 + a/Λ`. -/
theorem cumWeightRight_sub_pi_mul_chiC (hk : 0 < k) (a : ℝ) :
    cumWeightRight k (a - π * chiC k) = endChargeRight k a := by
  rw [sub_pi_mul_chiC_eq_endChargeRight hk, mul_comm, cumWeightRight_spec hk]

/-- **Lemma 4.3, continuation toward the right end.** At a state where the driver collides exactly with the left marks
strictly right of a point `y < 0` of the image of the upper boundary, whose height is `a + π X`, and with no right
mark, the continuation threshold is not reached exactly when `a < Λ − π X`. -/
theorem not_thresholdCondition_iff_of_collide_left (hk : 0 < k) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w : ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {y a : ℝ}
    (hy : y < 0) (hcol : univ.filter (fun i => vL i = w) = univ.filter (fun i => y < xL i))
    (hR : ∀ i, vR i ≠ w) (hF : forceBoundaryData k ρL ρR xL xR y = a + π * chiC k) :
    ¬ ForceWord.ThresholdCondition ρL ρR w vL vR ↔ a < sleLambda k - π * chiC k := by
  have hsum : ∑ i ∈ univ.filter (fun i => vL i = w), ρL i = endChargeLeft k a := by
    rw [hcol, ← cumWeightLeft_forceBoundaryData hk ρL ρR xL xR hy, hF,
      cumWeightLeft_add_pi_mul_chiC hk]
  have hRe : univ.filter (fun i => vR i = w) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i _ => hR i
  rw [← neg_two_lt_rhoLeft_iff hk, ForceWord.ThresholdCondition, hsum, hRe, sum_empty]
  constructor
  · intro h; exact lt_of_not_ge fun h' => h (Or.inl h')
  · rintro h (h' | h')
    · linarith
    · norm_num at h'

/-- **Lemma 4.3, continuation toward the left end.** With the roles reversed (right marks at or left of `y ≥ 0`,
transformed height `a − π X`), the continuation threshold is not reached exactly when `a > −Λ + π X`. -/
theorem not_thresholdCondition_iff_of_collide_right (hk : 0 < k) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w : ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {y a : ℝ}
    (hy : 0 ≤ y) (hcol : univ.filter (fun i => vR i = w) = univ.filter (fun i => xR i ≤ y))
    (hL : ∀ i, vL i ≠ w) (hF : forceBoundaryData k ρL ρR xL xR y = a - π * chiC k) :
    ¬ ForceWord.ThresholdCondition ρL ρR w vL vR ↔ -sleLambda k + π * chiC k < a := by
  have hsum : ∑ i ∈ univ.filter (fun i => vR i = w), ρR i = endChargeRight k a := by
    rw [hcol, ← cumWeightRight_forceBoundaryData hk ρL ρR xL xR hy, hF,
      cumWeightRight_sub_pi_mul_chiC hk]
  have hLe : univ.filter (fun i => vL i = w) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i _ => hL i
  rw [← neg_two_lt_rhoRight_iff hk, ForceWord.ThresholdCondition, hsum, hLe, sum_empty]
  constructor
  · intro h; exact lt_of_not_ge fun h' => h (Or.inr h')
  · rintro h (h' | h')
    · norm_num at h'
    · linarith

end Sec4

end InteractingSLE
