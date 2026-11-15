/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR3RefDist
import InteractingSLE.Spec.Supplement.GW0BadGroup
import InteractingSLE.Spec.Supplement.LPAmalgamate

/-!
# `GW0BadGroup.BR3ReferenceStatement` from Theorem 1.3

Packet PROVE-T14-BR3. The named input `GW0BadGroup.BR3ReferenceStatement` of PROVE-T14-GW3 (BR3's bounded reference
in driver form, supplement pp. 608–609 and p. 617) is proved here from Theorem 1.3 (`Exist.Theorem13Statement`, the
frozen anchor's type).

**The reference right weights** (BR3's proof: "Preserve the original right seed `r₀ > −2` and put one right jump at a
deterministic `b > 0` […] so that the total right weight is `c`"; here `b` is the first original right mark strictly
right of `0`, which is below every positive original nonseed mark): the seed weights are kept, the first positive mark
carries `c − r₀`, `c = k/2 − 2`, every other positive mark `0` (`exists_refρR`). Every partial sum of the reference
right word over a set of marks closed to the left is `0`, `r₀` or `c`, so its right group ends are admissible.

**The proof** reflects the given evolution (the bad group becomes a right group), amalgamates coincident marks
(`IsIntegratedSLEEvolution.amalgamate`) and applies `BR3Ref.ae_event_dist`: almost surely the lifetime is finite, and
before it the far-left marks (beyond the bad group) and the right marks strictly right of `0` stay at a positive
distance from the driver. When the bad group sits at the seed the seed is a continuation threshold and the lifetime is
`0`.

## Main results

* `exists_refρR`: the reference right weights;
* **`br3ReferenceStatement_of_theorem13`**: `Exist.Theorem13Statement.{0} → GW0BadGroup.BR3ReferenceStatement`;
* `gw0SeparatedBadGroupStatement_of_theorem13`, **`gw0ForwardStatement_of_theorem13`**: Lemma GW0's third sentence and
  forward implication (PROVE-T14-GW3's reductions `…_of_br3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace BR3Ref

/-! ### The reference right weights -/

section Weights

variable {nR : ℕ} {xR : Fin nR → ℝ}

/-- A set of right marks closed to the left (in position). -/
def LeftClosed (xR : Fin nR → ℝ) (A : Finset (Fin nR)) : Prop :=
  ∀ i ∈ A, ∀ i', xR i' ≤ xR i → i' ∈ A

/-- **The reference right weights**: the seed weights are kept, and every partial sum over a set closed to the left
exceeds `−2`, and is at least `c` once the set contains a mark strictly right of `0`. -/
theorem exists_refρR (hmono : Monotone xR) (hR0 : ∀ i, 0 ≤ xR i) (ρR : Fin nR → ℝ) {c : ℝ} (hc : -2 < c)
    (hseed : -2 < ∑ i ∈ univ.filter (fun i => xR i = 0), ρR i) :
    ∃ ρR' : Fin nR → ℝ, (∀ i, xR i = 0 → ρR' i = ρR i) ∧
      (∀ A : Finset (Fin nR), LeftClosed xR A → -2 < ∑ i ∈ A, ρR' i) ∧
      (∀ A : Finset (Fin nR), LeftClosed xR A → (∃ i ∈ A, 0 < xR i) → c ≤ ∑ i ∈ A, ρR' i) := by
  classical
  set r₀ := ∑ i ∈ univ.filter (fun i => xR i = 0), ρR i with hr₀
  -- a closed-to-the-left set containing a mark contains every mark at `0`
  have hzeros : ∀ A : Finset (Fin nR), LeftClosed xR A → A.Nonempty → A.filter (fun i => xR i = 0) =
      univ.filter (fun i => xR i = 0) := by
    intro A hA ⟨i, hi⟩
    ext i'
    simp only [mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro h'
    exact hA i hi i' (by rw [h']; exact hR0 i)
  by_cases hpos : ∃ i, 0 < xR i
  · set S := univ.filter (fun i => 0 < xR i) with hS
    have hSne : S.Nonempty := by obtain ⟨i, hi⟩ := hpos; exact ⟨i, by simp [hS, hi]⟩
    set i₀ := S.min' hSne with hi₀
    have hi₀pos : 0 < xR i₀ := by have := S.min'_mem hSne; simpa [hS] using this
    refine ⟨fun i => if xR i = 0 then ρR i else if i = i₀ then c - r₀ else 0, fun i hi => by simp [hi], ?_⟩
    have hsum : ∀ A : Finset (Fin nR), ∑ i ∈ A, (if xR i = 0 then ρR i else if i = i₀ then c - r₀ else 0) =
        (∑ i ∈ A.filter (fun i => xR i = 0), ρR i) + (if i₀ ∈ A then c - r₀ else 0) := by
      intro A
      rw [Finset.sum_ite, Finset.sum_ite_eq']
      congr 1
      simp only [mem_filter, hi₀pos.ne', not_false_eq_true, and_true]
    have hmain : ∀ A : Finset (Fin nR), LeftClosed xR A → (∃ i ∈ A, 0 < xR i) →
        ∑ i ∈ A, (if xR i = 0 then ρR i else if i = i₀ then c - r₀ else 0) = c := by
      intro A hA ⟨i, hiA, hi⟩
      have hi₀A : i₀ ∈ A := hA i hiA i₀ (hmono (S.min'_le i (by simp [hS, hi])))
      rw [hsum, hzeros A hA ⟨i, hiA⟩]
      simp only [hi₀A, ite_true]
      ring
    refine ⟨fun A hA => ?_, fun A hA h => (hmain A hA h).ge⟩
    by_cases h : ∃ i ∈ A, 0 < xR i
    · rw [hmain A hA h]; exact hc
    · push Not at h
      have hi₀A : i₀ ∉ A := fun hm => absurd (h i₀ hm) (not_le.2 hi₀pos)
      rw [hsum]
      simp only [hi₀A, ite_false, add_zero]
      rcases A.eq_empty_or_nonempty with he | hne
      · rw [he]; simp
      · rw [hzeros A hA hne]; exact hseed
  · push Not at hpos
    refine ⟨ρR, fun _ _ => rfl, fun A hA => ?_, fun A _ ⟨i, _, hi⟩ => absurd (hpos i) (not_le.2 hi)⟩
    rcases A.eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · have : A = A.filter (fun i => xR i = 0) := by
        ext i; simp only [mem_filter, iff_self_and]
        exact fun _ => le_antisymm (hpos i) (hR0 i)
      rw [this, hzeros A hA hne]; exact hseed

end Weights

/-! ### Prefix sums of amalgamated weights -/

section Classes

variable {n m : ℕ}

/-- Prefix sums of class weights are sums over the marks of the first classes. -/
theorem pre_amWeight (cls : Fin n → Fin m) (ρ : Fin n → ℝ) (v : ℕ) :
    pre (LP.amWeight cls ρ) v = ∑ i ∈ univ.filter (fun i => ((cls i : Fin m) : ℕ) < v), ρ i := by
  unfold pre LP.amWeight
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun i => ((cls i : Fin m) : ℕ) < v))
    (t := univ.filter (fun c : Fin m => (c : ℕ) < v)) (g := cls) (fun i hi => by simpa using hi)]
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_filter, Finset.mem_univ, true_and] at hc ⊢
  constructor
  · intro h; exact ⟨h ▸ hc, h⟩
  · exact fun h => h.2

theorem amCls_le_amCls_iff (x : Fin n → ℝ) (i i' : Fin n) : LP.amCls x i ≤ LP.amCls x i' ↔ x i ≤ x i' := by
  rw [← (LP.strictMono_amPos x).le_iff_le, LP.amPos_amCls, LP.amPos_amCls]

theorem amCls_lt_amCls_iff (x : Fin n → ℝ) (i i' : Fin n) : LP.amCls x i < LP.amCls x i' ↔ x i < x i' := by
  rw [← (LP.strictMono_amPos x).lt_iff_lt, LP.amPos_amCls, LP.amPos_amCls]

theorem amClsL_le_amClsL_iff (x : Fin n → ℝ) (i i' : Fin n) : LP.amClsL x i ≤ LP.amClsL x i' ↔ x i' ≤ x i := by
  unfold LP.amClsL
  rw [Fin.rev_le_rev, amCls_le_amCls_iff]

end Classes

/-! ### The bounded reference -/

open GW0BadGroup in
/-- **BR3's bounded reference in driver form (`GW0BadGroup.BR3ReferenceStatement`), from Theorem 1.3.** -/
theorem br3ReferenceStatement_of_theorem13 (hT13 : Exist.Theorem13Statement.{0}) : BR3ReferenceStatement := by
  intro k hk nL nR xL xR ρL ρR j hF hsep hj hL hadm hR0
  obtain ⟨hxLa, hL0, hxRm, hR0'⟩ := hF
  have hc : -2 < k / 2 - 2 := by linarith
  obtain ⟨ρR', hseed', hP2, hP3⟩ := exists_refρR hxRm hR0' ρR hc hR0
  refine ⟨ρR', hseed', fun m hm => hP2 _ fun i hi i' hi' => ?_, ?_⟩
  · simp only [mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_contra h
    rw [not_le] at h
    have h1 := hm i' h
    have h2 := hxRm hi
    linarith
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  suffices hae : ∀ᵐ ω ∂P, ζ ω < ⊤ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      (∀ i, j < i → δ ≤ W t ω - VL i t ω) ∧ (∀ i, 0 < xR i → δ ≤ VR i t ω - W t ω) by
    intro h0
    have h1 : P univ ≤ P {ω | ζ ω < ⊤ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
        (∀ i, j < i → δ ≤ W t ω - VL i t ω) ∧ (∀ i, 0 < xR i → δ ≤ VR i t ω - W t ω)} :=
      measure_mono_ae (hae.mono fun ω h _ => h)
    rw [measure_univ, h0] at h1
    exact absurd h1 (by norm_num)
  by_cases hj0 : xL j = 0
  · -- the bad group sits at the seed: a continuation threshold at time `0`
    filter_upwards [hE.ae_isIntegratedSLEPath] with ω hp
    have hζ0 : ζ ω = 0 := by
      by_contra hne
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
      apply hp.isForcePath.not_threshold h0
      left
      have hset : univ.filter (fun i => VL i 0 ω = W 0 ω) = univ.filter (· ≤ j) := by
        ext i
        simp only [mem_filter, Finset.mem_univ, true_and, hp.isForcePath.vL_zero, hp.isForcePath.w_zero]
        constructor
        · intro h
          by_contra hij
          rw [not_le] at hij
          have := hj i hij
          linarith
        · intro h
          exact le_antisymm (hL0 i) (hj0 ▸ hxLa h)
      rw [hset]
      refine le_of_eq_of_le (Finset.sum_congr rfl fun i hi => ?_) hL
      exact refρL_of_le ρL (mem_filter.1 hi).2
    exact ⟨by rw [hζ0]; exact ENNReal.zero_lt_top, 1, one_pos, fun t ht => absurd ht (by rw [hζ0]; simp)⟩
  have hj0' : xL j < 0 := lt_of_le_of_ne (hL0 j) hj0
  -- reflect and amalgamate
  have hFr : IsOrderedForceWord (-xR) (-xL) :=
    ⟨fun a b h => neg_le_neg (hxRm h), fun i => by simp [hR0' i], fun a b h => neg_le_neg (hxLa h),
      fun i => by simp [hL0 i]⟩
  have hEa := hE.reflect.amalgamate hFr
  set J := LP.amCls (-xL) j with hJdef
  have hrefle : ∀ m, m ≤ j → refρL j ρL m = ρL m := fun m hm => refρL_of_le ρL hm
  -- the hypotheses of the distinct form
  have hsepa : ∀ c c', LP.amXL (-xR) c < LP.amPos (-xL) c' := fun c c' => by
    rw [← LP.apply_amRepL, ← LP.apply_amRep]
    have := hsep (LP.amRep (-xL) c') (LP.amRepL (-xR) c)
    simp only [Pi.neg_apply]
    linarith
  have hJ0 : 0 < LP.amPos (-xL) J := by rw [hJdef, LP.amPos_amCls]; simp; linarith
  have hclosedL : ∀ v : ℕ, LeftClosed xR (univ.filter fun i => ((LP.amClsL (-xR) i : Fin _) : ℕ) < v) := by
    intro v i hi i' hi'
    simp only [mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have := (amClsL_le_amClsL_iff (-xR) i' i).2 (by simp; exact hi')
    exact lt_of_le_of_lt (Fin.le_def.1 this) hi
  have hLpre : ∀ v ≤ (Finset.univ.image (-xR)).card, -2 < pre (LP.amWeight (LP.amClsL (-xR)) ρR') v := fun v _ => by
    rw [pre_amWeight]; exact hP2 _ (hclosedL v)
  have hLc : ∀ c, LP.amXL (-xR) c < 0 → k / 2 - 2 ≤ pre (LP.amWeight (LP.amClsL (-xR)) ρR') (c + 1) := by
    intro c hcneg
    rw [pre_amWeight]
    refine hP3 _ (hclosedL _) ⟨LP.amRepL (-xR) c, ?_, ?_⟩
    · simp [LP.amClsL_amRepL]
    · have := LP.apply_amRepL (-xR) c
      simp only [Pi.neg_apply] at this
      linarith
  have hRpre : ∀ v ≤ (J : ℕ), -2 < pre (LP.amWeight (LP.amCls (-xL)) (refρL j ρL)) v := by
    intro v hv
    rw [pre_amWeight]
    set A := univ.filter fun i => ((LP.amCls (-xL) i : Fin _) : ℕ) < v with hA
    rcases A.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; norm_num
    set m := A.max' hne with hm
    have hmA : m ∈ A := A.max'_mem hne
    have hmv : ((LP.amCls (-xL) m : Fin _) : ℕ) < v := (mem_filter.1 hmA).2
    have hAeq : A = univ.filter (· ≤ m) := by
      ext i
      have hR : i ∈ univ.filter (· ≤ m) ↔ i ≤ m := by simp
      rw [hR]
      constructor
      · intro hi; exact A.le_max' i hi
      · intro hi
        have := (amCls_le_amCls_iff (-xL) i m).2 (by simp; exact hxLa hi)
        have hiA : i ∈ univ.filter fun i => ((LP.amCls (-xL) i : Fin _) : ℕ) < v := by
          simp only [mem_filter, Finset.mem_univ, true_and]
          exact lt_of_le_of_lt (Fin.le_def.1 this) hmv
        exact hiA
    have hmj : xL j < xL m := by
      have : LP.amCls (-xL) m < J := Fin.lt_def.2 (lt_of_lt_of_le hmv hv)
      have := (amCls_lt_amCls_iff (-xL) m j).1 this
      simp only [Pi.neg_apply] at this
      linarith
    have hmle : m ≤ j := by
      by_contra h; rw [not_le] at h
      have := hxLa h.le
      linarith
    have hend : ∀ i, m < i → xL i < xL m := by
      intro i hi
      have hiA : i ∉ A := fun h => absurd (A.le_max' i h) (not_le.2 hi)
      simp only [hA, mem_filter, Finset.mem_univ, true_and, not_lt] at hiA
      have : LP.amCls (-xL) m < LP.amCls (-xL) i := Fin.lt_def.2 (lt_of_lt_of_le hmv hiA)
      have := (amCls_lt_amCls_iff (-xL) m i).1 this
      simp only [Pi.neg_apply] at this
      linarith
    rw [hAeq, Finset.sum_congr rfl fun i hi => hrefle i ((mem_filter.1 hi).2.trans hmle)]
    exact hadm m hend hmj
  have hRJ : pre (LP.amWeight (LP.amCls (-xL)) (refρL j ρL)) (J + 1) ≤ -2 := by
    rw [pre_amWeight]
    have hAeq : (univ.filter fun i => ((LP.amCls (-xL) i : Fin _) : ℕ) < (J : ℕ) + 1) = univ.filter (· ≤ j) := by
      ext i
      simp only [mem_filter, Finset.mem_univ, true_and]
      rw [Nat.lt_succ_iff, ← Fin.le_def, hJdef, amCls_le_amCls_iff]
      simp only [Pi.neg_apply, neg_le_neg_iff]
      constructor
      · intro h
        by_contra hij; rw [not_le] at hij
        have := hj i hij
        linarith
      · exact fun h => hxLa h
    rw [hAeq, Finset.sum_congr rfl fun i hi => hrefle i (mem_filter.1 hi).2]
    exact hL
  have hRfar : ∀ c, J < c → LP.amWeight (LP.amCls (-xL)) (refρL j ρL) c = 0 := by
    intro c hc
    refine Finset.sum_eq_zero fun i hi => refρL_of_lt ρL ?_
    have hci := (mem_filter.1 hi).2
    rw [← hci, hJdef, amCls_lt_amCls_iff] at hc
    simp only [Pi.neg_apply, neg_lt_neg_iff] at hc
    by_contra hij; rw [not_lt] at hij
    have := hxLa hij
    linarith
  have hmain := ae_event_dist hT13 hk (LP.isDistinctForceWord_amalgamate hFr) hsepa J hJ0 hLpre hLc hRpre hRJ hRfar hEa
  filter_upwards [hmain, hE.ae_isIntegratedSLEPath] with ω ⟨hζ, δ, hδ, hb⟩ hp
  refine ⟨hζ, δ, hδ, fun t ht => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩
  · have hci : J < LP.amCls (-xL) i := by
      rw [hJdef, amCls_lt_amCls_iff]
      simp only [Pi.neg_apply, neg_lt_neg_iff]
      exact hj i hi
    have h1 := (hb t ht).1 _ hci
    have heq : VL (LP.amRep (-xL) (LP.amCls (-xL) i)) t ω = VL i t ω := by
      refine hp.vL_eq_of_xL_eq ht ?_
      have := LP.apply_amRep (-xL) (LP.amCls (-xL) i)
      rw [LP.amPos_amCls] at this
      simpa using this
    simp only [Pi.neg_apply] at h1
    linarith
  · have hci : LP.amXL (-xR) (LP.amClsL (-xR) i) < 0 := by
      rw [LP.amXL_amClsL]; simp only [Pi.neg_apply]; linarith
    have h1 := (hb t ht).2 _ hci
    have heq : VR (LP.amRepL (-xR) (LP.amClsL (-xR) i)) t ω = VR i t ω := by
      refine hp.vR_eq_of_xR_eq ht ?_
      have := LP.apply_amRepL (-xR) (LP.amClsL (-xR) i)
      rw [LP.amXL_amClsL] at this
      simpa using this
    simp only [Pi.neg_apply] at h1
    linarith

universe u

/-- **Lemma GW0, third sentence** (a first bad separated group is reached at a finite threshold with positive
probability), from Theorem 1.3: PROVE-T14-GW3's reduction with its input discharged. -/
theorem gw0SeparatedBadGroupStatement_of_theorem13 (hT13 : Exist.Theorem13Statement.{0}) :
    GW0.GW0SeparatedBadGroupStatement.{u} :=
  GW0BadGroup.gw0SeparatedBadGroupStatement_of_br3 (br3ReferenceStatement_of_theorem13 hT13)

/-- **Lemma GW0, forward implication**, from Theorem 1.3. -/
theorem gw0ForwardStatement_of_theorem13 (hT13 : Exist.Theorem13Statement.{0}) : GW0.GW0ForwardStatement.{u} :=
  GW0BadGroup.gw0ForwardStatement_of_br3 (br3ReferenceStatement_of_theorem13 hT13)

end BR3Ref

end Theorem14

end InteractingSLE
