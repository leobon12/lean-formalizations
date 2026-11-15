/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoLimits

/-!
# Rational restart barriers and western excursion endpoints

The rational hypotheses of `FwdNoWrapQStatement` control every finite excursion
interval and every infinite tail. Combining them with the prime-end limits
proves that each terminal chart coordinate is strictly negative, provided that
the finite physical endpoint is not the counterflow tip. The no-contact case
then follows from the landed crosscut separation theorem with no extra limit
hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

variable {w : ℝ → ℝ} {η β : ℝ → ℂ} {s a b : ℝ}

/-- A rational restart in a nonempty excursion controls its finite endpoint.
The source filter is the ordinary left-neighborhood filter. -/
theorem not_hitsEastPartAlong_left_of_rational
    (hbar : ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η)
    (ha : 0 ≤ a) (hab : a < b)
    (hD : ∀ t ∈ Ioo a b, η t ∈ H \ cfHullQ w s) :
    ¬ HitsEastPartAlong w s η (𝓝[<] b) := by
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  have hq0 : (0 : ℝ) < q := ha.trans_lt haq
  have hq0' : (0 : ℚ) ≤ q := by exact_mod_cast hq0.le
  have hqD : 0 < (q : ℝ) → η q ∈ H \ cfHullQ w s :=
    fun _ => hD q ⟨haq, hqb⟩
  have h := (hbar q hq0' hqD).1 b hqb
    (fun t ht => hD t ⟨haq.trans ht.1, ht.2⟩)
  rwa [nhdsWithin_Ioo_eq_nhdsLT hqb] at h

/-- A rational restart in an infinite tail controls its terminal prime end. -/
theorem not_hitsEastPartAlong_atTop_of_rational
    (hbar : ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η)
    (ha : 0 ≤ a) (hD : ∀ t ∈ Ioi a, η t ∈ H \ cfHullQ w s) :
    ¬ HitsEastPartAlong w s η atTop := by
  obtain ⟨q, haq, _⟩ := exists_rat_btwn (lt_add_one a)
  have hq0 : (0 : ℝ) < q := ha.trans_lt haq
  have hq0' : (0 : ℚ) ≤ q := by exact_mod_cast hq0.le
  exact (hbar q hq0' (fun _ => hD q haq)).2
    (fun t ht => hD t (haq.trans ht))

/-- Rational restarts suffice at every nonnegative real restart, including
times at which the path itself is on the hull. -/
theorem firstContactNotEast_of_rational
    (hbar : ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η)
    {t : ℝ} (ht : 0 ≤ t) : FirstContactNotEast w s t η := by
  intro _
  refine ⟨fun u htu hD => ?_,
    fun hD => not_hitsEastPartAlong_atTop_of_rational hbar ht hD⟩
  simpa only [nhdsWithin_Ioo_eq_nhdsLT htu] using
    not_hitsEastPartAlong_left_of_rational hbar ht htu hD

/-- With eventual complementary-domain membership a positive real chart limit
is an eastern approach in the precise sense of `HitsEastPartAlong`. -/
theorem hitsEastPartAlong_of_tendsto {l : Filter ℝ} [l.NeBot] {x : ℝ}
    (hx : 0 < x) (hD : ∀ᶠ t in l, η t ∈ H \ cfHullQ w s)
    (hlim : Tendsto (fun t => revChart w s (η t)) l (𝓝 (x : ℂ))) :
    HitsEastPartAlong w s η l := by
  refine ⟨x, hx, ?_⟩
  have heq : l ⊓ 𝓟 {t | η t ∈ H \ cfHullQ w s} = l :=
    inf_eq_left.2 (le_principal_iff.2 hD)
  rw [heq]
  exact hlim.mapClusterPt

/-- Every finite excursion ending away from the counterflow tip lands at a
strictly negative real chart coordinate. -/
theorem exists_neg_tendsto_revChart_left (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (ha : 0 < a) (hab : a < b)
    (hD : ∀ t ∈ Ico a b, η t ∈ H \ cfHullQ w s)
    (hb : η b ∉ H \ cfHullQ w s) (htip : η b ≠ negInv (β s))
    (hbar : ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η) :
    ∃ x : ℝ, x < 0 ∧
      Tendsto (fun t => revChart w s (η t)) (𝓝[<] b) (𝓝 (x : ℂ)) := by
  obtain ⟨x, hx0, hx⟩ := exists_tendsto_revChart_left hη hβ hw hw0 hs ha hab hD hb htip
  refine ⟨x, lt_of_le_of_ne (not_lt.1 fun hxpos => ?_) hx0, hx⟩
  exact not_hitsEastPartAlong_left_of_rational hbar ha.le hab
    (fun t ht => hD t ⟨ht.1.le, ht.2⟩)
    (hitsEastPartAlong_of_tendsto hxpos
      (Filter.mem_of_superset (Ico_mem_nhdsLT hab) hD) hx)

/-- Every infinite excursion tail lands at a strictly negative chart coordinate. -/
theorem exists_neg_tendsto_revChart_atTop (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hβs : β s ≠ 0) (ha : 0 ≤ a)
    (hD : ∀ t ∈ Ioi a, η t ∈ H \ cfHullQ w s)
    (hbar : ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η) :
    ∃ x : ℝ, x < 0 ∧
      Tendsto (fun t => revChart w s (η t)) atTop (𝓝 (x : ℂ)) := by
  obtain ⟨x, hx0, hx⟩ := exists_tendsto_revChart_atTop hη hβ hw hw0 hs hβs ha hD
  refine ⟨x, lt_of_le_of_ne (not_lt.1 fun hxpos => ?_) hx0, hx⟩
  exact not_hitsEastPartAlong_atTop_of_rational hbar ha hD
    (hitsEastPartAlong_of_tendsto hxpos
      ((eventually_gt_atTop a).mono fun t ht => hD t ht) hx)

/-- The full no-wrap hypotheses prove the no-contact case without a separate
assumption on the terminal chart limit. -/
theorem negInv_notMem_leftSideOf_of_noContact_of_rational (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hβs : β s ≠ 0)
    (hpre : ∀ t, 0 < t → η t ∉ cfHullQ w s)
    (hbar : ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η) :
    negInv (β s) ∉ leftSideOf (arcRange η) := by
  obtain ⟨x, hx, hlim⟩ := exists_neg_tendsto_revChart_atTop hη hβ hw hw0 hs hβs
    (a := 0) le_rfl (fun t ht => ⟨hη.mem_H t ht, hpre t ht⟩) hbar
  exact negInv_notMem_leftSideOf_of_noContact hη hβ hw hw0 hs hx hpre hlim

end InteractingSLE.Sec5.Prop51HTopo
