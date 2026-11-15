/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordInStrip
import InteractingSLE.Spec.Sec5.StripRevVisitLaw
import InteractingSLE.Spec.Sec5.Prop411QOrder

/-!
# Pocket-wall visits from rational first contacts

PROVE-POCKET-WORDIN continuation. The landed Q-chart first-contact theorem
already proves the density argument. This file adapts it to the pocket's
nonnegative wall clock and the counterflow's real clock.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketWordIn

open WangWu Lemma71I PocketJordan

/-- Rational first contacts give the pocket wall's weak reverse visit order.
The density argument is `Prop411Q.exists_eq_of_isFirstHitQ`. -/
theorem isWallReverseVisit_of_firstHitQ {R : ℝ≥0 → ℂ} {η : ℝ → ℂ}
    (hR : IsSimpleProper R) (hη : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hfirst : ∀ q : ℚ, 0 < q → Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath R) η q) :
    IsWallReverseVisit R η := by
  rintro t a b ha hab ⟨v, hv, he⟩
  rcases hab.eq_or_lt with rfl | hab
  · exact ⟨v, hv, he⟩
  have hRa : R a ∈ H := hR.2.2.2.1 a ha
  have hv0 : 0 < v := by
    refine lt_of_le_of_ne hv.1 ?_
    intro hvz
    rw [← hvz, hη0] at he
    exact (WangWu.ne_zero_of_mem_H (negInv_mem_H hRa)) he.symm
  have he' : Lemma71I.realPath R a = negInv (η v) := by
    rw [Lemma71I.realPath_coe, he, negInv_negInv]
  obtain ⟨w, hw, hew⟩ := Sec5.Prop411Q.exists_eq_of_isFirstHitQ hR.isProperArc
    hη hη0 hfirst (show 0 < (a : ℝ) from ha) hv0 he' (show (a : ℝ) < b from hab)
  refine ⟨w, ⟨hw.1.le, hw.2.trans hv.2⟩, ?_⟩
  have hew' : η w = negInv (Lemma71I.realPath R b) := (Sec5.Prop411Q.negInv_eq_iff.1 hew.symm)
  simpa only [Lemma71I.realPath_coe] using hew'

/-- Every positive-time wall point is visited: choose a smaller positive rational
wall time, use its first contact, and apply the proved reverse visit order. -/
theorem isWallVisited_of_firstHitQ {R : ℝ≥0 → ℂ} {η : ℝ → ℂ}
    (hR : IsSimpleProper R) (hη : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hfirst : ∀ q : ℚ, 0 < q → Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath R) η q) :
    IsWallVisited R η := by
  intro a ha
  obtain ⟨q, hq, hqa⟩ := exists_rat_btwn (show (0 : ℝ) < a from ha)
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  obtain ⟨v, hv, he, -⟩ := hfirst q hq'
  have hqNN : ((q : ℝ).toNNReal : ℝ) = q := Real.coe_toNNReal _ hq.le
  have hqpos : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 hq
  have hqle : (q : ℝ).toNNReal ≤ a := by
    exact_mod_cast (show (((q : ℝ).toNNReal : ℝ)) ≤ a by rw [hqNN]; exact hqa.le)
  have he' : negInv (R (q : ℝ).toNNReal) ∈ η '' Icc 0 v :=
    ⟨v, ⟨hv.le, le_rfl⟩, Sec5.Prop411Q.negInv_eq_iff.1 he⟩
  exact ⟨v, isWallReverseVisit_of_firstHitQ hR hη hη0 hfirst v _ a hqpos hqle he'⟩

/-- Countably many rational first-contact events give both wall laws on one
conull event, for the actual supplied versions. -/
theorem ae_wall_visits_of_firstHitQ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {R : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω))
    (hη : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hη0 : ∀ ω, η ω 0 = 0)
    (hfirst : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (R ω)) (η ω) q) :
    ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) := by
  have hfirst' : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q →
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (R ω)) (η ω) q := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < q
    · exact (hfirst q hq).mono fun _ hf _ => hf
    · exact Eventually.of_forall fun _ hq' => (hq hq').elim
  filter_upwards [hR, hfirst'] with ω hr hf
  exact ⟨isWallReverseVisit_of_firstHitQ hr (hη ω) (hη0 ω) hf,
    isWallVisited_of_firstHitQ hr (hη ω) (hη0 ω) hf⟩

end InteractingSLE.Sec7.PocketWordIn
