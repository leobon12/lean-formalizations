/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7RetainedWord
import InteractingSLE.Spec.Restart.ChartMeasFlow
import InteractingSLE.Spec.Restart.ClockGeom
import InteractingSLE.Spec.Sec4.Aux25Term

/-!
# Lemma G7: retained data of two flow lines, and pathwise facts of the retained chart

Packet PROVE-G7.

* `exists_retData_of_isFlowLine`: for two flow lines and own cutoffs `(u, r)`, measurable retained data (`RetData`)
  whose good event contains almost surely `{u < ζ₁, r < ζ₂}` and whose paths agree with the flow lines on `[0, u]`,
  `[0, r]` (measurable versions; continuity, `ℍ̄`, real seeds, simplicity at the tip by Aux. lemma 25);
* `RetData.IsMeasGood.mem_E_of_ordinary`: an ordinary retained pair lies in the chart event;
* pathwise facts of a retained chart (`IsRetChart`): `ψ` maps `ℍ̄` into the closure of the active domain
  (`inv_mem_closure`); a real boundary point whose image is interior lies on the retained union
  (`inv_mem_prefixSet_of_real`); every point off the union is regular (`isChartRegularPoint_of_notMem`), so two
  points of `ℍ̄` with the same image off the union are equal (`eq_of_inv_eq_of_notMem`; the chart separates fresh
  points).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### Paths agreeing on the retained prefixes -/

theorem activeDomain_congr_Icc {α α' β β' : ℝ≥0 → ℂ} {a b : ℝ≥0} (h₁ : EqOn α α' (Icc 0 a))
    (h₂ : EqOn β β' (Icc 0 b)) : activeDomain α a β b = activeDomain α' a β' b := by
  unfold activeDomain; rw [h₁.image_eq, h₂.image_eq]

theorem prefixSet_congr_Icc {α α' β β' : ℝ≥0 → ℂ} {a b : ℝ≥0} (h₁ : EqOn α α' (Icc 0 a))
    (h₂ : EqOn β β' (Icc 0 b)) : prefixSet α a β b = prefixSet α' a β' b := by
  unfold prefixSet; rw [h₁.image_eq, h₂.image_eq]

theorem isChartRegularPoint_congr_Icc {α α' β β' : ℝ≥0 → ℂ} {a b : ℝ≥0} (h₁ : EqOn α α' (Icc 0 a))
    (h₂ : EqOn β β' (Icc 0 b)) (z : ℂ) : IsChartRegularPoint α a β b z ↔ IsChartRegularPoint α' a β' b z := by
  unfold IsChartRegularPoint
  rw [activeDomain_congr_Icc h₁ h₂, prefixSet_congr_Icc h₁ h₂]

/-! ### Retained data of two flow lines -/

section FlowLines

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Measurable retained data of two flow lines** at own cutoffs `(u, r)`. -/
theorem exists_retData_of_isFlowLine (hκ : 0 < κ) (hκ4 : κ < 4) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) (u r : ℝ≥0) :
    ∃ d : RetData Ω, d.IsMeasGood ∧ d.u = u ∧ d.r = r ∧
      ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ r, d.η₂ ω t = η₂ ω t := by
  obtain ⟨η₁', hm₁, ha₁⟩ := exists_measurable_version_of_isFlowLine hη₁
  obtain ⟨η₂', hm₂, ha₂⟩ := exists_measurable_version_of_isFlowLine hη₂
  set Good : Set Ω := {ω | (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω →
    ((∀ s ≤ u, η₁' ω s = η₁ ω s) ∧ (∀ t ≤ r, η₂' ω t = η₂ ω t)) ∧ IsRetGood (η₁' ω) u (η₂' ω) r} with hGood
  have haeGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [ha₁, ha₂, Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
      ae_mem_Hbar_of_isFlowLine hη₁, ae_mem_Hbar_of_isFlowLine hη₂, Supp10.ae_apply_zero_of_isFlowLine hη₁,
      Supp10.ae_apply_zero_of_isFlowLine hη₂, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂]
      with ω e₁ e₂ hc₁ hc₂ hH₁ hH₂ h0₁ h0₂ hi₂ hu hr
    have hle₁ : ∀ s ≤ u, (s : ℝ≥0∞) ≤ ζ₁ ω := fun s hs => (ENNReal.coe_le_coe.2 hs).trans hu.le
    have hle₂ : ∀ t ≤ r, (t : ℝ≥0∞) ≤ ζ₂ ω := fun t ht => (ENNReal.coe_le_coe.2 ht).trans hr.le
    have ag₁ : ∀ s ≤ u, η₁' ω s = η₁ ω s := fun s hs => e₁ s (hle₁ s hs)
    have ag₂ : ∀ t ≤ r, η₂' ω t = η₂ ω t := fun t ht => e₂ t (hle₂ t ht)
    refine ⟨⟨ag₁, ag₂⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hc₁.mono fun s hs => hle₁ s hs.2).congr fun s hs => ag₁ s hs.2
    · exact (hc₂.mono fun t ht => hle₂ t ht.2).congr fun t ht => ag₂ t ht.2
    · intro s hs; rw [ag₁ s hs.2]; exact hH₁ s (hle₁ s hs.2)
    · intro t ht; rw [ag₂ t ht.2]; exact hH₂ t (hle₂ t ht.2)
    · rw [ag₁ 0 zero_le, h0₁]; simp
    · rw [ag₂ 0 zero_le, h0₂]; simp
    · intro t ht he
      rw [ag₂ t ht.le, ag₂ r le_rfl] at he
      exact (ne_of_lt ht) (hi₂ (hle₂ t ht.le) (hle₂ r le_rfl) he)
  set G₀ : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG₀
  have hG₀sub : G₀ ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  have hG₀ae : ∀ᵐ ω ∂P, ω ∈ G₀ := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G₀} = toMeasurable P Goodᶜ := by ext ω; simp [hG₀]
    rw [this, measure_toMeasurable]
    exact ae_iff.1 haeGood
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  refine ⟨⟨G₀ ∩ {ω | (u : ℝ≥0∞) < ζ₁ ω} ∩ {ω | (r : ℝ≥0∞) < ζ₂ ω}, η₁', η₂', u, r⟩,
    ⟨?_, hm₁, hm₂, fun ω hω => (hG₀sub hω.1.1 hω.1.2 hω.2).2⟩, rfl, rfl, ?_⟩
  · exact ((measurableSet_toMeasurable P _).compl.inter (measurableSet_lt measurable_const hζ₁)).inter
      (measurableSet_lt measurable_const hζ₂)
  · filter_upwards [hG₀ae] with ω hω hu hr
    exact ⟨⟨⟨hω, hu⟩, hr⟩, (hG₀sub hω hu hr).1.1, (hG₀sub hω hu hr).1.2⟩

end FlowLines

/-! ### Ordinary retained pairs are in the chart event -/

namespace RetData

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- **An ordinary retained pair lies in the chart event** (for paths agreeing with `d`'s on the prefixes, at a point
of the good event). -/
theorem IsMeasGood.mem_E_of_ordinary (hd : d.IsMeasGood) {ω : Ω} (hG : ω ∈ d.G) {α β : ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : ℝ≥0∞} (ha₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (ha₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (hord : IsOrdinaryRetainedPair α ζ₁ d.u β ζ₂ d.r) : ω ∈ d.E := by
  have e₁ : EqOn (d.η₁ ω) α (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) β (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have htip : d.η₂ ω d.r = β d.r := ha₂ d.r le_rfl
  have hE₀ : ω ∈ d.E₀ := ⟨⟨hG, by rw [mem_ofPred_eq, htip]; exact hord.2.2.2.1⟩, by
    rw [mem_ofPred_eq, htip, e₁.image_eq]; exact hord.2.2.2.2.1⟩
  refine ⟨hE₀, ?_⟩
  show d.η₂ ω d.r ∈ closure (d.DOf d.E₀ ω)
  rw [hd.DOf_of_mem E₀_subset_G hE₀, activeDomain_congr_Icc e₁ e₂, htip]
  exact hord.2.2.2.2.2.2.2.1

end RetData

/-! ### Pathwise facts of a retained chart -/

section Pathwise

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

theorem isCompact_prefixSet' (hc₁ : ContinuousOn α (Icc 0 a)) (hc₂ : ContinuousOn β (Icc 0 b)) :
    IsCompact (prefixSet α a β b) :=
  (isCompact_Icc.image_of_continuousOn hc₁).union (isCompact_Icc.image_of_continuousOn hc₂)

/-- `ψ` maps `ℍ̄` into the closure of the active domain. -/
theorem inv_mem_closure (hC : IsRetChart α a β b φ ψ lift) (h0₂ : (β 0).im = 0) {w : ℂ} (hw : w ∈ Hbar) :
    ψ w ∈ closure (activeDomain α a β b) := by
  have hcw : ContinuousWithinAt ψ H w := (hC.continuousOn_inv w hw).mono QuantumZipper.H_subset_Hbar
  have hcl : w ∈ closure H := by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hw
  exact closure_mono (hC.bijOn h0₂).mapsTo.image_subset (hcw.mem_closure_image hcl)

/-- **A real boundary point with interior image lies on the retained union.** -/
theorem inv_mem_prefixSet_of_real (hC : IsRetChart α a β b φ ψ lift) (h0₂ : (β 0).im = 0)
    (hc₁ : ContinuousOn α (Icc 0 a)) (hc₂ : ContinuousOn β (Icc 0 b)) {y : ℝ} (hy : ψ y ∈ H) :
    ψ y ∈ prefixSet α a β b := by
  have hK := isCompact_prefixSet' hc₁ hc₂
  have hyH : ((y : ℂ)) ∈ Hbar := show (0 : ℝ) ≤ ((y : ℂ)).im by simp
  have hnot : ψ y ∉ activeDomain α a β b :=
    hC.inv_notMem h0₂ _ fun h => (lt_irrefl (0 : ℝ)) (by simpa using (show (0 : ℝ) < ((y : ℂ)).im from h))
  by_contra hyK
  have hcl := inv_mem_closure hC h0₂ hyH
  rw [activeDomain_eq hK.isClosed] at hcl hnot
  exact hnot (mem_H_diff_fillH_of_mem_closure hK.isClosed hy hyK hcl)

/-- **Every point off the retained union is regular.** -/
theorem isChartRegularPoint_of_notMem (hc₁ : ContinuousOn α (Icc 0 a)) (hc₂ : ContinuousOn β (Icc 0 b))
    (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0) {q : ℂ} (hq : q ∉ prefixSet α a β b) :
    IsChartRegularPoint α a β b q := by
  refine Or.inr (isUnboundedLinked_of_forall fun z hz _ => ?_)
  rcases hz with hz | hz
  · refine ⟨α '' Icc 0 a, subset_union_left, isPreconnected_Icc.image _ hc₁, hz,
      fun h => hq (Or.inl h), α 0, ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₁⟩
  · refine ⟨β '' Icc 0 b, subset_union_right, isPreconnected_Icc.image _ hc₂, hz,
      fun h => hq (Or.inr h), β 0, ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₂⟩

/-- **The chart separates points off the retained union**: two points of `ℍ̄` with the same image off the union
are equal (that image has a single prime end). -/
theorem eq_of_inv_eq_of_notMem (hC : IsRetChart α a β b φ ψ lift) (hc₁ : ContinuousOn α (Icc 0 a))
    (hc₂ : ContinuousOn β (Icc 0 b)) (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0) {w₁ w₂ : ℂ} (hw₁ : w₁ ∈ Hbar)
    (hw₂ : w₂ ∈ Hbar) (he : ψ w₁ = ψ w₂) (hK : ψ w₁ ∉ prefixSet α a β b) : w₁ = w₂ := by
  obtain ⟨w, -, -, -, hu⟩ := hC.exists_tendsto_of_regular h0₂ (inv_mem_closure hC h0₂ hw₁)
    (isChartRegularPoint_of_notMem hc₁ hc₂ h0₁ h0₂ hK)
  exact (hu w₁ hw₁ rfl).trans (hu w₂ hw₂ he.symm).symm

end Pathwise

end Supp7

end InteractingSLE
