/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofHist

/-!
# Stop-line chart measurability for the physical information

Packet PROVE-RETPLUMB. A good event can be chosen inside the event that both
prefixes are alive. Its null completion is then a retained-history event. Stopped
capped versions reconstruct the chart from that history; their null modifications
are handled inside `retSigma76`, without observing the future of either curve.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open Supp7 Sec7 Sec7.Lemma76F LocalSets

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}

/-- Null modifications of ambient measurable events remain physical events. -/
theorem measurableSet_retSigma76_congr {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] B) (he : A =ᵐ[P] B) :
    MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] A :=
  ⟨hA, measurableSet_aeSigma_of_ae_eq he hB.2⟩

/-- Null modifications of ambient measurable observables remain physical observables. -/
theorem measurable_retSigma76_congr {Y : Type*} [MeasurableSpace Y] {f g : Ω → Y}
    (hf : Measurable f) (hg : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] g)
    (he : f =ᵐ[P] g) : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] f := by
  intro B hB
  apply measurableSet_retSigma76_congr (hf hB) (hg hB)
  filter_upwards [he] with ω heω
  simp only [mem_preimage, heω]

/-- The good event may be chosen inside the live event, measurably for the
completed retained histories. -/
theorem exists_retG_with_live [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hκ : 0 < κ) (hκ4 : κ < 4)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {η₁' η₂' : Ω → ℝ≥0 → ℂ}
    (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (hm₂ : ∀ t, Measurable fun ω => η₂' ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (u r : ℝ≥0) :
    ∃ G : Set Ω, (⟨G, η₁', η₂', u, r⟩ : RetData Ω).IsMeasGood ∧
      G ⊆ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω} ∧
      MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] G ∧
      ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → ω ∈ G := by
  obtain ⟨G, hd, hG⟩ := exists_retG_of_version hκ hκ4 hη₁ hη₂ hm₁ hm₂ ha₁ ha₂ u r
  have hLive := measurableSet_retLive P η₁ η₂ ζ₁ ζ₂
    (measurable_lifetime_of_isFlowLine hη₁) (measurable_lifetime_of_isFlowLine hη₂) u r
  have hmLive := retSigma76_le P η₁ η₂ ζ₁ ζ₂ u r _ hLive
  refine ⟨G ∩ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω},
    ⟨hd.measurableSet_G.inter hmLive, hm₁, hm₂, fun ω hω => hd.good ω hω.1⟩,
    inter_subset_right, ?_, ?_⟩
  · apply measurableSet_retSigma76_congr (hd.measurableSet_G.inter hmLive) hLive
    filter_upwards [hG] with ω hω
    exact propext ⟨fun h => h.2, fun h => ⟨hω h.1 h.2, h⟩⟩
  · filter_upwards [hG] with ω hω hu hr using ⟨hω hu hr, hu, hr⟩

/-- Choose the locally measurable good events simultaneously as a family in the
second cutoff; each line has exactly the source's available prefixes. -/
theorem exists_retG_family_with_live [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hκ : 0 < κ) (hκ4 : κ < 4)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {η₁' η₂' : Ω → ℝ≥0 → ℂ}
    (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (hm₂ : ∀ t, Measurable fun ω => η₂' ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (u : ℝ≥0) :
    ∃ G : ℝ≥0 → Set Ω, ∀ r,
      (retFam G η₁' η₂' u r).IsMeasGood ∧
      G r ⊆ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω} ∧
      MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] (G r) ∧
      ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → ω ∈ G r := by
  classical
  choose G hG using fun r : ℝ≥0 =>
    exists_retG_with_live hκ hκ4 hη₁ hη₂ hm₁ hm₂ ha₁ ha₂ u r
  exact ⟨G, hG⟩

variable [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The stop-line chart is measurable for the physical information if its good
event is supported on the live event. All chart coordinates are obtained from
the stopped histories, including on null modifications. -/
theorem chart_measurability_retSigma76 {d : RetData Ω} (hd : d.IsMeasGood)
    (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂)
    (hGsub : d.G ⊆ {ω | (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω})
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω →
      ω ∈ d.G ∧ (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧
        ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t)
    (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t)
    {x₁ x₂ : ℝ} (h0₁ : ∀ ω, ηc₁ ω 0 = x₁) (h0₂ : ∀ ω, ηc₂ ω 0 = x₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) t))
    (ha₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) t)) :
    (∀ z, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r]
      {ω | z ∈ (d.chart ω).dom}) ∧
    (∀ z, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r]
      ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => (d.chart ω).1 z)) ∧
    (∀ z, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r]
      ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => (d.chart ω).2.2 z)) := by
  classical
  set R := retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r with hR
  let _ : MeasurableSpace Ω := mΩ
  set F := cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR d.u d.r))
    (fun ω => cutLife (ζ₂ ω) (capR d.u d.r)) d.u d.r with hF
  have hFR : Measurable[R] F := by
    apply measurable_retSigma76_of_ae_eq
      (measurable_cstHist hm₁ hm₂ ((measurable_cutLife _).comp hζ₁)
        ((measurable_cutLife _).comp hζ₂) d.u d.r)
      (comap_measurable (retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r))
    filter_upwards [ha₁, ha₂] with ω e₁ e₂
    have a₁ : ηc₁ ω = cappedPath η₁ ζ₁ (capR d.u d.r) ω := funext e₁
    have a₂ : ηc₂ ω = cappedPath η₂ ζ₂ (capR d.u d.r) ω := funext e₂
    simp only [retHist76, cstHist, a₁, a₂, Function.comp_apply]
  set d₀ := stopRet ηc₁ ηc₂ d.u d.r with hd₀def
  have hd₀ : @RetData.IsMeasGood Ω R d₀ :=
    isMeasGood_stopRet hFR.comap_le hc₁ hc₂ h0₁ h0₂
  set L := {ω | (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω} with hL
  have hLR : MeasurableSet[R] L := measurableSet_retLive P η₁ η₂ ζ₁ ζ₂ hζ₁ hζ₂ d.u d.r
  let d' : RetData Ω := ⟨d₀.G ∩ L, d₀.η₁, d₀.η₂, d.u, d.r⟩
  have hd' : @RetData.IsMeasGood Ω R d' :=
    @RetData.IsMeasGood.mk Ω R d'
      ((@RetData.IsMeasGood.measurableSet_G Ω R d₀ hd₀).inter hLR)
      (@RetData.IsMeasGood.meas₁ Ω R d₀ hd₀)
      (@RetData.IsMeasGood.meas₂ Ω R d₀ hd₀)
      (fun ω hω => @RetData.IsMeasGood.good Ω R d₀ hd₀ ω hω.1)
  have heq : ∀ᵐ ω ∂P, d'.chart ω = d.chart ω := by
    filter_upwards [hag, ha₁, ha₂] with ω hagω e₁ e₂
    by_cases hωL : ω ∈ L
    · obtain ⟨hG, a₁, a₂⟩ := hagω hωL.1 hωL.2
      have b₁ : ∀ s ≤ d.u, d₀.η₁ ω s = d.η₁ ω s := fun s hs => by
        change hproj (ηc₁ ω (min s d.u)) = _
        rw [min_eq_left hs, e₁ s,
          capTime_eq_of_lt hωL.1 (lt_capR_left d.u d.r) hs, ← a₁ s hs]
        exact hproj_of_im_nonneg ((hd.good ω hG).2.2.1 ⟨zero_le, hs⟩)
      have b₂ : ∀ t ≤ d.r, d₀.η₂ ω t = d.η₂ ω t := fun t ht => by
        change hproj (ηc₂ ω (min t d.r)) = _
        rw [min_eq_left ht, e₂ t,
          capTime_eq_of_lt hωL.2 (lt_capR_right d.u d.r) ht, ← a₂ t ht]
        exact hproj_of_im_nonneg ((hd.good ω hG).2.2.2.1 ⟨zero_le, ht⟩)
      have hG₀ : ω ∈ d₀.G := by
        intro t ht he
        have he' : d₀.η₂ ω t = d₀.η₂ ω d.r := he
        rw [b₂ t ht.le, b₂ d.r le_rfl] at he'
        exact (hd.good ω hG).2.2.2.2.2.2 t ht he'
      exact (RetData.chart_eq_of_agree (d := d) (G' := d'.G) hG ⟨hG₀, hωL⟩ b₁ b₂).2.2
    · have hG : ω ∉ d.G := fun h => hωL (hGsub h)
      have hG' : ω ∉ d'.G := fun h => hωL h.2
      rw [RetData.chart_of_notMem (fun h => hG (RetData.E_subset_G h)),
        RetData.chart_of_notMem (fun h => hG' (RetData.E_subset_G h))]
  obtain ⟨hdom', hfwd', hlift'⟩ := @RetData.IsMeasGood.chart_measurability Ω R d' hd'
  obtain ⟨hdom, hfwd, hlift⟩ := hd.chart_measurability
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_⟩
  · apply measurableSet_retSigma76_congr (hdom z) (hdom' z)
    filter_upwards [heq] with ω he
    exact congrArg (fun c : Chart => z ∈ c.dom) he.symm
  · apply measurable_retSigma76_congr (hfwd z) (hfwd' z)
    filter_upwards [heq] with ω he
    simp only [Set.indicator_apply, mem_ofPred_eq, he]
  · apply measurable_retSigma76_congr (hlift z) (hlift' z)
    filter_upwards [heq] with ω he
    simp only [Set.indicator_apply, mem_ofPred_eq, he]

end InteractingSLE.Restart.RetAux79
