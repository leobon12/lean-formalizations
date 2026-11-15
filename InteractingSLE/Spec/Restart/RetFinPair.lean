/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetFinGlue
import InteractingSLE.Spec.Restart.RetPlumbProofHist
import InteractingSLE.Spec.Restart.RetPlumbLine
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj

/-!
# The retained pair event and the word comparison

Packet PROVE-T15-RET3. Two probabilistic facts for the finite type partition of
`RetAux79.RetStoppedModelsStatement`:

* `exists_retSigma76_pairEvent`: the disjoint-pair event of the two flow lines at `(u, r)` agrees almost
  surely with an event of the retained σ-algebra `retSigma76` (the pair set of CONDDET-HIST's stopped retained
  data, which is good for `retSigma76`, intersected with the live event);
* `ae_mean_integrals_eq_retWordAt`: almost surely at a disjoint pair, an arbitrary sorted mean-identifying word
  `β` (for retained data `d`) and the explicit retained word `retWordAt` of any retained family agreeing with the
  flow lines are both sorted and have the same mean pairings. Both identify the same conditional mean in charts
  which agree at the pair (`RetData.chart_eq_of_agree`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetFin

open LQGMetric (DistOn TestOn)
open Supp7 Sec7 Sec7.Lemma76F RetAux79

universe v

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The disjoint-pair event is, up to a null set, an event of the retained σ-algebra.** -/
theorem exists_retSigma76_pairEvent (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (u₀ : ℂ → ℝ) (u r : ℝ≥0) :
    ∃ B : Set Ω, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] B ∧
      ∀ᵐ ω ∂P, ω ∈ B ↔ Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r := by
  obtain ⟨ηs₁, ηs₂, hd', hag'⟩ := RLC.exists_retStop hL75 hκ hκ4 hb hh hη₁ hη₂ u₀ u r
  set d' := stopRet ηs₁ ηs₂ u r with hd'def
  have hLive := measurableSet_retLive P η₁ η₂ ζ₁ ζ₂ (measurable_lifetime_of_isFlowLine hη₁)
    (measurable_lifetime_of_isFlowLine hη₂) u r
  refine ⟨pairSet d' (fun _ => ⊤) (fun _ => ⊤) ∩ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω},
    (@measurableSet_pairSet Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r) d' hd' (fun _ => ⊤) (fun _ => ⊤)
      measurable_const measurable_const).inter hLive, ?_⟩
  filter_upwards [hag'] with ω hω
  have key : ∀ (hu : (u : ℝ≥0∞) < ζ₁ ω) (hr : (r : ℝ≥0∞) < ζ₂ ω),
      (ω ∈ pairSet d' (fun _ => ⊤) (fun _ => ⊤) ↔
        Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r) := by
    intro hu hr
    obtain ⟨hG', a₁, a₂⟩ := hω hu hr
    rw [@mem_pairSet_iff Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r) d' hd' _ _ ω hG']
    exact isDisjointPair_congr a₁ a₂ (iff_of_true ENNReal.coe_lt_top hu)
      (iff_of_true ENNReal.coe_lt_top hr)
  constructor
  · rintro ⟨hP, hu, hr⟩
    exact (key hu hr).1 hP
  · intro hp
    exact ⟨(key hp.1 hp.2.1).2 hp, hp.1, hp.2.1⟩

/-- **An arbitrary mean-identifying word and the explicit retained word have the same mean pairings** almost
surely at a disjoint pair, and both are sorted there. -/
theorem ae_mean_integrals_eq_retWordAt (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hmean : IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    (hsort : ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).IsSorted)
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {G : ℝ≥0 → Set Ω}
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hdG : (retFam G η₁' η₂' d.u d.r).IsMeasGood)
    (hG : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ G d.r)
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps)
    (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y) :
    ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (β ω).IsSorted ∧ (retWordAt G η₁' η₂' d.u κ θ₁ θ₂ c₀ d.r ω).IsSorted ∧
        ∀ φ : TestOn upperHalfPlaneOpens,
          ∫ z, (β ω).mean z * φ z = ∫ z, (retWordAt G η₁' η₂' d.u κ θ₁ θ₂ c₀ d.r ω).mean z * φ z := by
  have hagF : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω →
      ω ∈ (retFam G η₁' η₂' d.u d.r).G ∧
      (∀ s ≤ (retFam G η₁' η₂' d.u d.r).u, (retFam G η₁' η₂' d.u d.r).η₁ ω s = η₁ ω s) ∧
      ∀ t ≤ (retFam G η₁' η₂' d.u d.r).r, (retFam G η₁' η₂' d.u d.r).η₂ ω t = η₂ ω t := by
    filter_upwards [hG, ha₁, ha₂] with ω hGω e₁ e₂ hu hr
    exact ⟨hGω hu hr, fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hu.le),
      fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht).trans hr.le)⟩
  obtain ⟨hW, hWs⟩ := Lemma76G.isRetMeanIdent_wordM (θ₁ := θ₁) (θ₂ := θ₂) hL75 hκ hκ4 hb hx hh hη₁ hη₂
    hdG hagF hu₀ hc₀ hc₀J hc₀b
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, -, -, e₁, e₂, g, hg, -⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hη₂
      hu₀ (capR d.u d.r) d.u d.r
  have hβ := hmean ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ e₁ e₂ hg
  have hW' := hW ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ e₁ e₂ hg
  filter_upwards [hβ, hW', hWs, hsort, hag, hagF] with ω eβ eW sW sβ a aF hp
  obtain ⟨hGd, a₁, a₂⟩ := a hp.1 hp.2.1
  obtain ⟨hGF, aF₁, aF₂⟩ := aF hp.1 hp.2.1
  have hch : (retFam G η₁' η₂' d.u d.r).chart ω = d.chart ω :=
    (RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁') (η₂' := η₂') hGd hGF
      (fun s hs => (aF₁ s hs).trans (a₁ s hs).symm) (fun t ht => (aF₂ t ht).trans (a₂ t ht).symm)).2.2
  refine ⟨sβ hp, sW hp, fun φ => ?_⟩
  rw [← eβ hp φ]
  exact (congrArg (fun H : DistOn upperHalfPlaneOpens => H φ)
    (Restart.chartTransport_congr_chart hch.symm _ _ _ _ _ _)).trans (eW hp φ)

end InteractingSLE.Restart.RetFin
