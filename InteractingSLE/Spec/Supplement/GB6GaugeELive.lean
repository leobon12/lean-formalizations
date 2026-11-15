/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEPrefix
import InteractingSLE.Spec.Supplement.GB6HullIdReadout

/-!
# The source separation readout is continuous and positive on the record event

This uses the corrected event-local interface. No condition is imposed on
arbitrary chosen coordinates outside the record event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Supp8.GB6.GaugeE

open Exist.StagedLaw ReadD RelDrv

/-- Every retained prefix point, rather than only its endpoint, is decoded
correctly from the actual record. -/
theorem recordTrace_eq {Ω : Type*} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    {α : Ω → ℝ≥0 → ℂ} {ω : Ω} (s : ℝ≥0) (h0 : Wα 0 ω = 0)
    (hc : ContinuousOn (Wα · ω) {t | (t : ℝ≥0∞) < ζα ω})
    (hα : IsGeneratingTrace (Wα · ω) (ζα ω) (α ω)) (hs : (s : ℝ≥0∞) < ζα ω)
    {v : ℝ≥0} (hv : v ≤ s) : recordTrace v (gb6Rec s Wα ζα ω) = α ω v := by
  unfold recordTrace
  rw [LP.traceAt_congr (w' := (Wα · ω)) (fun u hu => ?_)]
  · exact LP.traceAt_eq_of_isGeneratingTrace hα hc h0 ((ENNReal.coe_le_coe.2 hv).trans_lt hs)
  · have he := rdrv_recOf_cfE s h0 hc hs (x := (u : ℝ)) (NNReal.coe_le_coe.2 (hu.trans hv))
    change rdrv (gb6Rec s Wα ζα ω) (u : ℝ) = Wα u ω
    rw [show rdrv (gb6Rec s Wα ζα ω) (u : ℝ) = Wα (u : ℝ).toNNReal ω from he, Real.toNNReal_coe]

/-- The two preterminal clauses of `HasLiveReadout` follow from the original
source hypotheses and the existing source coordinate predicate. -/
theorem ae_separationRead_regular {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) (hs0 : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s →
      ContinuousOn (fun t => separationRead s t (gb6Rec s Wα ζα ω, (fun u => D u ω)))
        {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω →
        0 < separationRead s t (gb6Rec s Wα ζα ω, (fun u => D u ω))) ∧
      recordTrace 0 (gb6Rec s Wα ζα ω) = 0 ∧
      ContinuousOn (fun v => recordTrace v (gb6Rec s Wα ζα ω)) (Iic s) ∧
      ContinuousOn (fun u => physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω)))
        {u | (u : ℝ≥0∞) < L ω} := by
  filter_upwards [ae_physicalReadback hκ hκ4 hF hα hW s hs0 hC, hC.relative,
    ae_gb6RecGood hF hα s, hW, hα, ae_driver_zero_continuousOn hF]
    with ω hread hcoords hgood hcounter hflow hreg hrec
  obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hgood).2 hrec
  obtain ⟨ha0, ham, hac, hat, hcapacity⟩ := hread hs hsH
  obtain ⟨hrange, _⟩ := hcoords hs hsH
  have hγc : Continuous (γ ω) := by
    have hc := hcounter.2.2.2.1
    simp only [le_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  have hX := continuousOn_liveReadback
    (X := fun u => physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω))) ha0 ham hac hrange hγc hat
  have hAe : ∀ v ≤ s, recordTrace v (gb6Rec s Wα ζα ω) = α ω v :=
    fun _ hv => recordTrace_eq s hreg.1 hreg.2 hflow hs hv
  have hA : ContinuousOn (fun v => recordTrace v (gb6Rec s Wα ζα ω)) (Iic s) :=
    (hflow.2.1.mono (fun v hv => show (v : ℝ≥0∞) ≤ ζα ω from
      ((ENNReal.coe_le_coe.2 hv).trans_lt hs).le)).congr (fun v hv => hAe v hv)
  refine ⟨continuousOn_separationRead s _ _ hX hA, ?_, ?_, hA, hX⟩
  · intro t ht
    apply separationRead_pos s t _ _ (hX.mono (fun u hu => (ENNReal.coe_le_coe.2 hu).trans_lt ht)) hA
    intro u hu v hv
    obtain ⟨q, hq, _, hXu⟩ := hcapacity u ((ENNReal.coe_le_coe.2 hu).trans_lt ht)
    rw [hXu, hAe v hv]
    intro hzero
    exact notMem_of_lt_firstContactTime hq ⟨v, ⟨zero_le, hv⟩,
      ((SourceC.sphereInv_eq_iff _ _).2 hzero).symm⟩
  · rw [hAe 0 zero_le]
    exact hflow.1

end InteractingSLE.Supp8.GB6.GaugeE
