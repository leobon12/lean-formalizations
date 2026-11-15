/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEEndpoint

/-!
# GB6's measurable relative-driver versions

The source hypotheses prove the corrected live readout on the retained
record event. The landed HULLID construction repairs the coordinates off
that event and supplies the regular stopped versions and their exhaustion.
No readout or terminal-geometry hypothesis remains.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Supp8.GB6.GaugeE

open RelDrv

/-- The original flow-line and transient counterflow trace hypotheses give
the corrected live readout for any proved source relative coordinates. -/
theorem hasLiveReadout {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) (hs : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    HullId.HasLiveReadout s P (gb6Rec s Wα ζα) D L :=
  hasLiveReadout_of_physicalTerminal hκ hκ4 hF hα
    (hW.mono (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)) s hs hC
    (hasPhysicalTerminalLimits hκ hκ4 hF hα hW s hs hC)

/-- The source live-readout statement, with all original outer binders and
no additional mathematical input. -/
theorem gb6LiveReadoutStatement : HullId.GB6LiveReadoutStatement.{u} := by
  intro κ θ hκ hκ4 _ _ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
    _ _ _ _ hcf hγ hflow hα s hs
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure P := hP
  have hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop := by
    filter_upwards [ae_driver_zero_continuousOn hcf, hγ] with ω hr ht
    have hc : Continuous (W · ω) := continuousOn_univ.1 (hr.2.mono fun t _ => by
      rw [mem_ofPred_eq, ht.1]
      exact ENNReal.coe_lt_top)
    exact ⟨hc, hr.1, ht.2.1, ht.2.2⟩
  exact hasLiveReadout hκ hκ4 hflow hα hW s hs
    (SourceC.sourceCoordinates_spec hcf hflow (hγ.mono fun _ hω => ⟨hω.1, hω.2.1⟩) hα s hs)

/-- The regular rule form of GB6's stopped relative-driver versions. -/
theorem gb6RelVersionRStatement : HullId.GB6RelVersionRStatement.{u} :=
  HullId.gb6RelVersionRStatement_of_readoutCoord
    (HullId.gb6ReadoutCoordStatement_of_liveReadout gb6LiveReadoutStatement)

/-- GB6's full measurable relative-driver versions and pre-contact
exhaustion, with the original source statement unchanged. -/
theorem gb6RelVersionStatement : GB6RelVersionStatement.{u} :=
  HullId.gb6RelVersionStatement_of_R gb6RelVersionRStatement

end InteractingSLE.Supp8.GB6.GaugeE
