/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXSource
import InteractingSLE.Spec.Coupling.WFSBridge

/-! # Recover the original marked state from an agreeing driver -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open Sec7.PocketTraversal
namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- Before the exit all original force coordinates are geometric functions
of any continuous driver agreeing with the original driver there. -/
theorem ae_original_geom_of_agree {e : S → ℝ≥0∞} {W : ℝ≥0 → S → ℝ}
    (he : e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω))
    (hc : ∀ ω, Continuous (W · ω))
    (hag : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω) :
    ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω →
      D.W₀ t ω = W t ω ∧
      (∀ i, D.VL₀ i t ω = geomLW W (fun _ => flowLineXL D.b D.J D.y) i t ω) ∧
      ∀ j, D.VR₀ j t ω = geomRW W (fun _ => flowLineXR D.b D.J D.y) j t ω := by
  filter_upwards [he, hag, D.coupling.1.ae_isIntegratedSLEPath, D.trace] with ω heω hagω hp hg t ht
  have hag' : ∀ s : ℝ≥0, (s : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω) →
      W s ω = D.W₀ s ω := fun s hs => hagω s (heω ▸ hs)
  obtain ⟨-, -, hL, hR, -, -⟩ := stopPathData_det D.V_bounded D.closureV_real D.hull_subset
    hp hg (hc ω) hag' (heω ▸ ht)
  refine ⟨(hagω t ht).symm, fun i => ?_, fun j => ?_⟩
  · apply sub_left_inj.mp
    simpa only [geomL_rpath_eq_geomLW_sub, hagω t ht] using hL i
  · apply sub_left_inj.mp
    simpa only [geomR_rpath_eq_geomRW_sub, hagω t ht] using hR j

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI
