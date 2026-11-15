/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC6Mean
import InteractingSLE.Spec.Sec7.SideC5Slices

/-!
# The precise remaining initial-height input

PROVE-SIDE-COLLAR2. The input concerns the initial pocket mean and base
chart only. It includes the supplied phase and common offset. It asserts
neither a comparison with a later mean nor a derivative-lift limit.
It is a named unproved mathematical input, not a source theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketStop PocketTraversal Lemma71C

/-- A driven traversal's zero-capacity inverse agrees with its base
inverse at every point of the upper half-plane. -/
theorem relChart_zero_inv_of_driven {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ}
    {ω : Ω} (hγ : IsDrivenCurve (γ ω)) {z : ℂ} (hz : z ∈ H) :
    (relChart c γ 0 ω).2.1 z = (c ω).2.1 z := by
  obtain ⟨W, hW, hW0, -, -, -, heq⟩ :=
    exists_relChart_eq_loewner (c := c) hγ (PocketPhaseMeans.capLife_pos hγ)
  rw [heq]
  exact Theorem14.GW2aCont.loewner_zero_inv hW hW0 hz

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C
  Sec7.PocketStopSide Sec7.Aux119Heights

/-- Remaining initial mathematics: the initial reference's own height
in the base chart is the prescribed initial word, with its phase and offset.
No proof of this boundary-height statement is claimed here. -/
def InitialReferenceHeightsExc {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let e := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (j.capacityReference i d 0) target.zeroField d.measure g₀ →
      ∀ᵐ ω ∂d.measure, ω ∈ target.event → ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a 0 ω -
          segDriver (target.curve ω) 0)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a 0 ω -
          segDriver (target.curve ω) 0) →
        extendFrom H (relChart target.baseChart target.curve 0 ω).2.1 (ξ : ℂ) ∉ X j 0 ω →
        Tendsto (sideMean target.kappa (target.baseChart ω) target.harmonic
          (harmRep (g₀ ω) (H \ j.capacityReference i d 0 ω)))
          (𝓝[H] (ξ : ℂ)) (𝓝 (forceBoundaryData target.kappa target.rhoL target.rhoR
            (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a 0 ω -
              segDriver (target.curve ω) 0)
            (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a 0 ω -
              segDriver (target.curve ω) 0) ξ +
            e.phase 0 ω * (Ioo
              (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL 0 ω -
                segDriver (target.curve ω) 0)
              (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR 0 ω -
                segDriver (target.curve ω) 0)).indicator 1 ξ - e.offset))

end InteractingSLE.Wire
