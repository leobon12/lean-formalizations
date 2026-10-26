import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Normalizer.Lemma25

/-!
# Lemma 2.5 estimates assembled from the normalizer module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLFPPAS.Glue

open HigherDimLFPPAS.Normalizer HigherDimLFPP HigherDimLQGMetric MeasureTheory

theorem lemma25_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) :
    Core.Lemma25Unif κ ξ Q ∧ Core.Lemma25Window κ ξ ∧ Core.Lemma25Exponent κ ξ Q := by
  have hd : 2 ≤ d := by have := hS.dim; omega
  refine ⟨fun a b ha η hη => ?_, fun a ha η hη => ?_, fun η hη => ?_⟩
  · exact lemma25_unif hd hS.admissible hS.strong hS.field hS.conv (b := b) ha η hη
  · exact lemma25_window hd hS.admissible hS.strong hS.field hS.conv ha η hη
  · exact lemma25_rpow_bounds hd hS.admissible hS.strong hS.field hS.conv η hη

end HigherDimLFPPAS.Glue
