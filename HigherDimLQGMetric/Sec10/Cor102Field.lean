import HigherDimLQGMetric.Field.Affine
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.LGF.Invariance

/-!
# Affine pullback preserves the two input classes

Local adapters for the fixed dilation in Corollary 10.2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- An LGF plus a continuous function stays in the same class after affine pullback. -/
theorem s8c_lgfPlusCont_affine {h : Ω → DistRd d} (hh : IsLGFPlusCont h P)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    IsLGFPlusCont (fun ω => affineComp r z (h ω)) P := by
  obtain ⟨hm, f, hf, hg⟩ := hh
  refine ⟨Measurable.affineComp hm r z, fun ω => (f ω).comp (affinePt r z),
    (ContinuousMap.continuous_precomp _).measurable.comp hf, ?_⟩
  have he : (fun ω => affineComp r z (h ω) - ofCont ((f ω).comp (affinePt r z))) =
      fun ω => affineComp r z (h ω - ofCont (f ω)) := by
    funext ω
    rw [affineComp_sub, affineComp_ofCont hr]
  rw [he]
  exact hg.affineComp hr z

/-- Affine pullback preserves samplewise bounded continuous perturbations. -/
theorem s8c_lgfPlusBdd_affine {h : Ω → DistRd d} (hh : IsLGFPlusBddCont h P)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    IsLGFPlusBddCont (fun ω => affineComp r z (h ω)) P := by
  obtain ⟨hm, f, hf, hb, hg⟩ := hh
  refine ⟨Measurable.affineComp hm r z, fun ω => (f ω).comp (affinePt r z),
    (ContinuousMap.continuous_precomp _).measurable.comp hf, ?_, ?_⟩
  · intro ω
    obtain ⟨M, hM⟩ := hb ω
    exact ⟨M, fun x => hM (affinePt r z x)⟩
  · have he : (fun ω => affineComp r z (h ω) - ofCont ((f ω).comp (affinePt r z))) =
        fun ω => affineComp r z (h ω - ofCont (f ω)) := by
      funext ω
      rw [affineComp_sub, affineComp_ofCont hr]
    rw [he]
    exact hg.affineComp hr z

end HigherDimLQGMetric
