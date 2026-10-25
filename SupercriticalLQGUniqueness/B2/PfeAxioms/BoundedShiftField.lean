import SupercriticalLQGUniqueness.B2.PfeAxioms.ContinuousCutoff

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem isGFFPlusBddCont_addFun_of_normalized
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (f : Ω → C(ℂ, ℝ)) (hf : Measurable f)
    (hfb : ∀ ω, ∃ M : ℝ, ∀ z, |f ω z| ≤ M) :
    IsGFFPlusBddCont (fun ω => addFun (h ω) (f ω)) P := by
  have hb := LQGMetric.DFGPS.L217.isGFFPlusBddCont_sub_ofCont
    hh.1 hf.neg (fun ω => by
      obtain ⟨M, hM⟩ := hfb ω
      exact ⟨M, fun z => by simpa using hM z⟩)
  convert hb using 1
  funext ω
  change addFun (h ω) (f ω) = h ω - ofCont (-(f ω))
  rw [LQGMetric.DFGPS.L217.ofCont_neg, sub_neg_eq_add]
  rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
