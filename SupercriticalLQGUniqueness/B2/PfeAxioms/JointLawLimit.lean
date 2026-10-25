import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem joint_limit_law_eq_of_finite_laws
    {E Ω Ω' : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (F : ℕ → Ω → E) (F' : ℕ → Ω' → E)
    (L : Ω → E) (L' : Ω' → E)
    (hmF : ∀ n, AEMeasurable (F n) P)
    (hmF' : ∀ n, AEMeasurable (F' n) P')
    (hmL : AEMeasurable L P) (hmL' : AEMeasurable L' P')
    (hLaw : ∀ n, P.map (F n) = P'.map (F' n))
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (L ω)))
    (hConv' : ∀ᵐ ω ∂P', Tendsto (fun n => F' n ω) atTop (𝓝 (L' ω))) :
    P.map L = P'.map L' := by
  have hD := tendstoInDistribution_of_ae_tendsto
    hmF hmL hConv
  have hD' := tendstoInDistribution_of_ae_tendsto
    hmF' hmL' hConv'
  have hSeq :
      (fun n => (⟨P.map (F n), inferInstance⟩ : ProbabilityMeasure E)) =
      (fun n => (⟨P'.map (F' n), inferInstance⟩ : ProbabilityMeasure E)) := by
    funext n
    exact Subtype.ext (hLaw n)
  have hD'' : TendstoInDistribution F atTop L' (fun _ => P) P' := by
    refine ⟨hmF, hmL', ?_⟩
    simpa only [hSeq] using hD'.tendsto
  exact tendstoInDistribution_unique F hD hD''

end SupercriticalLQGUniqueness.B2.PfeAxioms
