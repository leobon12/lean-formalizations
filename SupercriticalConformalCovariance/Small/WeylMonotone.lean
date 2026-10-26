import SupercriticalConformalCovariance.Domain.Geometry

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness (LSCMetric)
open SupercriticalConformalCovariance (weylScaleOn)

/-- Restricting the path domain can only increase the domain Weyl distance. -/
theorem weylScaleOn_le_restrict (D : LSCMetric) (ξ : ℝ)
    {W V : Set ℂ} (hWV : W ⊆ V) (f : C(V, ℝ)) (p : W × W) :
    weylScaleOn ξ f D
      (⟨(p.1 : ℂ), hWV p.1.2⟩, ⟨(p.2 : ℂ), hWV p.2.2⟩) ≤
    weylScaleOn ξ (SupercriticalConformalCovariance.Domain.resC hWV f) D p := by
  unfold weylScaleOn
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hP =>
    le_iInf fun hspeed => le_iInf fun h0 => le_iInf fun hL => ?_
  let Q : ℝ → V := fun t => ⟨(P t : ℂ), hWV (P t).2⟩
  refine iInf_le_of_le Q <| iInf_le_of_le L <|
    iInf_le_of_le hP <| iInf_le_of_le hspeed <|
    iInf_le_of_le (Subtype.ext (congrArg (fun x : W => (x : ℂ)) h0)) <|
    iInf_le_of_le (Subtype.ext (congrArg (fun x : W => (x : ℂ)) hL)) ?_
  exact le_of_eq (by congr 1)

end SupercriticalConformalCovariance.Small
