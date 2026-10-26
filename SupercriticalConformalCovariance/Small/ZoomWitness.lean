import SupercriticalConformalCovariance.Small.ZoomFieldSquare
import LQGMetric.Papers.GM.S1.Dilate

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SupercriticalConformalCovariance.Small
open LQGMetric

/-- A chosen whole-plane GFF witness for the original target realization
remains a witness after a positive affine zoom. -/
theorem wholePlaneGFF_zoom_witness
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → DistC) (F : Ω → C(ℂ, ℝ))
    (hwp : IsWholePlaneGFF (fun ω => g ω - ofCont (F ω)) P)
    (a : ℂ) {r : ℝ} (hr : 0 < r) :
    IsWholePlaneGFF
      (fun ω => affineComp r a (g ω) -
        ofCont ((F ω).comp (affinePt r a))) P := by
  have heq : (fun ω => affineComp r a (g ω) -
      ofCont ((F ω).comp (affinePt r a))) =
      (fun ω => affineComp r a (g ω - ofCont (F ω))) := by
    funext ω
    rw [LQGMetric.GM.affineComp_sub, LQGMetric.GM.affineComp_ofCont hr]
  rw [heq]
  exact hwp.affineComp hr a

end SupercriticalConformalCovariance.Small
