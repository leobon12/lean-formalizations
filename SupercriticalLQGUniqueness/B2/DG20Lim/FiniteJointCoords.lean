import SupercriticalLQGUniqueness.B2.DG20Lim.AroundMeasurable

 





set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def finiteRatCoords (D : LQGMetric.ContMetric) : RatCoords :=
  (finiteCircleCoords D, finiteAroundCoords D)

theorem aemeasurable_finiteRatCoords
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (D : Ω → LQGMetric.ContMetric)
    (hD : AEMeasurable D P) :
    AEMeasurable (fun ω => finiteRatCoords (D ω)) P := by
  let Dm : Ω → LQGMetric.ContMetric := hD.mk D
  have hDm : Measurable Dm := hD.measurable_mk
  have hC : Measurable (fun ω => finiteCircleCoords (Dm ω)) :=
    measurable_finiteCircleCoords.comp hDm
  have hA : AEMeasurable (fun ω => finiteAroundCoords (Dm ω)) P :=
    aemeasurable_finiteAroundCoords Dm hDm
  have hBoth : AEMeasurable (fun ω => finiteRatCoords (Dm ω)) P :=
    hC.aemeasurable.prodMk hA
  exact hBoth.congr (hD.ae_eq_mk.mono fun ω hω => by
    simp only [finiteRatCoords, Dm, hω])

 
def measurableRatCoordsVersion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (D : Ω → LQGMetric.ContMetric)
    (hD : AEMeasurable D P) : Ω → RatCoords :=
  (aemeasurable_finiteRatCoords D hD).mk _

theorem measurable_measurableRatCoordsVersion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (D : Ω → LQGMetric.ContMetric)
    (hD : AEMeasurable D P) :
    Measurable (measurableRatCoordsVersion D hD) :=
  (aemeasurable_finiteRatCoords D hD).measurable_mk

theorem ae_eq_measurableRatCoordsVersion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (D : Ω → LQGMetric.ContMetric)
    (hD : AEMeasurable D P) :
    (fun ω => finiteRatCoords (D ω)) =ᵐ[P] measurableRatCoordsVersion D hD :=
  (aemeasurable_finiteRatCoords D hD).ae_eq_mk

end SupercriticalLQGUniqueness.B2.DG20Lim
