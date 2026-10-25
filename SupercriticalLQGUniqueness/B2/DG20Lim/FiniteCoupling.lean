import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoordEmbedding
import LQGMetric.Field.RandomDistVersion

 





set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

def decodeFinitePair : (LQGMetric.CoordJ → ℝ) × RatCoords →
    LQGMetric.DistC × LQGMetric.ContMetric :=
  fun q => (LQGMetric.pairJInv ⊤ q.1, circleCoordsInv q.2.1)

theorem measurable_decodeFinitePair : Measurable decodeFinitePair :=
  ((LQGMetric.measurable_pairJInv ⊤).comp measurable_fst).prodMk
    (measurable_circleCoordsInv.comp (measurable_fst.comp measurable_snd))

theorem ae_decodeFinitePair_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (h : Ω → LQGMetric.DistC)
    (D : Ω → LQGMetric.ContMetric) (hD : AEMeasurable D P) :
    (fun ω => decodeFinitePair
      (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)) =ᵐ[P]
      (fun ω => (h ω, D ω)) := by
  filter_upwards [ae_eq_measurableRatCoordsVersion D hD] with ω hω
  have heq : (measurableRatCoordsVersion D hD ω).1 = finiteCircleCoords (D ω) :=
    congrArg Prod.fst hω.symm
  simp only [decodeFinitePair, LQGMetric.pairJInv_pairJ, heq,
    circleCoordsInv_finiteCircleCoords]

 

theorem joint_finite_pair_law_of_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsFiniteMeasure P]
    {P' : Measure Ω'}
    (h : Ω → LQGMetric.DistC) (hh : Measurable h)
    (D : Ω → LQGMetric.ContMetric) (hD : AEMeasurable D P)
    (Y : Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords)
    (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (fun ω =>
      (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω))) :
    P'.map (fun ω => decodeFinitePair (Y ω)) =
      P.map (fun ω => (h ω, D ω)) := by
  have hSource : Measurable (fun ω =>
      (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)) :=
    ((LQGMetric.measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion D hD)
  calc
    P'.map (fun ω => decodeFinitePair (Y ω)) =
        (P'.map Y).map decodeFinitePair :=
      (Measure.map_map measurable_decodeFinitePair hY).symm
    _ = (P.map (fun ω =>
          (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω))).map
          decodeFinitePair := by rw [hLaw]
    _ = P.map (fun ω => decodeFinitePair
          (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)) :=
      Measure.map_map measurable_decodeFinitePair hSource
    _ = P.map (fun ω => (h ω, D ω)) :=
      Measure.map_congr (ae_decodeFinitePair_source h D hD)

end SupercriticalLQGUniqueness.B2.DG20Lim
