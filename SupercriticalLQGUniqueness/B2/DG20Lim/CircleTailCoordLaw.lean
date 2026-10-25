import SupercriticalLQGUniqueness.B2.DG20Lim.LimitPositiveFromTail
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteJointCoords
import LQGMetric.Field.StandardBorelRange

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem circle_lower_tail_of_joint_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (Y : Ω' → (CoordJ → ℝ) × RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)))
    (O Pcircle : RatCircle) (δ b : ℝ≥0∞)
    (hSource : P {ω | finiteCircleCoords (D ω) (O, Pcircle) < δ} ≤ b) :
    P' {ω | (Y ω).2.1 (O, Pcircle) < δ} ≤ b := by
  let π : (CoordJ → ℝ) × RatCoords → ℝ≥0∞ :=
    fun q => q.2.1 (O, Pcircle)
  have hπ : Measurable π :=
    (measurable_pi_apply (O, Pcircle)).comp
      (measurable_fst.comp measurable_snd)
  let S : Ω → (CoordJ → ℝ) × RatCoords :=
    fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)
  have hS : Measurable S :=
    ((measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion D hD)
  have hCoordLaw : P'.map (π ∘ Y) = P.map (π ∘ S) := by
    calc
      P'.map (π ∘ Y) = (P'.map Y).map π :=
        (Measure.map_map hπ hY).symm
      _ = (P.map S).map π := by rw [hLaw]
      _ = P.map (π ∘ S) := Measure.map_map hπ hS
  have hVersion :
      {ω | π (S ω) < δ} =ᵐ[P]
        {ω | finiteCircleCoords (D ω) (O, Pcircle) < δ} := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD] with ω hω
    simp only [S, π, finiteRatCoords] at *
    rw [← hω]
  calc
    P' {ω | (Y ω).2.1 (O, Pcircle) < δ} =
      (P'.map (π ∘ Y)) (Iio δ) := by
        rw [Measure.map_apply (hπ.comp hY) isOpen_Iio.measurableSet]
        rfl
    _ = (P.map (π ∘ S)) (Iio δ) := by rw [hCoordLaw]
    _ = P {ω | π (S ω) < δ} := by
      rw [Measure.map_apply (hπ.comp hS) isOpen_Iio.measurableSet]
      rfl
    _ = P {ω | finiteCircleCoords (D ω) (O, Pcircle) < δ} :=
      measure_congr hVersion
    _ ≤ b := hSource

end SupercriticalLQGUniqueness.B2.DG20Lim
