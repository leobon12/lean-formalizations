import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedRatAnnulusLocality
import SupercriticalLQGUniqueness.B2.DG20Lim.CircleTailCoordLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem bad_ratio_probability_of_joint_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (Y : Ω' → (CoordJ → ℝ) × RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)))
    (A : RatAnnulus) (C b : ℝ≥0∞)
    (hSource : P {ω | C * finiteCircleCoords (D ω)
      (A.inner, A.outer) < finiteAroundCoords (D ω) A} ≤ b) :
    P' {ω | C * (Y ω).2.1 (A.inner, A.outer) <
      (Y ω).2.2 A} ≤ b := by
  let bad : Set ((CoordJ → ℝ) × RatCoords) :=
    {v | C * v.2.1 (A.inner, A.outer) < v.2.2 A}
  have hAcross : Measurable fun v : (CoordJ → ℝ) × RatCoords =>
      v.2.1 (A.inner, A.outer) :=
    (measurable_pi_apply (A.inner, A.outer)).comp
      (measurable_fst.comp measurable_snd)
  have hAround : Measurable fun v : (CoordJ → ℝ) × RatCoords =>
      v.2.2 A :=
    (measurable_pi_apply A).comp (measurable_snd.comp measurable_snd)
  have hbad : MeasurableSet bad :=
    measurableSet_lt (measurable_const.mul hAcross) hAround
  let S : Ω → (CoordJ → ℝ) × RatCoords :=
    fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)
  have hS : Measurable S :=
    ((measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion D hD)
  have hVersion : S ⁻¹' bad =ᵐ[P]
      {ω | C * finiteCircleCoords (D ω) (A.inner, A.outer) <
        finiteAroundCoords (D ω) A} := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD] with ω hω
    change (C * (measurableRatCoordsVersion D hD ω).1
      (A.inner, A.outer) < (measurableRatCoordsVersion D hD ω).2 A) = _
    rw [← hω]
    rfl
  calc
    P' {ω | C * (Y ω).2.1 (A.inner, A.outer) < (Y ω).2.2 A} =
        (P'.map Y) bad := by
      rw [Measure.map_apply hY hbad]
      rfl
    _ = (P.map S) bad := by rw [hLaw]
    _ = P (S ⁻¹' bad) := Measure.map_apply hS hbad
    _ = P {ω | C * finiteCircleCoords (D ω) (A.inner, A.outer) <
          finiteAroundCoords (D ω) A} := measure_congr hVersion
    _ ≤ b := hSource

end SupercriticalLQGUniqueness.B2.DG20Lim
