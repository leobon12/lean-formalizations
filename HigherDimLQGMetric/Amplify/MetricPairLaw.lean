import HigherDimLQGMetric.Amplify.PairLaw
import HigherDimLQGMetric.Amplify.UnitWitnessMeas

/-! Joint law of the two centered metrics as metric objects. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem amplify_measurable_weakScaledMetric
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    Measurable fun X : DistRd d =>
      weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) X hr z
        (Real.rpow_pos_of_pos hr _) := by
  have hval : Measurable fun X : DistRd d =>
      (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) X hr z
        (Real.rpow_pos_of_pos hr _)).1 := by
    convert measurable_scaledField hD.measurable (fun t => t ^ (ξ * Q)) r z using 1
    funext X
    ext p
    exact weakScaledMetric_apply ξ D (fun t => t ^ (ξ * Q)) X hr z
      (Real.rpow_pos_of_pos hr _) p
  exact hval.subtype_mk

theorem amplify_map_weakScaledPair_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistRd d} {h' : Ω' → DistRd d}
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (hh' : IsWholeSpaceLGF h' P')
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    P.map (fun ω =>
      (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) (h ω) hr z
        (Real.rpow_pos_of_pos hr _),
       weakScaledMetric ξ Dt (fun t => t ^ (ξ * Q)) (h ω) hr z
        (Real.rpow_pos_of_pos hr _))) =
    P'.map (fun ω =>
      (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) (h' ω) hr 0
        (Real.rpow_pos_of_pos hr _),
       weakScaledMetric ξ Dt (fun t => t ^ (ξ * Q)) (h' ω) hr 0
        (Real.rpow_pos_of_pos hr _))) := by
  let e : ContMetric d × ContMetric d →
      C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ) :=
    fun q => (q.1.1, q.2.1)
  have he : MeasurableEmbedding e := by
    exact (MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)).prodMap
      (MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d))
  let Z : Ω → ContMetric d × ContMetric d := fun ω =>
    (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) (h ω) hr z
      (Real.rpow_pos_of_pos hr _),
     weakScaledMetric ξ Dt (fun t => t ^ (ξ * Q)) (h ω) hr z
      (Real.rpow_pos_of_pos hr _))
  let Z' : Ω' → ContMetric d × ContMetric d := fun ω =>
    (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) (h' ω) hr 0
      (Real.rpow_pos_of_pos hr _),
     weakScaledMetric ξ Dt (fun t => t ^ (ξ * Q)) (h' ω) hr 0
      (Real.rpow_pos_of_pos hr _))
  have hZ : Measurable Z :=
    ((amplify_measurable_weakScaledMetric hD hr z).comp hh.measurable).prodMk
      ((amplify_measurable_weakScaledMetric hDt hr z).comp hh.measurable)
  have hZ' : Measurable Z' :=
    ((amplify_measurable_weakScaledMetric hD hr 0).comp hh'.measurable).prodMk
      ((amplify_measurable_weakScaledMetric hDt hr 0).comp hh'.measurable)
  apply he.map_injective
  calc
    (P.map Z).map e = P.map (e ∘ Z) := Measure.map_map he.measurable hZ
    _ = P.map (fun ω =>
      (scaledField ξ D (fun t => t ^ (ξ * Q)) r z (h ω),
       scaledField ξ Dt (fun t => t ^ (ξ * Q)) r z (h ω))) := by
         congr 1
    _ = P'.map (fun ω =>
      (scaledField ξ D (fun t => t ^ (ξ * Q)) r 0 (h' ω),
       scaledField ξ Dt (fun t => t ^ (ξ * Q)) r 0 (h' ω))) :=
      amplify_map_scaledPair_eq hD hDt hd hh hh' hr z
    _ = P'.map (e ∘ Z') := by
         congr 1
    _ = (P'.map Z').map e := (Measure.map_map he.measurable hZ').symm

end HigherDimLQGMetric
