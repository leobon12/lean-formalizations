import HigherDimLQGMetric.Events.TightLaw

/-! Joint centered laws for the two metric assignments in Lemma 6.1. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The law of the pair of centered metric observables is invariant under
translation and independent of the whole-space LGF realization. -/
theorem amplify_map_scaledPair_eq
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
      (scaledField ξ D (fun t => t ^ (ξ * Q)) r z (h ω),
       scaledField ξ Dt (fun t => t ^ (ξ * Q)) r z (h ω))) =
    P'.map (fun ω =>
      (scaledField ξ D (fun t => t ^ (ξ * Q)) r 0 (h' ω),
       scaledField ξ Dt (fun t => t ^ (ξ * Q)) r 0 (h' ω))) := by
  let Z : DistRd d → C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ) :=
    fun X => (scaledField ξ D (fun t => t ^ (ξ * Q)) r 0 X,
      scaledField ξ Dt (fun t => t ^ (ξ * Q)) r 0 X)
  have hZ : Measurable Z :=
    (measurable_scaledField hD.measurable _ r 0).prodMk
      (measurable_scaledField hDt.measurable _ r 0)
  have hz := hh.affineComp one_pos z
  have htrans : ∀ᵐ ω ∂P,
      (scaledField ξ D (fun t => t ^ (ξ * Q)) r z (h ω),
       scaledField ξ Dt (fun t => t ^ (ξ * Q)) r z (h ω)) =
      Z (affineComp 1 z (h ω)) := by
    filter_upwards [hD.ae_scaledField_translate hd hh hr z,
      hDt.ae_scaledField_translate hd hh hr z] with ω h1 h2
    exact congrArg₂ Prod.mk h1 h2
  have hnorm : ∀ᵐ ω ∂P,
      Z (affineComp 1 z (h ω)) =
      Z (addConst (affineComp 1 z (h ω))
        (-sphereAvg (affineComp 1 z (h ω)) 1 0)) := by
    filter_upwards [hD.ae_scaledField_normalize hd hz hr,
      hDt.ae_scaledField_normalize hd hz hr] with ω h1 h2
    exact congrArg₂ Prod.mk h1 h2
  have hnorm' : ∀ᵐ ω ∂P', Z (h' ω) =
      Z (addConst (h' ω) (-sphereAvg (h' ω) 1 0)) := by
    filter_upwards [hD.ae_scaledField_normalize hd hh' hr,
      hDt.ae_scaledField_normalize hd hh' hr] with ω h1 h2
    exact congrArg₂ Prod.mk h1 h2
  rw [Measure.map_congr htrans, Measure.map_congr hnorm,
    Measure.map_congr hnorm']
  have hN := measurable_sphereAvg_left (d := d) 1 0
  have hm1 : Measurable fun ω => addConst (affineComp 1 z (h ω))
      (-sphereAvg (affineComp 1 z (h ω)) 1 0) :=
    (hz.addConst (hN.comp hz.measurable).neg).measurable
  have hm2 : Measurable fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0) :=
    (hh'.addConst (hN.comp hh'.measurable).neg).measurable
  calc
    P.map (fun ω => Z (addConst (affineComp 1 z (h ω))
        (-sphereAvg (affineComp 1 z (h ω)) 1 0))) =
        (P.map (fun ω => addConst (affineComp 1 z (h ω))
          (-sphereAvg (affineComp 1 z (h ω)) 1 0))).map Z := by
          simpa only [Function.comp_def] using (Measure.map_map hZ hm1).symm
    _ = (P'.map (fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0))).map Z := by
      rw [map_normalizedLGF_eq hd hz hh']
    _ = P'.map (fun ω => Z (addConst (h' ω) (-sphereAvg (h' ω) 1 0))) := by
      simpa only [Function.comp_def] using Measure.map_map hZ hm2

end HigherDimLQGMetric
