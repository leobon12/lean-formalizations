import HigherDimLQGMetric.Amplify.MetricPairLaw

/-! Uniform witness probability at every translated trial center. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem amplify_wit_probability_eq_chain
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d}
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hh : IsWholeSpaceLGF h P)
    (U a A₀ ℓ β₀ t : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) =
      (P.map (fun ω =>
        (weakScaledMetric ξ A (fun x => x ^ (ξ * Q)) (h ω) hr z
          (Real.rpow_pos_of_pos hr _),
         weakScaledMetric ξ B (fun x => x ^ (ξ * Q)) (h ω) hr z
          (Real.rpow_pos_of_pos hr _))))
      {q : ContMetric d × ContMetric d | AmpUnitWitChain q U a A₀ ℓ β₀ t} := by
  let Z : Ω → ContMetric d × ContMetric d := fun ω =>
    (weakScaledMetric ξ A (fun x => x ^ (ξ * Q)) (h ω) hr z
      (Real.rpow_pos_of_pos hr _),
     weakScaledMetric ξ B (fun x => x ^ (ξ * Q)) (h ω) hr z
      (Real.rpow_pos_of_pos hr _))
  have hZ : Measurable Z :=
    ((amplify_measurable_weakScaledMetric hA hr z).comp hh.measurable).prodMk
      ((amplify_measurable_weakScaledMetric hB hr z).comp hh.measurable)
  let E : Set (ContMetric d × ContMetric d) :=
    {q | AmpUnitWitChain q U a A₀ ℓ β₀ t}
  have hE : NullMeasurableSet E (P.map Z) :=
    (ampUnitWitChain_uMeasurable U a A₀ ℓ β₀ t).nullMeasurableSet _
  have hAE : h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z =ᵐ[P] Z ⁻¹' E := by
    filter_upwards [hA.length P h hh.isLGFPlusCont,
      hB.length P h hh.isLGFPlusCont] with ω hlenA hlenB
    have hm : (Z ω).1.IsLength := weakScaledMetric_isLength ξ A
      (fun x => x ^ (ξ * Q)) (h ω) hr z (Real.rpow_pos_of_pos hr _) hlenA
    have hn : (Z ω).2.IsLength := weakScaledMetric_isLength ξ B
      (fun x => x ^ (ξ * Q)) (h ω) hr z (Real.rpow_pos_of_pos hr _) hlenB
    exact propext ((⟨amplify_unitWit_of_witEvent ξ Q U a A₀ ℓ β₀ t A B
      (h ω) hr z, amplify_witEvent_of_unitWit ξ Q U a A₀ ℓ β₀ t A B
      (h ω) hr z⟩ :
      h ω ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z ↔
      AmplifyUnitWit (Z ω).1 (Z ω).2 U a A₀ ℓ β₀ t).trans
      (ampUnitWit_iff_chain (Z ω).1 (Z ω).2 hm hn U a A₀ ℓ β₀ t))
  exact (measure_congr hAE).trans (Measure.map_apply₀ hZ.aemeasurable hE).symm

theorem amplify_wit_probability_center_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistRd d} {h' : Ω' → DistRd d}
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (hh' : IsWholeSpaceLGF h' P')
    (U a A₀ ℓ β₀ t : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) =
      P' (h' ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r 0) := by
  rw [amplify_wit_probability_eq_chain hA hB hh U a A₀ ℓ β₀ t hr z,
    amplify_wit_probability_eq_chain hA hB hh' U a A₀ ℓ β₀ t hr 0,
    amplify_map_weakScaledPair_eq hA hB hd hh hh' hr z]

end HigherDimLQGMetric
