/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafDenseIClosing

/-!
# A continuous adapted closed process from dyadic mean limits

The upper-dyadic construction is measurable at each time. Its closing
identity and null completeness give adaptedness. Conversely every continuous
closed version supplies the same dyadic limit condition on one conull event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique

/-- All version construction, adaptedness, and fixed-time identities follow
from the dyadic limit condition. The regularity condition itself is a premise. -/
theorem exists_continuous_closed_process_of_dyadic_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓓 : Filtration ℝ≥0 mΩ) [𝓓.IsRightContinuous]
    (hn : ∀ t, nullSigma P ≤ 𝓓 t) {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hlim : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ c : ℝ,
      Tendsto (fun d : dyadicTimes => P[Z | 𝓓 d] ω)
        (comap (fun d : dyadicTimes => (d : ℝ≥0)) (𝓝 t)) (𝓝 c)) :
    ∃ X : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 X ∧
      (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) ∧
      ∀ t, X t =ᵐ[P] P[Z | 𝓓 t] := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω => dyadicTimeLimit (fun s => P[Z | 𝓓 s] ω) t
  have he : ∀ t, X t =ᵐ[P] P[Z | 𝓓 t] :=
    ae_dyadicTimeLimit_eq_condExp 𝓓 hZ hlim
  have hXm : ∀ t, Measurable (X t) := by
    intro t
    exact (StronglyMeasurable.limUnder fun n =>
      (stronglyMeasurable_condExp (μ := P) (m := 𝓓 (dyadicTime (upperDyadic t n)))
        (f := Z)).mono (𝓓.le _)).measurable
  refine ⟨X, fun t => ?_, hlim.mono fun ω hω => continuous_dyadicTimeLimit hω, he⟩
  apply Measurable.stronglyMeasurable
  exact Sec2.Restart.measurable_of_ae_eq_of_null (𝓓.le t)
    (fun A hA hA0 => hn t A (MeasurableSpace.measurableSet_generateFrom ⟨hA, hA0⟩))
    stronglyMeasurable_condExp.measurable (hXm t) (he t).symm

/-- A continuous closed version implies the dyadic limit condition. Only
countably many fixed-time version equalities are intersected. -/
theorem ae_dyadic_limits_of_continuous_closed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓓 : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hclosed : ∀ t, X t =ᵐ[P] P[Z | 𝓓 t]) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ c : ℝ,
      Tendsto (fun d : dyadicTimes => P[Z | 𝓓 d] ω)
        (comap (fun d : dyadicTimes => (d : ℝ≥0)) (𝓝 t)) (𝓝 c) := by
  have he := ae_all_iff.2 (fun p : ℕ × ℕ => hclosed (dyadicTime p))
  filter_upwards [hc, he] with ω hcω heω
  have hv : (fun d : dyadicTimes => P[Z | 𝓓 d] ω) = fun d : dyadicTimes => X d ω := by
    funext d
    obtain ⟨p, hp⟩ := d.property
    exact hp ▸ (heω p).symm
  intro t
  refine ⟨X t ω, ?_⟩
  rw [hv]
  exact (hcω.tendsto t).comp tendsto_comap

end InteractingSLE.WFS
