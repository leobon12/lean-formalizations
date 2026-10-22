import HigherDimLQGMetric.Locality.StageData
import LQGMetric.Papers.DFGPS.L2_19
import LQGMetric.Prob.CondIndepAEDet

/-!
# The cutoff Markov harmonic field is an interior observation

The Markov theorem supplies a pointwise measurable version of the harmonic
field. Its actual continuous version agrees with this version almost surely.
This is enough to make a continuous cutoff of the actual field measurable in
the almost-everywhere completion of the interior sigma algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.GM.Bilip (aeClosure)

theorem l7a_cutoffH_comap_le_aeClosure {d : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (M : MeasurableSpace Ω) {U : Set (Rd d)} (hU : IsOpen U)
    (φ : C(Rd d, ℝ)) (hsup : tsupport φ ⊆ U)
    (H G : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) U)
    (hGm : Measurable[M] G) (hHG : H =ᵐ[P] G) :
    MeasurableSpace.comap
      (fun ω => (⟨fun x => φ x * H ω x,
        l7a_continuous_cutoffH hU φ (H ω) (hHc ω) hsup⟩ : C(Rd d, ℝ)))
      inferInstance ≤ aeClosure P M := by
  have hEval (x : Rd d) : Measurable[aeClosure P M]
      (fun ω => φ x * H ω x) := by
    have hGx : Measurable[M] (fun ω => φ x * G ω x) := by
      letI : MeasurableSpace Ω := M
      exact measurable_const.mul ((measurable_pi_apply x).comp hGm)
    have hFx : (fun ω => φ x * H ω x) =ᵐ[P]
        (fun ω => φ x * G ω x) :=
      hHG.mono (fun ω hω => by simp only [hω])
    apply measurable_iff_comap_le.mpr
    rintro s ⟨t, ht, rfl⟩
    refine ⟨(fun ω => φ x * G ω x) ⁻¹' t, hGx ht, ?_⟩
    filter_upwards [hFx] with ω hω
    change (φ x * H ω x ∈ t) = (φ x * G ω x ∈ t)
    rw [hω]
  have hF : Measurable[aeClosure P M]
      (fun ω => (⟨fun x => φ x * H ω x,
        l7a_continuous_cutoffH hU φ (H ω) (hHc ω) hsup⟩ : C(Rd d, ℝ))) := by
    letI : MeasurableSpace Ω := aeClosure P M
    apply ContinuousMap.measurable_iff_eval.mpr
    intro x
    exact hEval x
  exact hF.comap_le

/-- A cutoff of the Markov harmonic field has an interior-measurable
continuous-map version. This is the standard-Borel upgrade of its eventwise
almost-sure measurability. -/
theorem l7a_exists_measurable_cutoffH_version {d : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (M : MeasurableSpace Ω) {U : Set (Rd d)} (hU : IsOpen U)
    (φ : C(Rd d, ℝ)) (hsup : tsupport φ ⊆ U)
    (H G : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) U)
    (hGm : Measurable[M] G) (hHG : H =ᵐ[P] G) :
    ∃ F : Ω → C(Rd d, ℝ), Measurable[M] F ∧
      (fun ω => (⟨fun x => φ x * H ω x,
        l7a_continuous_cutoffH hU φ (H ω) (hHc ω) hsup⟩ : C(Rd d, ℝ))) =ᵐ[P] F := by
  letI : MeasurableSpace Ω := mΩ
  exact LQGMetric.exists_ae_eq_measurable_of_aeDeterminedSigma
    (l7a_cutoffH_comap_le_aeClosure P M hU φ hsup H G hHc hGm hHG)

end HigherDimLQGMetric
