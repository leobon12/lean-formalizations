import HigherDimLQGMetric.Locality.CutoffH
import HigherDimLQGMetric.Markov.OfFun

/-! The exterior Markov residual has a measurable version. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Almost sure equality to a pointwise measurable field suffices for
measurability of its continuous open-set distribution in the completed
ambient sigma algebra. -/
theorem l7a_residual_comap_le_aeClosure {d : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → DistRd d) (hg : Measurable g)
    (O : TopologicalSpace.Opens (Rd d))
    (M : MeasurableSpace Ω) (hM : M ≤ mΩ)
    (H G : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) O)
    (hGm : Measurable[M] G) (hHG : H =ᵐ[P] G) :
    MeasurableSpace.comap (fun ω => restrictTo O (g ω) - ofFunOn O (H ω))
      inferInstance ≤ aeClosure P mΩ := by
  letI : MeasurableSpace Ω := mΩ
  have hGambient : Measurable[mΩ] G := hGm.mono hM le_rfl
  have hHcomp : Measurable[aeClosure P mΩ] H := by
    letI : MeasurableSpace Ω := aeClosure P mΩ
    rw [measurable_pi_iff]
    intro x
    have hGx : Measurable[mΩ] (fun ω => G ω x) :=
      (measurable_pi_apply x).comp hGambient
    have hHx : (fun ω => H ω x) =ᵐ[P] (fun ω => G ω x) :=
      hHG.mono (fun ω hω => congrFun hω x)
    have hle : MeasurableSpace.comap (fun ω => H ω x) inferInstance ≤
        aeClosure P mΩ := by
      letI : MeasurableSpace Ω := mΩ
      exact LQGMetric.DFGPS.L219.comap_le_aeClosure_of_ae_eq hGx hHx
    exact measurable_iff_comap_le.mpr hle
  have hgcomp : Measurable[aeClosure P mΩ] g :=
    hg.mono (le_aeClosure _) le_rfl
  letI : MeasurableSpace Ω := aeClosure P mΩ
  have hRm : Measurable (fun ω => restrictTo O (g ω) - ofFunOn O (H ω)) :=
    ((measurable_restrictTo O).comp hgcomp).sub
      (markov_measurable_ofFunOn O H hHc hHcomp)
  exact hRm.comap_le

/-- A measurable ambient version of the exterior residual. -/
theorem l7a_exists_measurable_residual_version {d : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → DistRd d) (hg : Measurable g)
    (O : TopologicalSpace.Opens (Rd d))
    (M : MeasurableSpace Ω) (hM : M ≤ mΩ)
    (H G : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) O)
    (hGm : Measurable[M] G) (hHG : H =ᵐ[P] G) :
    ∃ R : Ω → DistOn O, Measurable[mΩ] R ∧
      (fun ω => restrictTo O (g ω) - ofFunOn O (H ω)) =ᵐ[P] R := by
  letI : MeasurableSpace Ω := mΩ
  exact LQGMetric.exists_ae_eq_measurable_of_aeDeterminedSigma (G := mΩ)
    (l7a_residual_comap_le_aeClosure P g hg O M hM H G hHc hGm hHG)

/-- The residual can be chosen measurable in any sigma algebra that already
measures the field and the pointwise harmonic version. In particular, the
full field sigma algebra suffices. -/
theorem l7a_exists_residual_version_in_sigma {d : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (N : MeasurableSpace Ω)
    (g : Ω → DistRd d) (hgN : Measurable[N] g)
    (O : TopologicalSpace.Opens (Rd d))
    (M : MeasurableSpace Ω) (hMN : M ≤ N)
    (H G : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) O)
    (hGm : Measurable[M] G) (hHG : H =ᵐ[P] G) :
    ∃ R : Ω → DistOn O, Measurable[N] R ∧
      (fun ω => restrictTo O (g ω) - ofFunOn O (H ω)) =ᵐ[P] R := by
  letI : MeasurableSpace Ω := mΩ
  have hGN : Measurable[N] G := hGm.mono hMN le_rfl
  have hHcomp : Measurable[aeClosure P N] H := by
    letI : MeasurableSpace Ω := aeClosure P N
    rw [measurable_pi_iff]
    intro x
    have hGx : Measurable[N] (fun ω => G ω x) :=
      (measurable_pi_apply x).comp hGN
    have hHx : (fun ω => H ω x) =ᵐ[P] (fun ω => G ω x) :=
      hHG.mono (fun ω hω => congrFun hω x)
    have hle : MeasurableSpace.comap (fun ω => H ω x) inferInstance ≤
        aeClosure P N := by
      letI : MeasurableSpace Ω := mΩ
      exact LQGMetric.DFGPS.L219.comap_le_aeClosure_of_ae_eq hGx hHx
    exact measurable_iff_comap_le.mpr hle
  have hgcomp : Measurable[aeClosure P N] g :=
    hgN.mono (le_aeClosure _) le_rfl
  have hRcomp : Measurable[aeClosure P N]
      (fun ω => restrictTo O (g ω) - ofFunOn O (H ω)) := by
    letI : MeasurableSpace Ω := aeClosure P N
    exact ((measurable_restrictTo O).comp hgcomp).sub
      (markov_measurable_ofFunOn O H hHc hHcomp)
  exact LQGMetric.exists_ae_eq_measurable_of_aeDeterminedSigma (G := N)
    hRcomp.comap_le

end HigherDimLQGMetric
