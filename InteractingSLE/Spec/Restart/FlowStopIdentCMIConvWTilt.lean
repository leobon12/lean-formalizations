/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWDirichlet

/-! # The local-set Cameron–Martin theorem for the explicit comparison cutoff -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The existing local-set tilt applies to the exact cutoff and arbitrary
dominated source approximation supplied by the comparison statement. -/
theorem isLocalSet_withDensity_cmiCut
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : IsLocalSet A h P) (hh : Measurable h) (F : CMCut)
    {s : ℕ → TestOn upperHalfPlaneOpens} (hs : ∀ n z, |s n z| ≤ |F.src z|)
    (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z)))
    {Λ : Ω → ℝ} (hΛ : ∀ᵐ ω ∂P, Tendsto (fun n => h ω (s n)) atTop (𝓝 (Λ ω)))
    {k : ℝ} (hk : 0 < k)
    (hprob : IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))))
    {q : ℂ → ℝ} (hq : InnerProductSpace.HarmonicOnNhd q H) :
    IsLocalSet A (fun ω => h ω + smoothDist upperHalfPlaneOpens (fun z => q z - F.f z))
      (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))) := by
  obtain ⟨a, ha, hcov⟩ := F.exists_covCauchy_subseq hs hslim
  let ℓ : DistOn upperHalfPlaneOpens → ℝ := fun T => limUnder atTop fun n => T (s (a n))
  have hℓ : Measurable ℓ := by
    have hm : ∀ n, StronglyMeasurable fun T : DistOn upperHalfPlaneOpens => T (s (a n)) :=
      fun n => ((LQGMetric.measurable_distOn_apply (s (a n)))).stronglyMeasurable
    exact (StronglyMeasurable.limUnder hm).measurable
  have heq : ∀ᵐ ω ∂P, ℓ (h ω) = Λ ω := hΛ.mono fun ω h => (h.comp ha.tendsto_atTop).limUnder_eq
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => h ω (s (a n))) atTop (𝓝 (ℓ (h ω))) := by
    filter_upwards [hΛ, heq] with ω h he
    rw [he]
    exact h.comp ha.tendsto_atTop
  have hdens : (fun ω => ENNReal.ofReal (Real.exp (-ℓ (h ω) + Real.log k))) =ᵐ[P]
      fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)) := by
    filter_upwards [heq] with ω he
    rw [he, Real.exp_add, Real.exp_log hk]
    congr 1
    exact mul_comm _ _
  have hZ : ∫⁻ ω, ENNReal.ofReal (Real.exp (-ℓ (h ω) + Real.log k)) ∂P = 1 := by
    rw [lintegral_congr_ae hdens]
    have h := hprob.measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  have htilt := LocalExt.IsLocalSet.withDensity_exp_neg hloc hh hcov hℓ hconv hZ
    (fun U hU g => F.tendsto_integral_mul_eq_shift_lapTest
      (fun n z => hs (a n) z) (fun z => (hslim z).comp ha.tendsto_atTop) hq U hU g)
  rwa [withDensity_congr_ae hdens] at htilt

end InteractingSLE.Restart.FlowStopIdentCMI
