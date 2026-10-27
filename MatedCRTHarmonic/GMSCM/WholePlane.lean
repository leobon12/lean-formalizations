import MatedCRTHarmonic.GMSCM.DataProcessing
import LQGMetric.Field.CameronMartin
import LQGMetric.Papers.MQ.ZBCM

/-!
# Cameron–Martin density for whole-plane GFF mean-zero pairings

The source comparison begins with a smooth finite-energy cut-off of the logarithmic
singularity. This module records the Gaussian second moment of the existing whole-plane
Cameron–Martin density. The field is observed modulo additive constants here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory LQGMetric LQGMetric.MQ QuantumZipper.CameronMartin
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- Every real moment of the whole-plane Cameron–Martin density is Gaussian. -/
theorem cmDensity_pair0_moment (hh : IsWholePlaneGFF h P) (φ : TestC) (s : ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (cmDensity φ ξ) ^ s ∂(lawPair0 h P) =
      ENNReal.ofReal (Real.exp (s * (s - 1) * gradEnergy φ / 2)) := by
  let : IsProbabilityMeasure P := hh.gaussian.isProbabilityMeasure
  let X : TestC0 → Ω → ℝ := pairProc h
  let σ : TestC0 →₀ ℝ := Finsupp.single (cmTest0 φ) 1
  have hmeas : ∀ ψ : TestC0, Measurable (X ψ) := fun ψ =>
    (measurable_evalDist ψ.1).comp hh.measurable
  have hm := lintegral_rnDeriv_tilt_rpow hh.gaussian hmeas hh.centered σ s
  change (∫⁻ ω, (tiltMeasure X P σ).rnDeriv P ω ^ s ∂P) =
    ENNReal.ofReal (Real.exp (s * (s - 1) * covNorm X P σ / 2)) at hm
  rw [covNorm_cm hh φ] at hm
  rw [← hm, lawPair0]
  change (∫⁻ ξ, ENNReal.ofReal (cmDensity φ ξ) ^ s ∂(P.map (pair0 ∘ h))) = _
  rw [lintegral_map
    ((measurable_cmDensity φ).ennreal_ofReal.pow_const s)
    (measurable_pair0.comp hh.measurable)]
  have hD : Measurable fun ω => ((tiltDensity X P σ ω).toNNReal : ℝ≥0∞) :=
    (measurable_tiltDensity hh.gaussian hmeas σ).real_toNNReal.coe_nnreal_ennreal
  have hrn := Measure.rnDeriv_withDensity P hD
  refine lintegral_congr_ae ?_
  filter_upwards [hrn] with ω hω
  change ENNReal.ofReal (cmDensity φ (pair0 (h ω))) ^ s =
    ((tiltMeasure X P σ).rnDeriv P ω) ^ s
  rw [show tiltMeasure X P σ = P.withDensity fun ω =>
    ((tiltDensity X P σ ω).toNNReal : ℝ≥0∞) from rfl, hω,
    tiltDensity_cm hh φ ω]
  rfl

/-- The whole-plane Cameron–Martin density has Gaussian second moment. -/
theorem cmDensity_pair0_sq (hh : IsWholePlaneGFF h P) (φ : TestC) :
    ∫⁻ ξ, ENNReal.ofReal (cmDensity φ ξ) ^ (2 : ℝ) ∂(lawPair0 h P) =
      ENNReal.ofReal (Real.exp (gradEnergy φ)) := by
  rw [cmDensity_pair0_moment hh φ 2]
  norm_num

/-- The second moment is finite, as required for a Hölder exponent of two. -/
theorem cmDensity_pair0_sq_finite (hh : IsWholePlaneGFF h P) (φ : TestC) :
    ∫⁻ ξ, ENNReal.ofReal (cmDensity φ ξ) ^ (2 : ℝ) ∂(lawPair0 h P) < ⊤ := by
  rw [cmDensity_pair0_sq hh φ]
  exact ENNReal.ofReal_lt_top

/-- The Cameron–Martin law comparison after any measurable observation of the
mean-zero pairings. Its density is the conditional expectation represented by
the Radon–Nikodym derivative; it has a finite second moment. -/
theorem cm_observation_comparison {S : Type*} [MeasurableSpace S]
    (hh : IsWholePlaneGFF h P) (φ : TestC)
    (observe : (TestC0 → ℝ) → S) (hobserve : Measurable observe) :
    ∃ M : S → ℝ≥0∞, Measurable M ∧
      (lawPair0 (fun ω => addFun (h ω) (testCont φ)) P).map observe =
        ((lawPair0 h P).map observe).withDensity M ∧
      ∫⁻ x, M x ^ (2 : ℝ) ∂((lawPair0 h P).map observe) < ⊤ := by
  let : IsProbabilityMeasure P := hh.gaussian.isProbabilityMeasure
  let μ : Measure (TestC0 → ℝ) :=
    lawPair0 (fun ω => addFun (h ω) (testCont φ)) P
  let ν : Measure (TestC0 → ℝ) := lawPair0 h P
  have hμprob : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pair0_addFun hh φ).aemeasurable).2 inferInstance
  let : IsProbabilityMeasure μ := hμprob
  let : IsFiniteMeasure μ := inferInstance
  have hνprob : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pair0_comp hh).aemeasurable).2 inferInstance
  let : IsProbabilityMeasure ν := hνprob
  have heq : μ = ν.withDensity (fun ξ => ENNReal.ofReal (cmDensity φ ξ)) :=
    lawPair0_addFun_eq_withDensity hh φ
  have hac : μ ≪ ν := by
    rw [heq]
    exact withDensity_absolutelyContinuous _ _
  refine ⟨(μ.map observe).rnDeriv (ν.map observe),
    Measure.measurable_rnDeriv _ _, ?_, ?_⟩
  · exact (Measure.withDensity_rnDeriv_eq _ _ (hac.map hobserve)).symm
  · exact map_withDensity_sq_finite
      (ENNReal.measurable_ofReal.comp (measurable_cmDensity φ)) heq
      (cmDensity_pair0_sq_finite hh φ) hobserve

/-- Reverse comparison: the unshifted law has an L² density with respect to
the shifted law after every measurable observation. -/
theorem cm_observation_comparison_reverse {S : Type*} [MeasurableSpace S]
    (hh : IsWholePlaneGFF h P) (φ : TestC)
    (observe : (TestC0 → ℝ) → S) (hobserve : Measurable observe) :
    ∃ M : S → ℝ≥0∞, Measurable M ∧
      (lawPair0 h P).map observe =
        ((lawPair0 (fun ω => addFun (h ω) (testCont φ)) P).map observe).withDensity M ∧
      ∫⁻ x, M x ^ (2 : ℝ) ∂
        ((lawPair0 (fun ω => addFun (h ω) (testCont φ)) P).map observe) < ⊤ := by
  let : IsProbabilityMeasure P := hh.gaussian.isProbabilityMeasure
  let μ : Measure (TestC0 → ℝ) :=
    lawPair0 (fun ω => addFun (h ω) (testCont φ)) P
  let ν : Measure (TestC0 → ℝ) := lawPair0 h P
  have hμprob : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pair0_addFun hh φ).aemeasurable).2 inferInstance
  let : IsProbabilityMeasure μ := hμprob
  have hνprob : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pair0_comp hh).aemeasurable).2 inferInstance
  let : IsProbabilityMeasure ν := hνprob
  let ρ : (TestC0 → ℝ) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (cmDensity φ ξ)
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (measurable_cmDensity φ)
  have hρpos : ∀ ξ, ρ ξ ≠ 0 := fun ξ =>
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hρtop : ∀ ξ, ρ ξ ≠ ⊤ := fun ξ => ENNReal.ofReal_ne_top
  have heq : μ = ν.withDensity ρ := lawPair0_addFun_eq_withDensity hh φ
  have hνμ : ν ≪ μ := by
    rw [heq]
    exact withDensity_absolutelyContinuous' hρ.aemeasurable
      (Filter.Eventually.of_forall hρpos)
  have hneg : ∫⁻ ξ, ρ ξ ^ (-1 : ℝ) ∂ν < ⊤ := by
    rw [cmDensity_pair0_moment hh φ (-1)]
    exact ENNReal.ofReal_lt_top
  have h2 : ∫⁻ ξ, (ν.rnDeriv μ ξ) ^ (2 : ℝ) ∂μ < ⊤ :=
    inverse_withDensity_sq_finite hρ hρpos hρtop heq hneg
  have hL2 : MemLp (fun ξ => (ν.rnDeriv μ ξ).toReal) 2 μ :=
    rnDeriv_memLp_two_of_sq_finite h2
  refine ⟨(ν.map observe).rnDeriv (μ.map observe),
    Measure.measurable_rnDeriv _ _, ?_, ?_⟩
  · exact (Measure.withDensity_rnDeriv_eq _ _ (hνμ.map hobserve)).symm
  · exact rnDeriv_map_sq_finite hνμ hobserve hL2

end MatedCRTHarmonic.GMSCM
