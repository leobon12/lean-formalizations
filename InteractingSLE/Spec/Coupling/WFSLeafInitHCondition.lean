/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafInitHGerm
import LQGMetric.Field.MarkovIndep

/-!
# Conditioning a driving evolution on an initial event

The full Brownian future is independent of the initial sigma algebra.
Conditioning on an initial event therefore preserves its finite-dimensional
laws, filtered increment independence, and a.e. path properties.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open QuantumZipper.StrongMarkov Sec2.Restart

/-- Conditioning on a nonnull event at time zero preserves filtered Brownian
motion. Almost sure path continuity suffices. -/
theorem isFilteredBrownianReal_cond_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓕 B P) {A : Set Ω}
    (hA : MeasurableSet[𝓕 0] A) (hPA : P A ≠ 0) :
    IsFilteredBrownianReal 𝓕 B (P[|A]) := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  have : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hPA
  have hBm : ∀ t, Measurable (B t) := hB.measurable'
  refine ⟨⟨IsPreBrownianReal.mk' fun I => ?_, cond_absolutelyContinuous.ae_le hB.1.cont⟩,
    hB.2.1, fun s t hst => indep_cond (𝓕.le s) (hB.2.2 s t hst)
      (𝓕.mono (zero_le : (0 : ℝ≥0) ≤ s) _ hA)⟩
  let U : Ω → (I → ℝ) := fun ω i => B i ω - B 0 ω
  have hUm : Measurable U := measurable_pi_iff.2 fun i => (hBm i).sub (hBm 0)
  have hUle : MeasurableSpace.comap U inferInstance ≤
      MeasurableSpace.comap (smPath B (fun _ => 0)) MeasurableSpace.pi := by
    have hm : Measurable[MeasurableSpace.comap (smPath B (fun _ => 0))
        MeasurableSpace.pi] U := by
      apply (@measurable_pi_iff Ω I (fun _ => ℝ)
        (MeasurableSpace.comap (smPath B (fun _ => 0)) MeasurableSpace.pi) _ _).2
      intro i
      simpa only [smPath, smShift, zero_add, U, Function.comp_def] using
        (measurable_pi_apply (i : ℝ≥0)).comp (comap_measurable (smPath B (fun _ => 0)))
    exact hm.comap_le
  have hind := indep_of_indep_of_le_left (indep_future hB 0).symm hUle
  have hmap : (P[|A]).map U = P.map U := by
    have hr := LQGMetric.MarkovIndep.map_restrict_eq_of_indep hUm hind hA
    change (P.restrict A).map U = P A • P.map U at hr
    rw [ProbabilityTheory.cond, Measure.map_smul, hr, smul_smul,
      ENNReal.inv_mul_cancel hPA (measure_ne_top P A), one_smul]
    exact hUm.aemeasurable
  have he : U =ᵐ[P] fun ω => I.restrict (B · ω) := by
    filter_upwards [hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
    funext i
    exact sub_eq_self.2 hω
  refine ⟨((Finset.measurable_restrict I).comp (measurable_pi_iff.2 hBm)).aemeasurable, ?_⟩
  rw [← Measure.map_congr (cond_absolutelyContinuous.ae_le he), hmap,
    Measure.map_congr he, (hB.1.toIsPreBrownianReal.hasLaw I).map_eq]

/-- An integrated evolution remains an evolution under conditioning on a
nonnull event in its initial filtration. The coordinates are unchanged. -/
theorem isIntegratedSLEEvolution_cond_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
    {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {A : Set Ω} (hA : MeasurableSet[𝓕 0] A) (hPA : P A ≠ 0) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR (P[|A]) 𝓕 W VL VR B ζ :=
  ⟨isFilteredBrownianReal_cond_initial hE.1 hA hPA, hE.2.1, hE.2.2.1,
    hE.2.2.2.1, cond_absolutelyContinuous.ae_le hE.2.2.2.2⟩

end InteractingSLE.WFS
