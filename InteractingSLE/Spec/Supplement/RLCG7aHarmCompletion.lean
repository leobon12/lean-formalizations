/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aHarmIntegral
import Mathlib.MeasureTheory.Measure.Trim

/-!
# Removing the measurability strengthening by completing the measure

Packet PROVE-G7A-MEANIDENT. Integrable sections need only be almost everywhere
measurable. They are measurable for the completed parameter measure. Trimming
back preserves both their integrability and their integrals, so the harmonic
integration theorem has no additional measurability hypothesis.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace Filter Topology

namespace InteractingSLE.Restart.FlowLocalityGen

/-- A pointwise finite integral of nonnegative harmonic sections is harmonic.
Parameter measurability is supplied by integrability, with no joint
measurability or common domination assumption in the statement. -/
theorem harmonicOnNhd_integral_nonneg {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {U : Set ℂ} (hU : IsOpen U) {k : A → ℂ → ℝ}
    (hk : ∀ a, HarmonicOnNhd (k a) U) (h0 : ∀ a, ∀ z ∈ U, 0 ≤ k a z)
    (hi : ∀ z ∈ U, Integrable (fun a => k a z) μ) :
    HarmonicOnNhd (fun z => ∫ a, k a z ∂μ) U := by
  let f : ℂ → ℝ := fun z => ∫ a, k a z ∂μ
  change HarmonicOnNhd f U
  let m : MeasurableSpace A := inferInstance
  let m' : MeasurableSpace A :=
    inferInstanceAs (MeasurableSpace (NullMeasurableSpace A μ))
  let ν : @Measure A m' := μ.completion
  let _ : MeasurableSpace A := m
  have hmle : m ≤ m' := fun s hs => hs.nullMeasurableSet
  have htrim : ν.trim hmle = μ := by
    refine @Measure.ext A m (ν.trim hmle) μ ?_
    intro s hs
    rw [trim_measurableSet_eq hmle hs]
    rfl
  have hm' : ∀ z ∈ U, @Measurable A ℝ m' _ (fun a => k a z) := by
    intro z hz
    change NullMeasurable (fun a => k a z) μ
    exact (hi z hz).1.aemeasurable.nullMeasurable
  have hs : ∀ z ∈ U, AEStronglyMeasurable[m] (fun a => k a z) (ν.trim hmle) := by
    intro z hz
    simpa only [htrim] using (hi z hz).1
  have : SigmaFinite (ν.trim hmle) := by rw [htrim]; infer_instance
  let _ : MeasurableSpace A := m'
  have : SigmaFinite ν := SigmaFinite.of_trim hmle
  have hi' : ∀ z ∈ U, Integrable (fun a => k a z) ν := by
    intro z hz
    apply integrable_of_integrable_trim hmle
    simpa only [htrim] using hi z hz
  have hH := harmonicOnNhd_integral_nonneg_of_measurable (μ := ν) hU hk h0 hi' hm'
  have heq : EqOn (fun y => ∫ a, k a y ∂ν) f U := by
    intro y hy
    have e := integral_trim_ae hmle (hs y hy)
    rw [htrim] at e
    exact e
  intro z hz
  have hev : (fun y => ∫ a, k a y ∂ν) =ᶠ[𝓝 z] f := by
    filter_upwards [hU.mem_nhds hz] with y hy using heq hy
  exact (harmonicAt_congr_nhds hev).1 (hH z hz)

end InteractingSLE.Restart.FlowLocalityGen
