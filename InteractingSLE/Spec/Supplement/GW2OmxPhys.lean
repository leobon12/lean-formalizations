/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxInst
import InteractingSLE.Spec.Sec5.Aux61SlitVChart
import InteractingSLE.Spec.Coupling.Assembly11BProvider

/-!
# GW2's open lines: the launch mean read from a physical harmonic representative

Packet PROVE-GW2-STAGEMEAN, R120 round (physical form). For a conformal chart `cL` with a continuous harmonic lift
and a distribution `T` with a harmonic representative `wP` off `B`, the launch transport `cL(T + u₀) − u'` has, off
the launch image of `B`, the harmonic representative `(wP + u₀)∘cL⁻¹ + k · lift∘cL⁻¹ − u'`:

* **`launch_rep`** (deterministic): harmonicity on `chartPre cL (ℍ ∖ B)` and the pairing identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW2Omx

open Restart.MarkovChart

/-- **The launch transport of a physical harmonic representative.** -/
theorem launch_rep {cL : Chart} (hconf : cL.IsConformal) (hlc : ContinuousOn cL.2.2 cL.dom)
    (hlh : InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom) {B : Set ℂ} {T : DistOn upperHalfPlaneOpens}
    {wP : ℂ → ℝ} (hwP : InnerProductSpace.HarmonicOnNhd wP (H \ B))
    (hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B → T φ = ∫ z, wP z * φ z)
    {u₀ u' : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu' : InnerProductSpace.HarmonicOnNhd u' H)
    (k : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun z => wP (cL.2.1 z) + u₀ (cL.2.1 z) + k * cL.2.2 (cL.2.1 z) - u' z)
        (chartPre cL (H \ B)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ chartPre cL (H \ B) →
        (Chart.chartTransport hconf 1 0 k (T + smoothDist upperHalfPlaneOpens u₀) -
          smoothDist upperHalfPlaneOpens u') φ =
          ∫ z, (wP (cL.2.1 z) + u₀ (cL.2.1 z) + k * cL.2.2 (cL.2.1 z) - u' z) * φ z := by
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hu'c : ContinuousOn u' H := fun z hz => (hu' z hz).1.continuousAt.continuousWithinAt
  have hwPc : ContinuousOn wP (H \ B) := fun z hz => (hwP z hz).1.continuousAt.continuousWithinAt
  refine ⟨fun z hz => ?_, fun φ hφ => ?_⟩
  · have hzH : z ∈ H := hz.1
    have hdom : cL.2.1 z ∈ cL.dom := hconf.inv_mem_dom hzH
    have hf : AnalyticAt ℂ cL.2.1 z :=
      hconf.1.analyticAt (QuantumZipper.isOpen_H.mem_nhds hzH)
    have h1 := QuantumZipper.FieldLawler.fl_harmonicAt_comp hf (hwP _ hz.2)
    have h2 := QuantumZipper.FieldLawler.fl_harmonicAt_comp hf (hu₀ _ (hconf.2.1 hzH))
    have h3 := QuantumZipper.FieldLawler.fl_harmonicAt_comp hf (hlh _ hdom)
    have h3' : InnerProductSpace.HarmonicAt (fun x => k * cL.2.2 (cL.2.1 x)) z := by
      have he : (k • (cL.2.2 ∘ cL.2.1)) = (fun x => k * cL.2.2 (cL.2.1 x)) := by
        funext x
        rfl
      simpa only [he] using h3.const_smul (c := k)
    exact ((h1.add h2).add h3').sub (hu' z hzH)
  · have hOH : chartPre cL (H \ B) ⊆ H := chartPre_subset_H _ _
    have himg : cL.2.1 '' chartPre cL (H \ B) ⊆ H \ B := by
      rw [image_chartPre hconf]
      exact inter_subset_left
    have hmc : ContinuousOn (fun z => wP z + u₀ z) (cL.2.1 '' chartPre cL (H \ B)) :=
      (hwPc.add (hu₀c.mono sdiff_subset)).mono himg
    have hT' : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ cL.2.1 '' chartPre cL (H \ B) →
        (T + smoothDist upperHalfPlaneOpens u₀) ψ = ∫ z, (wP z + u₀ z) * ψ z := by
      intro ψ hψ
      have hψ' : tsupport ψ ⊆ H \ B := hψ.trans himg
      have i1 := WholeField.integrable_mul_testOn hwPc ψ hψ'
      have i2 := WholeField.integrable_mul_testOn hu₀c ψ ψ.tsupport_subset
      rw [add_apply, hT ψ hψ', Coupling.smoothDist_apply_eq hu₀c ψ, ← integral_add i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [add_mul]
    have hmain := Sec5.Aux61SlitV.chartTransport_apply_eq_integral_of_subset hconf hlc hOH hmc hT' 0 k hφ
    have hlic : ContinuousOn (fun z => cL.2.2 (cL.2.1 z)) H := hconf.continuousOn_lift_inv hlc
    have hwic : ContinuousOn (fun z => wP (cL.2.1 z) + u₀ (cL.2.1 z)) (chartPre cL (H \ B)) :=
      hmc.comp (hconf.1.continuousOn.mono hOH) (mapsTo_image _ _)
    have i1 := WholeField.integrable_mul_testOn hwic φ hφ
    have i2 := WholeField.integrable_mul_testOn (hlic.mono hOH) φ hφ
    have i3 := WholeField.integrable_mul_testOn hu'c φ φ.tsupport_subset
    rw [sub_apply, hmain, Coupling.smoothDist_apply_eq hu'c φ, ← integral_sub _ i3]
    · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      ring
    · have i2' := i2.const_mul k
      refine (i1.add i2').congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply]
      ring

end InteractingSLE.Theorem14.GW2Omx
