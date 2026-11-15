/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField2Hull
import InteractingSLE.Frozen.Spec.IsTranslateAddConst

/-!
# GW2's open lines: two centrings of a field and of its angle translate agree

Packet PROVE-GW2-STAGEMEAN, R120 round. The kernel union mean is stated for the angle field `Xθ = X + θχ` centred by
the bounded harmonic extension of the angle-`θ` flow-line data; RELDET's launch kernel for `X` centred by the bounded
harmonic extension of the launch data. Both centred fields are zero-boundary GFFs under the same measure, hence equal:

* **`centredField_translate_eq`**: if `Xθ ω = X ω + c` (as `IsTranslateAddConst 0 c`) and both `centredField Xθ u₁` and
  `centredField X u₂` are zero-boundary GFFs, they are equal at every sample (their difference is a deterministic
  distribution with mean zero).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW2Omx

open WholeField

/-- **Two centrings of a field and of its constant translate that are both zero-boundary GFFs agree.** -/
theorem centredField_translate_eq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X Xθ : Ω → DistOn upperHalfPlaneOpens} {c : ℝ} (htr : ∀ ω, IsTranslateAddConst 0 c (X ω) (Xθ ω))
    {u₁ u₂ : ℂ → ℝ} (h₁ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField Xθ u₁) Q)
    (h₂ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₂) Q) :
    centredField Xθ u₁ = centredField X u₂ := by
  have hshift : ∀ ω φ, Xθ ω φ = X ω φ + c * ∫ z, φ z := fun ω φ =>
    htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
  set d : TestOn upperHalfPlaneOpens → ℝ := fun ψ =>
    c * (∫ z, ψ z) - smoothDist upperHalfPlaneOpens u₁ ψ + smoothDist upperHalfPlaneOpens u₂ ψ with hd
  have e : ∀ ω ψ, centredField Xθ u₁ ω ψ = centredField X u₂ ω ψ + d ψ := by
    intro ω ψ
    simp only [centredField, sub_apply, hshift, hd]
    ring
  have hd0 : ∀ ψ, d ψ = 0 := by
    intro ψ
    have i₁ := (h₁.process.gaussian.hasGaussianLaw_eval ψ).integrable
    have i₂ := (h₂.process.gaussian.hasGaussianLaw_eval ψ).integrable
    have c₁ := h₁.process.centered ψ
    have c₂ := h₂.process.centered ψ
    have hP : IsProbabilityMeasure Q := h₁.process.gaussian.isProbabilityMeasure
    have h := integral_sub i₁ i₂
    rw [c₁, c₂, sub_zero] at h
    have e' : (fun ω => centredField Xθ u₁ ω ψ - centredField X u₂ ω ψ) = fun _ => d ψ := by
      funext ω
      rw [e ω ψ]
      ring
    simp only [e', integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact h
  funext ω
  ext ψ
  rw [e ω ψ, hd0 ψ, add_zero]

end InteractingSLE.Theorem14.GW2Omx
