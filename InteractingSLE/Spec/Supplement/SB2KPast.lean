/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# A frozen quantity with a measurable version on a conull event is measurable for the past, up to null sets

Packet PROVE-T14-SB2FIN5 (SB2(1)'s past-measurable entry point). K2 needs the entry point `m` of SB2(1) as a function
measurable for the retained past `𝒢 = pastSigma k`. The entry point is a function of the run (so it is frozen under
the regular conditional laws given `𝒢`), but it is only known to agree with an ambient-measurable function on a conull
event (where the launched pieces are regular). This file closes that gap abstractly:

* **`exists_measurable_eq_of_frozen`**: if `g` agrees almost surely on `F` with a measurable `G`, and for almost every
  `ω₀ ∈ F`, under the regular conditional law given `𝒢` at `ω₀`, almost surely `ω ∈ F` and `g ω = g ω₀`, then
  `m' = tan (P[arctan ∘ G | 𝒢])` is `𝒢`-measurable and equals `g` almost surely on `F` (the conditional expectation is
  the kernel integral, `condExp_ae_eq_integral_condExpKernel`, and the integrand is kernel-almost surely the constant
  `arctan (g ω₀)`).

Measure theory only; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace InteractingSLE.Theorem14.SB.Lv

theorem measurable_real_tan : Measurable Real.tan := by
  have e : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
  rw [e]
  exact Real.measurable_sin.div Real.measurable_cos

/-- **A frozen quantity with a measurable version on a conull event has a version measurable for `𝒢`.** -/
theorem exists_measurable_eq_of_frozen {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {g G : Ω → ℝ}
    (hG : Measurable G) {F : Set Ω} (hgG : ∀ᵐ ω ∂P, ω ∈ F → G ω = g ω)
    (hfr : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ F ∧ g ω = g ω₀) :
    ∃ m' : Ω → ℝ, Measurable[𝒢] m' ∧ ∀ᵐ ω ∂P, ω ∈ F → m' ω = g ω := by
  set f : Ω → ℝ := fun ω => Real.arctan (G ω) with hf
  have hfm : Measurable f := Real.continuous_arctan.measurable.comp hG
  have hfi : Integrable f P := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (Real.pi / 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  refine ⟨fun ω => Real.tan ((P[f | 𝒢]) ω),
    measurable_real_tan.comp stronglyMeasurable_condExp.measurable, ?_⟩
  filter_upwards [condExp_ae_eq_integral_condExpKernel h𝒢 hfi, hfr,
    Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hgG] with ω₀ hc hfr₀ hk₀ hF
  have hint : ∫ y, f y ∂condExpKernel P 𝒢 ω₀ = Real.arctan (g ω₀) := by
    have hae : f =ᵐ[condExpKernel P 𝒢 ω₀] fun _ => Real.arctan (g ω₀) := by
      filter_upwards [hfr₀ hF, hk₀] with ω hω hk
      simp only [hf, hk hω.1, hω.2]
    rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]
  show Real.tan ((P[f | 𝒢]) ω₀) = g ω₀
  rw [hc, hint, Real.tan_arctan]

end InteractingSLE.Theorem14.SB.Lv
