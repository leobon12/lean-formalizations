/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.SubdomainLaw
import InteractingSLE.Spec.Sec7.MarkedProp39

/-!
# Equal-variance comparison when the enlarged kernel is known on an event

PROVE-SIDE-COLLAR2. The filled-pocket comparison needs the original
marked kernel only for tests supported in the selected component.
Localize those scalar variables to that measurable support event and
reuse the existing Gaussian tower argument.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE.Sec7.SideC13

open LocalSets

variable {Ω : Type*} {𝒢 𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Extend an eventwise centered Gaussian characteristic identity to a
global identity by setting the variable and variance to zero off the event. -/
theorem condExp_exp_indicator_of_on (h𝒢 : 𝒢 ≤ mΩ) {E : Set Ω}
    (hE : MeasurableSet[𝒢] E) {X v : Ω → ℝ} (hX : Measurable X)
    (hc : ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * (X ω : ℂ)) | 𝒢] ω =
        ((Real.exp (-(1 / 2) * v ω) : ℝ) : ℂ)) :
    P[fun ω => Complex.exp (Complex.I * ((E.indicator X ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * E.indicator v ω) : ℝ) : ℂ) := by
  have hEm : MeasurableSet E := h𝒢 _ hE
  have hFi := GFF.integrable_exp_I_mul hX (P := P)
  have hOne : Integrable (Eᶜ.indicator fun _ : Ω => (1 : ℂ)) P :=
    (integrable_const 1).indicator hEm.compl
  have he : (fun ω => Complex.exp (Complex.I * ((E.indicator X ω : ℝ) : ℂ))) =
      E.indicator (fun ω => Complex.exp (Complex.I * (X ω : ℂ))) +
        Eᶜ.indicator (fun _ => (1 : ℂ)) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  rw [he]
  have hAdd := condExp_add (m := 𝒢) (hFi.indicator hEm) hOne
  have hInd := condExp_indicator (m := 𝒢) hFi hE
  have hConst : P[Eᶜ.indicator (fun _ : Ω => (1 : ℂ)) | 𝒢] = Eᶜ.indicator (fun _ => 1) :=
    condExp_of_stronglyMeasurable h𝒢 (stronglyMeasurable_const.indicator hE.compl) hOne
  filter_upwards [hAdd, hInd, hc] with ω hAddω hIndω hcω
  rw [hAddω, Pi.add_apply, hIndω, hConst]
  by_cases hω : ω ∈ E
  · simpa only [indicator_of_mem hω,
      indicator_of_notMem (show ω ∉ Eᶜ from fun h => h hω), add_zero] using hcω hω
  · simp [hω]

/-- The equal-variance Gaussian tower comparison needs the upper kernel
only on the lower-record event under consideration. -/
theorem ae_cos_eq_one_of_condCharFun_on (h𝒢𝒦 : 𝒢 ≤ 𝒦) (h𝒦 : 𝒦 ≤ mΩ)
    {X M M' v : Ω → ℝ} (hX : Measurable X)
    (hM : Measurable[𝒢] M) (hM' : Measurable[𝒦] M')
    (hc : P[fun ω => Complex.exp (Complex.I * ((X ω - M ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * v ω) : ℝ) : ℂ))
    {E : Set Ω} (hE : MeasurableSet[𝒢] E)
    (hc' : ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * ((X ω - M' ω : ℝ) : ℂ)) | 𝒦] ω =
        ((Real.exp (-(1 / 2) * v ω) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, ω ∈ E → Real.cos (M' ω - M ω) = 1 := by
  have h𝒢 := h𝒢𝒦.trans h𝒦
  have hEm := h𝒢 _ hE
  have hLo := condExp_exp_indicator_of_on h𝒢 hE (hX.sub (hM.mono h𝒢 le_rfl))
    (hc.mono fun _ h _ => h)
  have hHi := condExp_exp_indicator_of_on h𝒦 (h𝒢𝒦 _ hE)
    (hX.sub (hM'.mono h𝒦 le_rfl)) hc'
  have hSub : ∀ f g : Ω → ℝ, E.indicator (f - g) =
      fun ω => E.indicator f ω - E.indicator g ω := fun f g => by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  rw [hSub] at hLo hHi
  have hCos := LocalSets.ae_cos_eq_one_of_condCharFun h𝒢𝒦 h𝒦
    (hX.indicator hEm) (hM.indicator hE) (hM'.indicator (h𝒢𝒦 _ hE))
    hLo hHi hE (ae_of_all _ fun _ _ => rfl)
  filter_upwards [hCos] with ω hω hωE
  simpa only [indicator_of_mem hωE] using hω hωE

/-- Distributional comparison when the upper residual law is available only
on the lower-record support event. -/
theorem ae_apply_eq_on_of_upper_condCharFun (h𝒢𝒦 : 𝒢 ≤ 𝒦) (h𝒦 : 𝒦 ≤ mΩ)
    {h M M' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (hM : Measurable[𝒢] M) (hM' : Measurable[𝒦] M')
    {U : Ω → Set ℂ}
    (hc : IsCondZeroBoundaryGFF P 𝒢 U fun ω => h ω - M ω)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) {E : Set Ω}
    (hE : MeasurableSet[𝒢] E)
    (hc' : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * ((h ω (c • φ) - M' ω (c • φ) : ℝ) : ℂ)) | 𝒦] ω =
        ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (U ω) (c • φ) (c • φ)) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, ω ∈ E → M ω φ = M' ω φ := by
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, ω ∈ E →
      Real.cos (((n : ℝ) + 1)⁻¹ * (M' ω φ - M ω φ)) = 1 := by
    intro n
    let c : ℝ := ((n : ℝ) + 1)⁻¹
    have hLo := hc (c • φ)
    simp only [sub_apply] at hLo
    have hCos := ae_cos_eq_one_of_condCharFun_on h𝒢𝒦 h𝒦
      ((LQGMetric.measurable_distOn_apply (c • φ)).comp hh)
      ((LQGMetric.measurable_distOn_apply (c • φ)).comp hM)
      ((LQGMetric.measurable_distOn_apply (c • φ)).comp hM') hLo hE (hc' c)
    filter_upwards [hCos] with ω hω hωE
    simpa only [map_smul, smul_eq_mul, Function.comp_apply, c, ← mul_sub] using hω hωE
  filter_upwards [ae_all_iff.2 hn] with ω hω hωE
  exact (sub_eq_zero.1 (eq_zero_of_forall_cos_eq_one (fun n => hω n hωE))).symm

end InteractingSLE.Sec7.SideC13
