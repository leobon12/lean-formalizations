/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewLawUnion

/-!
# Forgetting the exterior germs after the retained mean is identified

The marked Gaussian union law descends to the retained histories once its mean
is measurable from those histories. The proof uses the landed cross-conditioning
tower lemma, and then Mathlib's regular conditional kernel integral identity.
The displayed mean identity is a mathematical input, not asserted proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.SewLaw

open LocalSets

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens}
  {A : Ω → Set ℂ}

omit [StandardBorelSpace Ω] in
/-- The joined germ/history Gaussian identity descends to the histories on
every retained event where the germ mean equals the specified retained mean. -/
theorem ae_retained_cexp_of_mean
    (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hA : Measurable[𝒢.1, hittingSigma] A)
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝒢.1 A X P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (φ : TestOn upperHalfPlaneOpens) {D : Set Ω} (hD : MeasurableSet[𝒢.1] D)
    {m : Ω → ℝ} (hm : Measurable[𝒢.1] m)
    (hmean : ∀ᵐ ω ∂P, ω ∈ D →
      P[fun ω' => X ω' φ | germSigma A X ⊔ 𝒢.1] ω = m ω) :
    ∀ᵐ ω ∂P, ω ∈ D →
      P[fun ω' => Complex.exp (Complex.I * (X ω' φ : ℂ)) | 𝒢.1] ω =
        Complex.exp (Complex.I * (m ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov
            (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) := by
  have hAm := hA.mono 𝒢.2 le_rfl
  obtain ⟨M, -, hM₁, hM₂⟩ :=
    WholeField.exists_condExp_germSigma_history hX hAm 𝒢.2 hloc hAc φ
  have hG : germSigma A X ⊔ 𝒢.1 ≤ mΩ :=
    sup_le (germSigma_le hAm hX.measurable) 𝒢.2
  have hXi : Integrable (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX.measurable)
  have hv : Measurable[𝒢.1] fun ω =>
      zeroGFFTestCov (H \ relClosureH (A ω)) φ φ :=
    (measurable_zeroGFFTestCov_compl φ φ).comp hA
  have hR : StronglyMeasurable[𝒢.1] fun ω =>
      Complex.exp (Complex.I * (m ω : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov
          (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) := by
    apply Measurable.stronglyMeasurable
    exact (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp hm))).mul
        (Complex.measurable_ofReal.comp
          (Real.measurable_exp.comp (measurable_const.mul hv)))
  apply Sec5.CrossCond.ae_condExp_eq_of_le_of_ae le_sup_right hG hD hXi hR
  filter_upwards [hM₁, hM₂, hmean] with ω he₁ he₂ he hωD
  rw [← he₂, he₁, he hωD]

/-- The same Gaussian law as an integral under the actual retained conditional
kernel. The field integrand is measurable and bounded in norm by one. -/
theorem ae_retained_kernel_cexp_of_mean
    (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hA : Measurable[𝒢.1, hittingSigma] A)
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝒢.1 A X P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (φ : TestOn upperHalfPlaneOpens) {D : Set Ω} (hD : MeasurableSet[𝒢.1] D)
    {m : Ω → ℝ} (hm : Measurable[𝒢.1] m)
    (hmean : ∀ᵐ ω ∂P, ω ∈ D →
      P[fun ω' => X ω' φ | germSigma A X ⊔ 𝒢.1] ω = m ω) :
    ∀ᵐ ω ∂P, ω ∈ D →
      (∫ ω', Complex.exp (Complex.I * (X ω' φ : ℂ)) ∂(condExpKernel P 𝒢.1 ω)) =
        Complex.exp (Complex.I * (m ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov
            (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) := by
  have hXi : Integrable (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX.measurable)
  have hk := condExp_ae_eq_integral_condExpKernel 𝒢.2 hXi
  have he := ae_retained_cexp_of_mean 𝒢 hX hA hloc hAc φ hD hm hmean
  filter_upwards [hk, he] with ω hkω heω hωD
  exact hkω.symm.trans (heω hωD)

omit [StandardBorelSpace Ω] in
/-- Restore the harmonic boundary datum. The only mean input is the displayed
identity for the centred field; the conclusion is the physical Gaussian law
in the form consumed by the landed K2 chart bridge. -/
theorem ae_retained_physical_cexp_of_mean
    (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ})
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hA : Measurable[𝒢.1, hittingSigma] A)
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝒢.1 A (WholeField.centredField h u₀) P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (φ : TestOn upperHalfPlaneOpens) {D : Set Ω} (hD : MeasurableSet[𝒢.1] D)
    {m : Ω → ℝ} (hm : Measurable[𝒢.1] m)
    (hmean : ∀ᵐ ω ∂P, ω ∈ D →
      P[fun ω' => WholeField.centredField h u₀ ω' φ |
        germSigma A (WholeField.centredField h u₀) ⊔ 𝒢.1] ω =
          m ω - (∫ z, u₀ z * φ z)) :
    ∀ᵐ ω ∂P, ω ∈ D →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝒢.1] ω =
        Complex.exp (Complex.I * (m ω : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (H \ A ω) φ φ : ℝ) : ℂ)) := by
  have he := ae_retained_cexp_of_mean 𝒢 hX hA hloc hAc φ hD
    (hm.sub measurable_const) hmean
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have hsplit : (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) =
      c • fun ω => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω φ : ℂ)) := by
    funext ω
    rw [Pi.smul_apply, WholeField.centredField_apply h hu₀ ω φ, smul_eq_mul,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := P) c
    (fun ω => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω φ : ℂ))) 𝒢.1
  filter_upwards [he, hpull, hAc] with ω heω hpω hAω hωD
  rw [hsplit, hpω, Pi.smul_apply, smul_eq_mul, heω hωD,
    relClosureH_eq hAω.1 hAω.2, hc, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [Pi.sub_apply]
  push_cast
  ring

end InteractingSLE.Theorem14.SB.SewLaw
