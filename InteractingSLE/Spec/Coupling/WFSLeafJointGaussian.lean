/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafKernel
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofCover

/-!
# A history kernel from a retained local set and its history-measurable mean

The marked local-set kernel initially conditions on both the history and the
field germ. If its mean and covariance are functions of the history, the tower
property removes the germ. This gives a joint-field-law criterion without
assuming a joint-field law as an input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LQGMetric LocalSets WholeField
open QuantumZipper (H zeroGFFTestCov)

/-- The characteristic function with history-coded mean and covariance. -/
def gaussianHistoryKernel {Γ : Type*}
    (M Q : TestOn upperHalfPlaneOpens → Γ → ℝ)
    (γ : Γ) (φ : TestOn upperHalfPlaneOpens) : ℂ :=
  Complex.exp (Complex.I * (M φ γ : ℂ)) *
    ((Real.exp (-(1 / 2) * Q φ γ) : ℝ) : ℂ)

theorem measurable_gaussianHistoryKernel {Γ : Type*} [MeasurableSpace Γ]
    {M Q : TestOn upperHalfPlaneOpens → Γ → ℝ}
    (hM : ∀ φ, Measurable (M φ)) (hQ : ∀ φ, Measurable (Q φ))
    (φ : TestOn upperHalfPlaneOpens) :
    Measurable (fun γ => gaussianHistoryKernel M Q γ φ) :=
  (Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp (hM φ)))).mul
    (Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((hQ φ).const_mul (-(1 / 2)))))

/-- The local-set mean is also the conditional mean when the retained history
is included among the marks. -/
theorem ae_localSetMean_eq_condExp_history
    {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ)
    (hloc : IsHistoryAvoidanceLocal ℋ A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hg : IsLocalSetMean A h P g) (φ : TestOn upperHalfPlaneOpens) :
    (fun ω => g ω φ) =ᵐ[P]
      P[fun ω => h ω φ | germSigma A h ⊔ ℋ] := by
  obtain ⟨M, hMm, hM1, _⟩ := exists_condExp_germSigma_history hh hA hℋ hloc hAc φ
  have hle := sup_le (germSigma_le hA hh.measurable) hℋ
  have hMi : Integrable M P := integrable_condExp.congr hM1.symm
  have e1 := condExp_condExp_of_le (μ := P)
    (f := fun ω => h ω φ) (le_sup_left : germSigma A h ≤ germSigma A h ⊔ ℋ) hle
  have e2 := condExp_congr_ae (m := germSigma A h) hM1.symm
  rw [condExp_of_stronglyMeasurable (germSigma_le hA hh.measurable)
    hMm.stronglyMeasurable hMi] at e2
  have hφi := (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
  have hg' := Sec6.IsLocalSetMean.ae_eq_condExp hA hh.measurable hg
    (hAc.mono fun _ hω => hω.2) φ hφi
  exact (hg'.trans (e1.symm.trans e2)).trans hM1

/-- A history-marked retained local set whose mean and covariance are coded by
the history supplies the whole-field kernel given that history. The conditions
concern the actual local set and its mean; no joint-law equality is assumed. -/
theorem isHistoryFieldKernel_of_retainedMean
    {Ω Γ : Type*} [mΩ : MeasurableSpace Ω] [mΓ : MeasurableSpace Γ]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {Y : Ω → Γ} (hY : Measurable Y)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsHistoryAvoidanceLocal (mΓ.comap Y) A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hg : IsLocalSetMean A h P g)
    {M Q : TestOn upperHalfPlaneOpens → Γ → ℝ}
    (hM : ∀ φ, Measurable (M φ)) (hQ : ∀ φ, Measurable (Q φ))
    (hmean : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, g ω φ = M φ (Y ω))
    (hcov : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      zeroGFFTestCov (H \ A ω) φ φ = Q φ (Y ω)) :
    LawUnique.IsHistoryFieldKernel P h Y (gaussianHistoryKernel M Q) := by
  intro φ
  obtain ⟨N, _, hN1, hN2⟩ := exists_condExp_germSigma_history hh hA hY.comap_le hloc hAc φ
  have hgN := (ae_localSetMean_eq_condExp_history hh hA hY.comap_le hloc hAc hg φ).trans hN1.symm
  have hfull : P[fun ω => Complex.exp ((h ω φ : ℂ) * Complex.I) |
      germSigma A h ⊔ mΓ.comap Y] =ᵐ[P] fun ω => gaussianHistoryKernel M Q (Y ω) φ := by
    have hex : (fun ω => Complex.exp ((h ω φ : ℂ) * Complex.I)) =
        (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) := by
      funext ω
      rw [mul_comm]
    rw [hex]
    filter_upwards [hN2, hgN, hmean φ, hcov φ, hAc] with ω h1 h2 h3 h4 h5
    rw [← h1, ← h2, h3, relClosureH_eq h5.1 h5.2, h4]
    rfl
  have hkm : Measurable[mΓ.comap Y] (fun ω => gaussianHistoryKernel M Q (Y ω) φ) :=
    (measurable_gaussianHistoryKernel hM hQ φ).comp (comap_measurable Y)
  have hki : Integrable (fun ω => gaussianHistoryKernel M Q (Y ω) φ) P :=
    integrable_condExp.congr hfull
  have ht := condExp_condExp_of_le (μ := P)
    (f := fun ω => Complex.exp ((h ω φ : ℂ) * Complex.I))
    (le_sup_right : mΓ.comap Y ≤ germSigma A h ⊔ mΓ.comap Y)
    (sup_le (germSigma_le hA hh.measurable) hY.comap_le)
  exact ht.symm.trans ((condExp_congr_ae hfull).trans
    (Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hY.comap_le hkm.stronglyMeasurable hki)))

end InteractingSLE.WFS
