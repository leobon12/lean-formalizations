import SupercriticalConformalCovariance.Transport.FieldLocality

/-! Uniform transported locality for domain metrics supplied by target realizations. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric (DistC DistOn)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric)
open SupercriticalConformalCovariance (IsConformalBijection IsDomainRealization
  confPullbackField domainMetric)

namespace SupercriticalConformalCovariance.Transport

variable {φ : ℂ → ℂ} {U V A B : Opens ℂ}

/-- For a countable family of source laws and realizations of their forward pulled fields, one
functional of the source restriction gives every target-domain metric on `B = φ(A)`. -/
theorem universal_transported_locality {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    (hφ : IsConformalBijection φ U V) (hAU : A ≤ U)
    (hcl : closure (A : Set ℂ) ⊆ U) (hbd : Bornology.IsBounded (A : Set ℂ))
    (hB : (B : Set ℂ) = φ '' A) (hBV : B ≤ V)
    (ι : Type) [Countable ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (h : ∀ i, Ω i → DistOn U) (hbar₀ : ∀ i, Ω i → DistC)
    (fbar : ∀ i, Ω i → C(V, ℝ))
    (hR : ∀ i, IsDomainRealization V (P i)
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h i ω))
      (hbar₀ i) (fbar i)) :
    ∃ G : DistOn A → (B × B → ℝ≥0∞), Measurable G ∧
      ∀ i, ∀ᵐ ω ∂(P i),
        domainMetric (ξ : ℝ) D B (hbar₀ i ω)
          (SupercriticalConformalCovariance.Domain.resC (show (B : Set ℂ) ⊆ V from hBV) (fbar i ω)) =
          G (SupercriticalConformalCovariance.Domain.restrictOn hAU (h i ω)) := by
  obtain ⟨R, hRm, hRe⟩ := exists_measurable_forward_restrict Q hφ hAU hcl hbd hB hBV
  obtain ⟨F, hFm, hFae⟩ := universal_domain_locality hD B ι Ω P
    (fun i ω => SupercriticalConformalCovariance.Domain.restrictOn hBV
      (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h i ω)))
    hbar₀ (fun i ω => SupercriticalConformalCovariance.Domain.resC (show (B : Set ℂ) ⊆ V from hBV) (fbar i ω))
    (fun i => SupercriticalConformalCovariance.Domain.isDomainRealization_restrictOn hBV (hR i))
  refine ⟨F ∘ R, hFm.comp hRm, fun i => ?_⟩
  filter_upwards [hFae i] with ω he
  rw [he, hRe (h i ω)]
  rfl

end SupercriticalConformalCovariance.Transport
