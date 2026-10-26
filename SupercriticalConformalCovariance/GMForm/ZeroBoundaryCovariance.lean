import SupercriticalConformalCovariance.Frozen.ConformalCovariance
import SupercriticalConformalCovariance.GMForm.Independence
import SupercriticalConformalCovariance.GMForm.Realization

set_option autoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace Set Function
open LQGMetric (DistC DistOn IsZeroBoundaryGFF)
open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GMForm

/-- The zero-boundary GM field class satisfies the coordinate-change equality
after a common coupling with whole-plane realizations. -/
theorem gm_zeroBoundary_covariance_on_extension
    (ξ : Set.Ioi (0 : ℝ)) (hξ : xiCrit < (ξ : ℝ))
    (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U V : Opens ℂ) (hUc : IsConnected (U : Set ℂ)) (hVc : IsConnected (V : Set ℂ))
    (hUg : IsGreenian U) (hVg : IsGreenian V)
    (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h z : Ω → DistOn U) (f : Ω → C(U, ℝ))
    (hh : Measurable h) (hz : IsZeroBoundaryGFF U z P) (hf : Measurable f)
    (heq : ∀ᵐ ω ∂P, h ω = z ω +
      Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤) :
    ∃ (Ω₁ : Type) (_ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (π₁ : Ω₁ → Ω)
        (a₀ : Ω₁ → DistC) (a : Ω₁ → C(U, ℝ)),
      MeasurePreserving π₁ P₁ P ∧
      IsDomainRealization U P₁ (h ∘ π₁) a₀ a ∧
      ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (π₂ : Ω₂ → Ω₁)
          (b₀ : Ω₂ → DistC) (b : Ω₂ → C(V, ℝ)),
        MeasurePreserving π₂ P₂ P₁ ∧
        IsDomainRealization V P₂
          (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
            (h (π₁ (π₂ ω)))) b₀ b ∧
        ∀ᵐ ω ∂P₂, ∀ u v : U,
          domainMetric (ξ : ℝ) D U (a₀ (π₂ ω)) (a (π₂ ω)) (u, v) =
            domainMetric (ξ : ℝ) D V (b₀ ω) (b ω)
              (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) := by
  obtain ⟨Ω₁, mΩ₁, P₁, π₁, a₀, a, hπ₁, ha⟩ :=
    exists_realization_of_zeroBoundary P U hUg h z f hh hz hf heq
  letI : MeasurableSpace Ω₁ := mΩ₁
  haveI : IsProbabilityMeasure P₁ := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπ₁
  obtain ⟨hex, hcov⟩ :=
    gm_direction_of_root ξ hξ Q hQ D hD U V hUc hVc hUg hVg φ hφ
      P₁ (h ∘ π₁) a₀ a ha
  obtain ⟨Ω₂, mΩ₂, P₂, π₂, b₀, b, hπ₂, hb⟩ := hex
  letI : MeasurableSpace Ω₂ := mΩ₂
  have he := hcov Ω₂ P₂ π₂ hπ₂ b₀ b hb
  exact ⟨Ω₁, mΩ₁, P₁, π₁, a₀, a, hπ₁, ha,
    Ω₂, mΩ₂, P₂, π₂, b₀, b, hπ₂, hb, he⟩

end SupercriticalConformalCovariance.GMForm
