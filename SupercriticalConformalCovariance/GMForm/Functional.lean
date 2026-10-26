import SupercriticalConformalCovariance.Frozen.ConformalCovariance
import SupercriticalConformalCovariance.GMForm.ZeroBoundaryCovariance
import SupercriticalConformalCovariance.Domain.Axioms
import SupercriticalConformalCovariance.Domain.AeEq

set_option autoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace Set Function
open scoped ENNReal
open LQGMetric (DistC DistOn IsZeroBoundaryGFF)
open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GMForm

/-- For a specified field law on a single space, one Borel function computes the
domain metric of every whole-plane realization on that space. -/
theorem exists_measurable_metric_for_all_realizations_on_space
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U : Opens ℂ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn U) (a₀ : Ω → DistC) (a : Ω → C(U, ℝ))
    (ha : IsDomainRealization U P h a₀ a) :
    ∃ Φ : DistOn U → (U × U → ℝ≥0∞), Measurable Φ ∧
      ∀ (b₀ : Ω → DistC) (b : Ω → C(U, ℝ)),
        IsDomainRealization U P h b₀ b →
        ∀ᵐ ω ∂P, Φ (h ω) = domainMetric (ξ : ℝ) D U (b₀ ω) (b ω) := by
  obtain ⟨Φ, hΦm, hΦ⟩ := SupercriticalConformalCovariance.Domain.exists_measurable_domainMetric hD U ha
  refine ⟨Φ, hΦm, ?_⟩
  intro b₀ b hb
  filter_upwards [hΦ, SupercriticalConformalCovariance.Domain.domainMetric_ae_eq_of_isDomainRealization ξ Q hQ D hD U P h a₀ b₀ a b ha hb] with ω eΦ eI
  exact eΦ.symm.trans eI

/-- For every individual zero-boundary GFF plus an arbitrary jointly measurable
continuous correction, a Borel function of the domain distribution represents
the domain metric on a measure-preserving whole-plane realization. The Borel
function is chosen for this law; the statement does not claim one choice for
all laws. -/
theorem exists_measurable_metric_of_zeroBoundary
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U : Opens ℂ) (hUg : IsGreenian U)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h z : Ω → DistOn U) (f : Ω → C(U, ℝ))
    (hh : Measurable h) (hz : IsZeroBoundaryGFF U z P) (hf : Measurable f)
    (heq : ∀ᵐ ω ∂P, h ω = z ω +
      Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤) :
    ∃ Φ : DistOn U → (U × U → ℝ≥0∞), Measurable Φ ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
          (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
        MeasurePreserving π P' P ∧
        IsDomainRealization U P' (h ∘ π) g₀ k ∧
        ∀ᵐ ω' ∂P', Φ (h (π ω')) = domainMetric (ξ : ℝ) D U (g₀ ω') (k ω') := by
  obtain ⟨Ω', mΩ', P', π, g₀, k, hπ, hr⟩ :=
    exists_realization_of_zeroBoundary P U hUg h z f hh hz hf heq
  letI : MeasurableSpace Ω' := mΩ'
  haveI : IsProbabilityMeasure P' := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπ
  obtain ⟨Φ, hΦm, hΦ⟩ := SupercriticalConformalCovariance.Domain.exists_measurable_domainMetric hD U hr
  exact ⟨Φ, hΦm, Ω', mΩ', P', π, g₀, k, hπ, hr, hΦ.mono fun _ e => e.symm⟩

/-- For a specified zero-boundary field law, measurable distribution-indexed
metrics on both domains obey the GM coordinate formula simultaneously for all
endpoint pairs on the common realization extension. The functions may depend
on the given law. -/
theorem exists_fieldwise_gm_axiomIV_on_extension
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
    ∃ ΦU : DistOn U → (U × U → ℝ≥0∞), Measurable ΦU ∧
    ∃ ΦV : DistOn V → (V × V → ℝ≥0∞), Measurable ΦV ∧
    ∃ (Ω₁ : Type) (_ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (π₁ : Ω₁ → Ω)
        (a₀ : Ω₁ → DistC) (a : Ω₁ → C(U, ℝ)),
      MeasurePreserving π₁ P₁ P ∧
      IsDomainRealization U P₁ (h ∘ π₁) a₀ a ∧
      (∀ᵐ ω ∂P₁, ΦU (h (π₁ ω)) = domainMetric (ξ : ℝ) D U (a₀ ω) (a ω)) ∧
      ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (π₂ : Ω₂ → Ω₁)
          (b₀ : Ω₂ → DistC) (b : Ω₂ → C(V, ℝ)),
        MeasurePreserving π₂ P₂ P₁ ∧
        IsDomainRealization V P₂
          (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
            (h (π₁ (π₂ ω)))) b₀ b ∧
        (∀ᵐ ω ∂P₂,
          ΦV (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
            (h (π₁ (π₂ ω)))) = domainMetric (ξ : ℝ) D V (b₀ ω) (b ω)) ∧
        (∀ᵐ ω ∂P₂, ∀ u v : U,
          ΦU (h (π₁ (π₂ ω))) (u, v) =
            ΦV (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
              (h (π₁ (π₂ ω))))
              (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩)) := by
  obtain ⟨Ω₁, mΩ₁, P₁, π₁, a₀, a, hπ₁, ha, Ω₂, mΩ₂, P₂, π₂, b₀, b,
    hπ₂, hb, hcov⟩ :=
      gm_zeroBoundary_covariance_on_extension ξ hξ Q hQ D hD
        U V hUc hVc hUg hVg φ hφ P h z f hh hz hf heq
  letI : MeasurableSpace Ω₁ := mΩ₁
  haveI : IsProbabilityMeasure P₁ := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπ₁
  obtain ⟨ΦU, hΦUm, hΦU⟩ := SupercriticalConformalCovariance.Domain.exists_measurable_domainMetric hD U ha
  letI : MeasurableSpace Ω₂ := mΩ₂
  haveI : IsProbabilityMeasure P₂ := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπ₂
  obtain ⟨ΦV, hΦVm, hΦV⟩ := SupercriticalConformalCovariance.Domain.exists_measurable_domainMetric hD V hb
  have hΦU₂ : ∀ᵐ ω ∂P₂,
      ΦU (h (π₁ (π₂ ω))) = domainMetric (ξ : ℝ) D U (a₀ (π₂ ω)) (a (π₂ ω)) := by
    have hmap : ∀ᵐ x ∂P₂.map π₂,
        ΦU (h (π₁ x)) = domainMetric (ξ : ℝ) D U (a₀ x) (a x) := by
      rw [hπ₂.map_eq]
      exact hΦU.mono fun _ e => e.symm
    exact ae_of_ae_map hπ₂.measurable.aemeasurable hmap
  refine ⟨ΦU, hΦUm, ΦV, hΦVm, Ω₁, mΩ₁, P₁, π₁, a₀, a,
    hπ₁, ha, hΦU.mono (fun _ e => e.symm),
    Ω₂, mΩ₂, P₂, π₂, b₀, b, hπ₂, hb,
    hΦV.mono (fun _ e => e.symm), ?_⟩
  filter_upwards [hΦU₂, hΦV, hcov] with ω eU eV ec
  intro u v
  rw [eU, ← eV]
  exact ec u v

end SupercriticalConformalCovariance.GMForm
