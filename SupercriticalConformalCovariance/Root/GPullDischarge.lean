import SupercriticalConformalCovariance.Root.Assembly
import SupercriticalConformalCovariance.GPull.Existence

set_option autoImplicit false
noncomputable section

namespace SupercriticalConformalCovariance.Root

/-- The proved Greenian pullback realization supplies the assembly input exactly. -/
theorem gPullInput_proved : GPullInput := by
  intro U V hU hV φ hφ Ω _ P _ Q h h₀ f hr
  exact SupercriticalConformalCovariance.GPull.exists_confPullback_domainRealization_greenian
    U V hU hV φ hφ P Q h h₀ f hr

/-- The exact frozen root type follows from the four remaining source inputs. -/
theorem conformal_covariance_of_four_inputs
    (hTight : ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) →
      ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
      ∀ D : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric,
        SupercriticalLQGUniqueness.IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.TargetTightUniform ξ Q D)
    (hGEL : ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) →
      ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
      ∀ D : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric,
        SupercriticalLQGUniqueness.IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.GoodEventsLocal ξ Q D)
    (hP43 : ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) →
      ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
      ∀ D : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric,
        SupercriticalLQGUniqueness.IsStrongLQGMetric ξ Q D → Prop43Input ξ Q D)
    (hL51 : ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) →
      ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
      ∀ D : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric,
        SupercriticalLQGUniqueness.IsStrongLQGMetric ξ Q D → Lemma51LocalInput ξ Q D) :
    (open MeasureTheory TopologicalSpace Set in
      open scoped ENNReal in
      open LQGMetric (DistC DistOn) in
      open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric) in
      open SupercriticalConformalCovariance in
      ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
        ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
        ∀ U V : Opens ℂ, IsConnected (U : Set ℂ) → IsConnected (V : Set ℂ) →
        IsGreenian U → IsGreenian V →
        ∀ (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V),
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ)),
          IsDomainRealization V P h h₀ f →
          (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
              (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)), MeasurePreserving π P' P ∧
            IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k) ∧
          ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (π : Ω' → Ω), MeasurePreserving π P' P →
            ∀ (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
              IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k →
              ∀ᵐ ω' ∂P', ∀ u v : U,
                domainMetric (ξ : ℝ) D V (h₀ (π ω')) (f (π ω'))
                    (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) =
                  domainMetric (ξ : ℝ) D U (g₀ ω') (k ω') (u, v)) := by
  exact conformal_covariance_closed hTight hGEL hP43 hL51 gPullInput_proved


end SupercriticalConformalCovariance.Root
