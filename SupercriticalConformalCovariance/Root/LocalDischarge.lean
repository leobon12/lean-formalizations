import SupercriticalConformalCovariance.Root.GPullDischarge
import SupercriticalConformalCovariance.BiLip.Final
import SupercriticalConformalCovariance.BiLip.L51.Main

/-! The Lemma 2.1 proof supplies the exact locality input used by the root assembly. -/
namespace SupercriticalConformalCovariance.Root

theorem conformal_covariance_of_three_inputs
    (hTight : ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) →
      ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
      ∀ D : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric,
        SupercriticalLQGUniqueness.IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.TargetTightUniform ξ Q D)
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
  exact conformal_covariance_of_four_inputs hTight
    (fun ξ _ Q _ D hD => SupercriticalConformalCovariance.BiLip.goodEventsLocal_proved hD) hP43 hL51

end SupercriticalConformalCovariance.Root

namespace SupercriticalConformalCovariance.Root

/-- The final Lemma 2.1 sources discharge both BiLip inputs of the root assembly. -/
theorem conformal_covariance_of_two_inputs
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
  exact conformal_covariance_of_three_inputs
    (fun ξ _ Q hQ D hD => SupercriticalConformalCovariance.BiLip.targetTightUniform_of_seq
      (SupercriticalConformalCovariance.BiLip.targetTightSeq_proved hQ hD)) hP43 hL51

end SupercriticalConformalCovariance.Root

namespace SupercriticalConformalCovariance.Root

/-- Lemma 5.1 discharges the locality input, leaving Proposition 4.3 as the
only input to the exact frozen root statement. -/
theorem conformal_covariance_of_prop43
    (hP43 : ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) →
      ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
      ∀ D : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric,
        SupercriticalLQGUniqueness.IsStrongLQGMetric ξ Q D → Prop43Input ξ Q D) :
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
  exact conformal_covariance_of_two_inputs hP43
    (fun ξ _ Q _ D hD => SupercriticalConformalCovariance.BiLip.L51.lemma51LocalInput_proved hD)

end SupercriticalConformalCovariance.Root
