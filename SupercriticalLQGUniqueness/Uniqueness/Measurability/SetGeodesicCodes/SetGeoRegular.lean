import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylAllShiftSample
import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.SetGeoSourceBounded




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
open LQGMetric (DistC addFun)

def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 

theorem setGeodesic_has_candidate_of_continuous_forget
    (D : LSCMetric) (K₁ K₂ : Set ℂ) (P : ℝ → ℂ) (T : ℝ)
    (hforget : Continuous (euclidForget D))
    (hSet : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T) :
    ∃ Q : Measurability.GeodesicCodes.Path,
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, (Q, (P 0, P T))) := by
  have hcont : ContinuousOn P (Icc (0 : ℝ) T) := by
    have htmp := hforget.comp_continuousOn hSet.1.1.2
    change ContinuousOn P (Icc (0 : ℝ) T) at htmp
    exact htmp
  have hcompact : IsCompact (P '' Icc (0 : ℝ) T) :=
    isCompact_Icc.image_of_continuousOn hcont
  exact Measurability.ClauseEvents.setGeodesic_has_candidate_of_bounded_trace
    D K₁ K₂ P T hSet hcompact.isBounded

 

theorem ae_all_shift_setGeodesic_has_candidate
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ) :
    ∀ᵐ ω ∂μ, ∀ g : C(ℂ, ℝ), ∀ (K₁ K₂ : Set ℂ)
      (P : ℝ → ℂ) (T : ℝ),
      EndSaving.FiniteEvents.SetGeodesic (D (addFun (h ω) g)) K₁ K₂ P T →
      ∃ R : Measurability.GeodesicCodes.Path,
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂
          (D (addFun (h ω) g), (R, (P 0, P T))) := by
  filter_upwards [Toolkit.WeylShift.ae_all_shift_curves hD μ h hh] with ω hω
  intro g K₁ K₂ P T hSet
  exact setGeodesic_has_candidate_of_continuous_forget
    _ K₁ K₂ P T (hω g).1 hSet

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
