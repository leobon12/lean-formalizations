import SupercriticalConformalCovariance.Small.AffineRegular
import SupercriticalConformalCovariance.Small.RescaleSource

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalConformalCovariance.Small
open LQGMetric
open SupercriticalLQGUniqueness

/-- Printed (7) and (8) after affine zoom and smooth recentering. -/
theorem ae_sourceRegularPair_rescale
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (r : Ioi (0 : ℝ)) (z : ℂ) (smooth : Ω → ℝ)
    (α θ : ℝ) (hα0 : (3 / 4 : ℝ) < α) (hα : α < 1) :
    ∀ᵐ ω ∂P, ∀ (u v : ℂ) (circle : ℝ),
      SupercriticalConformalCovariance.Regular.SourceRegularPair (D (h ω)) z u v r α θ
        ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * circle)) →
      SupercriticalConformalCovariance.Regular.SourceRegularPair
        (D (addConst (affineComp (r : ℝ) z (h ω)) (-smooth ω))) 0
        ((regularZoomHomeo z r.2).symm u)
        ((regularZoomHomeo z r.2).symm v)
        1 α θ (Real.exp ((ξ : ℝ) * (circle - smooth ω))) := by
  filter_upwards [ae_rescaled_source_metric hD P h hh r z smooth] with ω hω u v circle hreg
  let s : ℝ := (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * smooth ω))
  have hs : 0 < s := mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _)
  have hm : ∀ a b : ℂ,
      D (addConst (affineComp (r : ℝ) z (h ω)) (-smooth ω)) (a,b) =
        ENNReal.ofReal s *
          D (h ω) (regularZoomHomeo z r.2 a, regularZoomHomeo z r.2 b) := by
    intro a b
    have ha : regularZoomHomeo z r.2 a = z + (r : ℂ) * a :=
      regularZoomHomeo_apply z r.2 a
    have hb : regularZoomHomeo z r.2 b = z + (r : ℂ) * b :=
      regularZoomHomeo_apply z r.2 b
    rw [ha, hb]
    exact hω a b
  have hreg' := sourceRegularPair_regularZoomHomeo z u v r.2 hs hm
    α θ ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * circle))
    hα0 hα hreg
  dsimp only [s] at hreg'
  rw [regularZoom_normalizer (ξ : ℝ) Q (r : ℝ) circle (smooth ω) r.2] at hreg'
  exact hreg'

end SupercriticalConformalCovariance.Small
