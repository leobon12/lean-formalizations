import SupercriticalConformalCovariance.Small.AffineConfined
import SupercriticalConformalCovariance.Domain.Sample
import LQGMetric.Papers.GM.S1.Dilate

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open LQGMetric
open SupercriticalLQGUniqueness

/-- Adding a global continuous correction commutes with adding a constant to a field. -/
private theorem addFun_addConst_commute (g : DistC) (c : ℝ) (F : C(ℂ,ℝ)) :
    addFun (addConst g c) F = addConst (addFun g F) c := by
  simp only [addConst, addFun]
  abel

/-- The exact affine/Weyl factor for a target whole-plane representative plus
any measurable global continuous correction. -/
theorem ae_rescaled_target_with_correction
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : Ω → DistC) (hg : IsGFFPlusCont g P)
    (F : Ω → C(ℂ,ℝ)) (hF : Measurable F)
    (r : Set.Ioi (0 : ℝ)) (a : ℂ) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      D (addFun (addConst (affineComp (r : ℝ) a (g ω)) (-c ω))
        ((F ω).comp (LQGMetric.affinePt (r : ℝ) a))) (u,v) =
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * c ω))) *
        D (addFun (g ω) (F ω))
          (a + (r : ℂ) * u, a + (r : ℂ) * v) := by
  have hgF : IsGFFPlusCont (fun ω => addFun (g ω) (F ω)) P :=
    SupercriticalConformalCovariance.Domain.isGFFPlusCont_addFun_of_measurable hg hF
  filter_upwards [ae_rescaled_source_metric hD P
    (fun ω => addFun (g ω) (F ω)) hgF r a c] with ω hω u v
  have hfield : addFun (addConst (affineComp (r : ℝ) a (g ω)) (-c ω))
      ((F ω).comp (LQGMetric.affinePt (r : ℝ) a)) =
      addConst (affineComp (r : ℝ) a (addFun (g ω) (F ω))) (-c ω) := by
    rw [addFun_addConst_commute,
      LQGMetric.GM.affineComp_addFun r.2]
  rw [hfield]
  exact hω u v

end SupercriticalConformalCovariance.Small
