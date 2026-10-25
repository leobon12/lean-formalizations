import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.LiteralAcross
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Event




 






set_option autoImplicit false
noncomputable section
open Set

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
open LQGMetric (DistC)

 
theorem inner_across_eq_acr
    {ξ : Set.Ioi (0 : ℝ)} {D D' : DistC → LSCMetric}
    {Wc : Set ℂ} {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)}
    {g : DistC} (hgood : Objects.Producer.LocalGood ξ D D' Wc Cc g)
    (r : Set.Ioi (0 : ℝ)) :
    Objects.CorrectedEvent.ambientAcross (D g) 0 (r : ℝ) (1.5 * (r : ℝ)) =
      Objects.CorrectedEvent.acr (D g) 0 (r : ℝ) (1.5 * (r : ℝ)) := by
  have hmetric := hgood.1
  have hlt : (r : ℝ) < 1.5 * (r : ℝ) := by
    have hr : 0 < (r : ℝ) := r.property
    nlinarith
  exact (Objects.ProbabilityS3.acr_eq_ambientAcross_of_barrier (D g) hmetric.2
    hmetric.1.1 0 (r : ℝ) (1.5 * (r : ℝ)) r.property hlt).symm

 
theorem outer_across_eq_acr
    {ξ : Set.Ioi (0 : ℝ)} {D D' : DistC → LSCMetric}
    {Wc : Set ℂ} {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)}
    {g : DistC} (hgood : Objects.Producer.LocalGood ξ D D' Wc Cc g)
    (r : Set.Ioi (0 : ℝ)) :
    Objects.CorrectedEvent.ambientAcross (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)) =
      Objects.CorrectedEvent.acr (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)) := by
  have hmetric := hgood.1
  have hpos : 0 < 2.5 * (r : ℝ) := mul_pos (by norm_num) r.property
  have hlt : 2.5 * (r : ℝ) < 3 * (r : ℝ) := by
    have hr : 0 < (r : ℝ) := r.property
    nlinarith
  exact (Objects.ProbabilityS3.acr_eq_ambientAcross_of_barrier (D g) hmetric.2
    hmetric.1.1 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)) hpos hlt).symm

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
