import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.AroundNarrow
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S7
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S8Weyl
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.LiteralAcross




 






set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

 

theorem around_wide_le_weyl_narrow
    (ξ : ℝ) (f : C(ℂ, ℝ)) (d e : LSCMetric)
    (he : ∀ x y : ℂ, e (x, y) = weylScale ξ f d (x, y))
    (w : ℂ) (t : ℝ) (ht : 0 < t) (c : ℝ)
    (hf : ∀ y : ℂ, (21 / 20) * t < dist y w →
      dist y w < (39 / 20) * t → f y = c) :
    Objects.CorrectedEvent.around e w t (2 * t) ≤
      ENNReal.ofReal (Real.exp (ξ * c)) *
        Objects.CorrectedEvent.around d w ((21 / 20) * t) ((39 / 20) * t) := by
  have hinner : 0 < (21 / 20) * t := by positivity
  have hordered : (21 / 20) * t < (39 / 20) * t := by linarith
  let A : EuclideanAnnulus :=
    ⟨(w, (21 / 20) * t, (39 / 20) * t), hinner, hordered⟩
  have hcost := Objects.ProbabilityS7S9.aroundDist_le_weyl ξ f d e he A c (by
    intro y hy
    change y ∈ ball w ((39 / 20) * t) \ closure (ball w ((21 / 20) * t)) at hy
    rw [closure_ball w hinner.ne'] at hy
    exact hf y (lt_of_not_ge hy.2) hy.1)
  rw [← Objects.ProbabilityS7S9.around_eq_aroundDist e w _ _ hinner hordered,
    ← Objects.ProbabilityS7S9.around_eq_aroundDist d w _ _ hinner hordered] at hcost
  exact (around_wide_le_narrow e w t ht).trans hcost

 

theorem acr_le_weyl_off_bump
    (ξ : ℝ) (f : C(ℂ, ℝ)) (d e : LSCMetric)
    (he : ∀ x y : ℂ, e (x, y) = weylScale ξ f d (x, y))
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), d.IsCurve γ a b →
      ContinuousOn γ (Icc a b))
    (hbarrier : BiLipschitz.Barrier.Barrier d) (hlength : d.IsLengthSpace)
    (w : ℂ) (t : ℝ) (ht : 0 < t)
    (hf : ∀ y : ℂ, 2 * t ≤ dist y w → dist y w ≤ 3 * t → f y = 0) :
    Objects.CorrectedEvent.acr d w (2 * t) (3 * t) ≤
      Objects.CorrectedEvent.acr e w (2 * t) (3 * t) := by
  have hinner : 0 < 2 * t := by linarith
  have hordered : 2 * t < 3 * t := by linarith
  let A : EuclideanAnnulus := ⟨(w, 2 * t, 3 * t), hinner, hordered⟩
  have hleft := Objects.ProbabilityS3.acr_eq_ambientAcross_of_barrier d hbarrier hlength
    w (2 * t) (3 * t) hinner hordered
  have hmiddle := Objects.ProbabilityS7S9.acrossDist_le_weyl ξ f d e he hcont A (by
    intro y hy1 hy2
    exact hf y hy1 hy2)
  have hright := Objects.ProbabilityS1S2.ambientAcross_le_acr e w (2 * t) (3 * t)
  calc
    Objects.CorrectedEvent.acr d w (2 * t) (3 * t) = acrossDist d A := hleft
    _ ≤ acrossDist e A := hmiddle
    _ = Objects.CorrectedEvent.ambientAcross e w (2 * t) (3 * t) := rfl
    _ ≤ Objects.CorrectedEvent.acr e w (2 * t) (3 * t) := hright

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
