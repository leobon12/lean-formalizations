import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.HolderRate




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem normalizedAroundAt_moment_rate
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p q : ℝ) (hp : 0 < p) (hq : 1 < q) :
    ∃ K : ENNReal, K < ∞ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (a s : Set.Ioi (0 : ℝ)) (has : (a : ℝ) ≤ s)
          (y c : ℂ) (hnear : ‖y - c‖ ≤ s),
          (∫⁻ ω, normalizedAroundAt ξ Q D (h ω) a s y c ^ p ∂P) ≤
            K * ENNReal.ofReal
              ((a / s) ^ (ξ * Q * p - q * p ^ 2 * ξ ^ 2 / 2)) := by
  obtain ⟨M, hMfin, hMoment⟩ :=
    normalizedAroundAt_moment_le ξ Q hQ D hD p q hp hq
  let C : ENNReal := ENNReal.ofReal
    (Real.exp (q * p ^ 2 * ξ ^ 2 * Real.log (1 + 1)))
  refine ⟨M ^ (1 / (q / (q - 1))) * C, ?_, ?_⟩
  · exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hMfin.ne))
      ENNReal.ofReal_lt_top
  intro Ω _ P _ h hh a s has y c hnear
  have hBound := hMoment P h hh a s has y c hnear
  have hid := annulus_rate_identity (a : ℝ) (s : ℝ) ξ Q p q
    a.2 s.2 hp (zero_lt_one.trans hq)
  calc
    (∫⁻ ω, normalizedAroundAt ξ Q D (h ω) a s y c ^ p ∂P) ≤
        ENNReal.ofReal ((a / s) ^ (ξ * Q)) ^ p *
          M ^ (1 / (q / (q - 1))) *
          ENNReal.ofReal
            (Real.exp ((p * q * ξ) ^ 2 *
              (Real.log (s / a) + 2 * Real.log (1 + 1)) / 2)) ^ (1 / q) := hBound
    _ = (M ^ (1 / (q / (q - 1))) * C) *
        ENNReal.ofReal ((a / s) ^ (ξ * Q * p - q * p ^ 2 * ξ ^ 2 / 2)) := by
      calc
        _ = M ^ (1 / (q / (q - 1))) *
            (ENNReal.ofReal ((a / s) ^ (ξ * Q)) ^ p *
              ENNReal.ofReal
                (Real.exp ((p * q * ξ) ^ 2 *
                  (Real.log (s / a) + 2 * Real.log (1 + 1)) / 2)) ^ (1 / q)) := by
            ac_rfl
        _ = _ := by
          rw [hid]
          dsimp only [C]
          ac_rfl


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
