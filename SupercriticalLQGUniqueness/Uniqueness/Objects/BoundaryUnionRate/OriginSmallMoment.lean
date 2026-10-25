import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AroundAtMeas
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.SubadditiveSum




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem origin_dyadic_sum_moment_small
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hpcrit : p < 2 * Q / ξ) :
    ∃ C : ENNReal, C < ∞ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (w : ℂ) (_hw : w ≠ 0),
          (∫⁻ ω, (∑' i : ℕ × Bool,
              Objects.BoundaryUnionMoments.dyadicAround (D (h ω)) w i /
                Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0) ^ p ∂P) ≤ C := by
  obtain ⟨q, K, hq, hK, hγ, hterm⟩ :=
    dyadic_around_moment_rate ξ Q hQ D hD p hp hpcrit
  let γ : ℝ := (ξ : ℝ) * Q * p - q * p ^ 2 * ξ ^ 2 / 2
  let S : ENNReal :=
    ∑' i : ℕ × Bool, ENNReal.ofReal (Objects.BoundaryUnionDyadic.dyadicQ i.1 ^ γ)
  have hS : S < ∞ := dyadicQ_rpow_tsum_lt_top γ hγ
  refine ⟨K * S, ENNReal.mul_lt_top hK hS, ?_⟩
  intro Ω _ P _ h hh w hw
  let f : ℕ × Bool → Ω → ENNReal := fun i ω =>
    Objects.BoundaryUnionMoments.dyadicAround (D (h ω)) w i /
      Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0
  have hf (i : ℕ × Bool) : AEMeasurable (f i) P := by
    let s : Set.Ioi (0 : ℝ) := ⟨‖w‖, norm_pos_iff.mpr hw⟩
    have hq : 0 < Objects.BoundaryUnionDyadic.dyadicQ i.1 := by
      unfold Objects.BoundaryUnionDyadic.dyadicQ
      positivity
    let a : Set.Ioi (0 : ℝ) :=
      ⟨Objects.BoundaryUnionDyadic.dyadicOuter w i, mul_pos hq s.2⟩
    have heq : f i = fun ω => normalizedAroundAt ξ Q D (h ω) a s
        (Objects.BoundaryUnionDyadic.dyadicCenter w i) 0 := by
      funext ω
      simp only [f, normalizedAroundAt, Objects.BoundaryUnionMoments.dyadicAround, a, s,
        one_mul, one_div, inv_mul_eq_div]
    rw [heq]
    exact ((measurable_normalizedAroundAt ξ Q D hD.1 a s
      (Objects.BoundaryUnionDyadic.dyadicCenter w i) 0).comp hh.1.measurable).aemeasurable
  calc
    (∫⁻ ω, (∑' i, f i ω) ^ p ∂P) ≤
        ∑' i, ∫⁻ ω, f i ω ^ p ∂P :=
      lintegral_tsum_rpow_le_tsum_lintegral_rpow P f hf hp hp1
    _ ≤ ∑' i, K * ENNReal.ofReal (Objects.BoundaryUnionDyadic.dyadicQ i.1 ^ γ) :=
      ENNReal.tsum_le_tsum (fun i => hterm P h hh w hw i)
    _ = K * S := by rw [ENNReal.tsum_mul_left]


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
