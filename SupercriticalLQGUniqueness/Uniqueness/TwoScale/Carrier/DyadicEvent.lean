import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.FiniteScaleTheorem
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.DyadicProbability




set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

open LQGMetric (DistC)

def dyadicScale (q : ℝ) (n : ℕ) : ℝ := q * (1 / 2 : ℝ) ^ n

theorem dyadicScale_pos {q : ℝ} (hq : 0 < q) (n : ℕ) :
    0 < dyadicScale q n := mul_pos hq (pow_pos (by norm_num) _)

theorem dyadicScale_le {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    dyadicScale q n ≤ q := by
  unfold dyadicScale
  have hp : (1 / 2 : ℝ) ^ n ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hp hq]


def dyadicGoodSample
    {Ω : Type} (h : Ω → DistC) (D : DistC → LSCMetric)
    (α M q R : ℝ) (hq : 0 < q) (hR : 0 < R)
    (z₀ : ℂ) (ω : Ω) : Prop :=
  ∀ n : ℕ, finiteScaleGoodSample h D α M (dyadicScale q n) R
    (dyadicScale_pos hq n) hR z₀ ω

 

theorem dyadic_good_sample_bad_probability
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ M C β lam₀ : ℝ,
      1 ≤ M ∧ 0 < C ∧ 0 < β ∧ 0 < lam₀ ∧
      lam₀ = scaleCutoff α
        (ENNReal.ofReal M * ENNReal.ofReal M).toReal ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (q R : ℝ) (hq : 0 < q), q ≤ lam₀ →
          (hR : 0 < R) → ∀ (z₀ : ℂ),
          P {ω | ¬ dyadicGoodSample h D α M q R hq hR z₀ ω} ≤
            ENNReal.ofReal (C * q ^ (4 : ℕ)) *
              (1 - ENNReal.ofReal (1 / 16 : ℝ))⁻¹ := by
  obtain ⟨M, C, β, lam₀, hM, hC, hβ, h0, heqcut, hscale⟩ :=
    finite_scale_ratio_f0 ξ Q D hD α hα0 hα1
  refine ⟨M, C, β, lam₀, hM, hC, hβ, h0, heqcut, ?_⟩
  intro Ω _ P _ h hh q R hq hq0 hR z₀
  let bad : ℕ → Set Ω := fun n =>
    {ω | ¬ finiteScaleGoodSample h D α M (dyadicScale q n) R
      (dyadicScale_pos hq n) hR z₀ ω}
  have hbad (n : ℕ) : P (bad n) ≤
      ENNReal.ofReal (C * (q * (1 / 2 : ℝ) ^ n) ^ (4 : ℕ)) := by
    have hqn : dyadicScale q n ≤ lam₀ :=
      (dyadicScale_le hq.le n).trans hq0
    exact (hscale P h hh (dyadicScale q n) R (dyadicScale_pos hq n)
      hqn hR z₀).1
  have heq : {ω | ¬ dyadicGoodSample h D α M q R hq hR z₀ ω} =
      ⋃ n, bad n := by
    ext ω
    simp only [dyadicGoodSample, bad, mem_ofPred_eq, mem_iUnion]
    push Not
    rfl
  rw [heq]
  exact dyadic_bad_probability P bad hC.le hq.le hbad


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
