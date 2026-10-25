import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover.E1eSite




 






set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
open LQGMetric (DistC)

private theorem e1e_radius_pos (n j : ℕ) : 0 < e1eRadius n j := by
  unfold e1eRadius e1eEps
  positivity

 
def e1eNormalizer {Ω : Type} (ξ : Ioi (0 : ℝ)) (Q : ℝ) (h : Ω → DistC)
    (n : ℕ) (x : ℂ) (j : ℕ) (ω : Ω) : ℝ :=
  (e1eRadius n j) ^ ((ξ : ℝ) * Q) *
    Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) (e1eRadius n j) x)

 
def e1eGood {Ω : Type} (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (A : ℝ) (h : Ω → DistC)
    (n : ℕ) (x : ℂ) (j : ℕ) : Set Ω :=
  {ω | BiLipschitz.PaidSeparators.GoodScalar (D (h ω)) (D' (h ω)) A x
    (e1eRadius n j) (e1eNormalizer ξ Q h n x j ω) (e1e_radius_pos n j)}

 



theorem e1e_iterated_grid_cover :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric) (A : ℝ),
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (hx : ℂ → Ω → DistC),
        (∀ x, LQGMetric.IsNormalizedWPGFF (hx x) P) →
        (∀ n x k, k ∈ Finset.Icc 1 (n + 1) →
          MeasurableSet[LQGMetric.Blueprint.fieldSigma
            (fun ω => LQGMetric.addConst (hx x ω)
              (-LQGMetric.circleAvg (hx x ω) (e1eReference n k) 0))
            (LQGMetric.Blueprint.annulus 0
              ((1 / 10) * e1eReference n k)
              ((4 / 5) * e1eReference n k))]
            (e1eGood ξ Q D D' A h n x (k - 1))) →
        (∀ n x j, j ≤ n → ENNReal.ofReal p ≤
          P (e1eGood ξ Q D D' A h n x j)) →
        ∀ᵐ ω ∂P, BiLipschitz.PaidSeparators.GoodGridCover (D (h ω)) (D' (h ω)) A := by
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := e1e_site_tail_constants
  refine ⟨p, c, hp0, hp1, hc, ?_⟩
  intro ξ Q D D' A Ω _ P _ h hx hnorm hlocal hmarg
  let good : ℕ → ℂ → ℕ → Set Ω := e1eGood ξ Q D D' A h
  have hsite : ∀ n x,
      P {ω | ∀ j ≤ n, ω ∉ good n x j} ≤
        ENNReal.ofReal (c * (1 / 100000000 : ℝ) ^ n) :=
    H P hx good hnorm (by intro n x k hk; exact hlocal n x k hk)
      (by intro n x j hj; exact hmarg n x j hj)
  exact e1e_cover_from_site_tail P h D D' A c hc.le e1eRadius
    (e1eNormalizer ξ Q h) good e1e_radius_pos e1e_radius_range
    (by intro n x j ω hω; exact hω) hsite

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
