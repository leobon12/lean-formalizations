import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover.E1eFinal




 





set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover

private theorem noSuccess_ae_eq {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (raw version : ℕ → Set Ω)
    (n : ℕ) (h : ∀ j, j ≤ n → version j =ᵐ[P] raw j) :
    {ω | ∀ j ≤ n, ω ∉ version j} =ᵐ[P]
      {ω | ∀ j ≤ n, ω ∉ raw j} := by
  have hall : ∀ᵐ ω ∂P, ∀ j : {j : ℕ // j ≤ n},
      (ω ∈ version j) = (ω ∈ raw j) :=
    ae_all_iff.mpr (fun j => h j.1 j.2)
  filter_upwards [hall] with ω hω
  apply propext
  constructor
  · intro hv j hj hjraw
    exact hv j hj ((Iff.of_eq (hω ⟨j, hj⟩)).2 hjraw)
  · intro hr j hj hjversion
    exact hr j hj ((Iff.of_eq (hω ⟨j, hj⟩)).1 hjversion)

private theorem e1e_radius_pos (n j : ℕ) : 0 < e1eRadius n j := by
  unfold e1eRadius e1eEps
  positivity

 

theorem e1e_iterated_grid_cover_versioned :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric) (A : ℝ),
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (hx : ℂ → Ω → DistC)
        (version : ℕ → ℂ → ℕ → Set Ω),
        (∀ x, LQGMetric.IsNormalizedWPGFF (hx x) P) →
        (∀ n x k, k ∈ Finset.Icc 1 (n + 1) →
          MeasurableSet[LQGMetric.Blueprint.fieldSigma
            (fun ω => LQGMetric.addConst (hx x ω)
              (-LQGMetric.circleAvg (hx x ω) (e1eReference n k) 0))
            (LQGMetric.Blueprint.annulus 0
              ((1 / 10) * e1eReference n k)
              ((4 / 5) * e1eReference n k))]
            (version n x (k - 1))) →
        (∀ n x j, j ≤ n → ENNReal.ofReal p ≤ P (version n x j)) →
        (∀ n x j, j ≤ n →
          version n x j =ᵐ[P] e1eGood ξ Q D D' A h n x j) →
        ∀ᵐ ω ∂P, BiLipschitz.PaidSeparators.GoodGridCover (D (h ω)) (D' (h ω)) A := by
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := e1e_site_tail_constants
  refine ⟨p, c, hp0, hp1, hc, ?_⟩
  intro ξ Q D D' A Ω _ P _ h hx version hnorm hlocal hmarg hversion
  let raw : ℕ → ℂ → ℕ → Set Ω := e1eGood ξ Q D D' A h
  have hsiteVersion : ∀ n x,
      P {ω | ∀ j ≤ n, ω ∉ version n x j} ≤
        ENNReal.ofReal (c * (1 / 100000000 : ℝ) ^ n) :=
    H P hx version hnorm hlocal hmarg
  have hsite : ∀ n x,
      P {ω | ∀ j ≤ n, ω ∉ raw n x j} ≤
        ENNReal.ofReal (c * (1 / 100000000 : ℝ) ^ n) := by
    intro n x
    have heq : P {ω | ∀ j ≤ n, ω ∉ version n x j} =
        P {ω | ∀ j ≤ n, ω ∉ raw n x j} := by
      exact measure_congr (noSuccess_ae_eq (raw n x) (version n x) n
        (fun j hj => hversion n x j hj))
    rw [← heq]
    exact hsiteVersion n x
  exact e1e_cover_from_site_tail P h D D' A c hc.le e1eRadius
    (e1eNormalizer ξ Q h) raw e1e_radius_pos e1e_radius_range
    (by intro n x j ω hω; exact hω) hsite


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
