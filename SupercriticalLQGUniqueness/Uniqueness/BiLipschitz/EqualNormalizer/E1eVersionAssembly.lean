import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.E1eLocalVersion




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover

private theorem e1e_radius_pos (n j : ℕ) : 0 < e1eRadius n j := by
  unfold e1eRadius e1eEps
  positivity

 

theorem normalized_grid_cover_of_around
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hAround : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), ∀ d e : LSCMetric,
      d.internal (BiLipschitz.OneScale.collarOpen z r : Set ℂ) =
        e.internal (BiLipschitz.OneScale.collarOpen z r : Set ℂ) →
      aroundDist d (BiLipschitz.OneScale.separatorAt z r) = aroundDist e (BiLipschitz.OneScale.separatorAt z r)) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ᵐ ω ∂P, BiLipschitz.PaidSeparators.GoodGridCover (D (h ω)) (D' (h ω)) A := by
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := e1e_iterated_grid_cover_versioned
  obtain ⟨A, hA, hmargRaw⟩ := BiLipschitz.OneScale.raw_paired_uniform ξ Q D D' hD hD' p hp0 hp1
  refine ⟨A, hA, ?_⟩
  intro Ω _ P _ h hh
  let version : ℕ → ℂ → ℕ → Set Ω := fun n x j =>
    Classical.choose (exists_e1e_local_version P h hh ξ Q hQ D D' hD hD' A
      hAround n x j)
  have hversion : ∀ n x j,
      MeasurableSet[LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst
          (translatedField h x ω)
          (-LQGMetric.circleAvg (translatedField h x ω)
            (e1eReference n (j + 1)) 0))
        (LQGMetric.Blueprint.annulus 0
          ((1 / 10) * e1eReference n (j + 1))
          ((4 / 5) * e1eReference n (j + 1)))]
        (version n x j) ∧
      version n x j =ᵐ[P] e1eGood ξ Q D D' A h n x j := by
    intro n x j
    exact Classical.choose_spec (exists_e1e_local_version P h hh ξ Q hQ D D' hD hD'
      A hAround n x j)
  have hnorm : ∀ x, LQGMetric.IsNormalizedWPGFF (translatedField h x) P := by
    intro x
    exact normalized_translate_old hh x
  have hlocal : ∀ n x k, k ∈ Finset.Icc 1 (n + 1) →
      MeasurableSet[LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (translatedField h x ω)
          (-LQGMetric.circleAvg (translatedField h x ω) (e1eReference n k) 0))
        (LQGMetric.Blueprint.annulus 0
          ((1 / 10) * e1eReference n k)
          ((4 / 5) * e1eReference n k))]
        (version n x (k - 1)) := by
    intro n x k hk
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Finset.mem_Icc.mp hk).1
    have hm := (hversion n x (k - 1)).1
    rw [hk1] at hm
    exact hm
  have hmarg : ∀ n x j, j ≤ n → ENNReal.ofReal p ≤ P (version n x j) := by
    intro n x j _
    have hraw : ENNReal.ofReal p ≤ P (e1eGood ξ Q D D' A h n x j) := by
      rw [raw_event_eq]
      exact hmargRaw P h hh x ⟨e1eRadius n j, e1e_radius_pos n j⟩
    rwa [measure_congr (hversion n x j).2]
  exact H ξ Q D D' A P h (translatedField h) version hnorm hlocal hmarg
    (fun n x j _ => (hversion n x j).2)

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
