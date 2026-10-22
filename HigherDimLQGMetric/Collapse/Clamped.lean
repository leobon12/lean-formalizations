import HigherDimLQGMetric.Collapse.GeodesicCompact

/-! # Internal distance along the constant extension of a geodesic -/

set_option autoImplicit false

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- The internal distance along a unit-speed geodesic extended constantly after time `ℓ`
is the difference of times clamped at `ℓ`. -/
theorem intrinsic_distance_eq_clamped_time {X : Type*} [MetricSpace X]
    {K : Set X} {T ℓ : ℝ} (hT : 0 ≤ T) (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ T)
    (Q : Icc (0 : ℝ) T →ᵇ X) (hQK : ∀ t, Q t ∈ K)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
      internalEDist K ((Set.IccExtend hT Q) s) ((Set.IccExtend hT Q) t) =
        ENNReal.ofReal (t - s))
    (htail : ∀ t : Icc (0 : ℝ) T, ℓ ≤ t → Q t = Q ⟨ℓ, ⟨hℓ0, hℓT⟩⟩)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hst : s ≤ t) :
    (internalEDist K ((Set.IccExtend hT Q) s) ((Set.IccExtend hT Q) t)).toReal =
      min t ℓ - min s ℓ := by
  have hℓmem : ℓ ∈ Icc (0 : ℝ) T := ⟨hℓ0, hℓT⟩
  by_cases htℓ : t ≤ ℓ
  · have hsℓ : s ≤ ℓ := hst.trans htℓ
    rw [hgeo s ⟨hs.1, hsℓ⟩ t ⟨ht.1, htℓ⟩ hst,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst), min_eq_left htℓ,
      min_eq_left hsℓ]
  by_cases hℓs : ℓ ≤ s
  · have hℓt : ℓ ≤ t := hℓs.trans hst
    have hsQ : (Set.IccExtend hT Q) s = Q ⟨ℓ, hℓmem⟩ := by
      rw [Set.IccExtend_of_mem hT Q hs]
      exact htail ⟨s, hs⟩ hℓs
    have htQ : (Set.IccExtend hT Q) t = Q ⟨ℓ, hℓmem⟩ := by
      rw [Set.IccExtend_of_mem hT Q ht]
      exact htail ⟨t, ht⟩ hℓt
    rw [hsQ, htQ, internalEDist_self (hQK ⟨ℓ, hℓmem⟩)]
    simp [min_eq_right hℓs, min_eq_right hℓt]
  · have hsℓ : s ≤ ℓ := le_of_not_ge hℓs
    have hℓt : ℓ ≤ t := (lt_of_not_ge htℓ).le
    have htQ : (Set.IccExtend hT Q) t =
        (Set.IccExtend hT Q) ℓ := by
      rw [Set.IccExtend_of_mem hT Q ht, Set.IccExtend_of_mem hT Q hℓmem]
      exact htail ⟨t, ht⟩ hℓt
    rw [htQ, hgeo s ⟨hs.1, hsℓ⟩ ℓ ⟨hℓ0, le_rfl⟩ hsℓ,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hsℓ),
      min_eq_right hℓt, min_eq_left hsℓ]

/-- If `s ≤ t ≤ L`, the unclamped duration differs from the clamped duration
by at most the excess of `L` over `ℓ`. -/
theorem time_gap_le_clamped_gap_add {s t L ℓ : ℝ} (hst : s ≤ t) (htL : t ≤ L) :
    t - s ≤ (min t ℓ - min s ℓ) + max (L - ℓ) 0 := by
  rcases le_total t ℓ with htℓ | hℓt
  · have hsℓ := hst.trans htℓ
    simp only [min_eq_left htℓ, min_eq_left hsℓ]
    exact le_add_of_nonneg_right (le_max_right _ _)
  rcases le_total s ℓ with hsℓ | hℓs
  · simp only [min_eq_right hℓt, min_eq_left hsℓ]
    have hLℓ : t - ℓ ≤ max (L - ℓ) 0 := by
      exact (sub_le_sub_right htL _).trans (le_max_left _ _)
    linarith
  · simp only [min_eq_right hℓt, min_eq_right hℓs, sub_self, zero_add]
    have hLℓ : t - ℓ ≤ max (L - ℓ) 0 := by
      exact (sub_le_sub_right htL _).trans (le_max_left _ _)
    linarith

end HigherDimLQGMetric
