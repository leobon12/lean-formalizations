import SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.SeparatorPacking
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.SelectedRecurrence




 






set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings

 


theorem selected_ratio_growth_on_internal_geodesic
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    (z : ℂ) (base : Ioi (0 : ℝ))
    (N : ℕ) (S : Finset ℕ) (hcard : 2 ≤ S.card)
    (hS : S ⊆ Finset.Icc 1 N)
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    {P : ℝ → ℂ} {T q : ℝ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (hAK : ∀ i ∈ S, (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)).toSet ⊆ K)
    (h0 : ∀ i ∈ S, 2 * (TwoScale.Ratio.ratioRadius base i : ℝ) ≤ dist (P 0) z)
    (hT : ∀ i ∈ S, 2 * (TwoScale.Ratio.ratioRadius base i : ℝ) ≤ dist (P T) z)
    (hq : dist (P q) z ≤ (TwoScale.Ratio.ratioRadius base N : ℝ))
    (hgood : ∀ i ∈ S,
      aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)) ≤
        C * acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)))
    (hfin : ∀ i ∈ S,
      aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)) ≠ ∞) :
    ∃ i ∈ S, ∃ j ∈ S,
      (∀ k ∈ S, i ≤ k) ∧ (∀ k ∈ S, k ≤ j) ∧
      (1 / C.toReal) * (1 + 1 / C.toReal) ^ (S.card - 2) *
        (aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j))).toReal ≤
          (aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i))).toReal := by
  classical
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  let i := S.min' hSne
  let j := S.max' hSne
  have hiS : i ∈ S := Finset.min'_mem S hSne
  have hjS : j ∈ S := Finset.max'_mem S hSne
  have hmin : ∀ k ∈ S, i ≤ k := fun k hk => Finset.min'_le S k hk
  have hmax : ∀ k ∈ S, k ≤ j := fun k hk => Finset.le_max' S k hk
  let X : ℕ → ℝ≥0∞ := fun k =>
    aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base k))
  have hrec : ∀ k ∈ S,
      (∑ m ∈ S.filter (fun m => k < m), X m) ≤ C * X k := by
    intro k hkS
    let U := S.filter (fun m => k < m)
    by_cases hU : U = ∅
    · simp only [U, hU, Finset.sum_empty, zero_le]
    · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
      obtain ⟨m, hmU⟩ := hUne
      have hm : m ∈ S ∧ k < m := Finset.mem_filter.mp hmU
      have hmN : m ≤ N := (Finset.mem_Icc.mp (hS hm.1)).2
      have hkN : k < N := lt_of_lt_of_le hm.2 hmN
      have hUS : U ⊆ Finset.Ioc k N := by
        intro m' hm'
        have hm' : m' ∈ S ∧ k < m' := Finset.mem_filter.mp hm'
        exact Finset.mem_Ioc.mpr ⟨hm'.2, (Finset.mem_Icc.mp (hS hm'.1)).2⟩
      have hgoodU : ∀ m ∈ U,
          aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base m)) ≤
            C * acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base m)) :=
        fun m hm => hgood m (Finset.mem_filter.mp hm).1
      exact selected_ratio_around_sum_le_outer D K hK z base k N hkN
        (hAK k hkS) hq0 hqT hP hPK hgeo (h0 k hkS) hq
        (hT k hkS) U hUS C hgoodU
  have hgrowth := selected_first_growth_of_ennreal C hC0 hCtop X S
    hcard j hjS hmax hfin hrec
  refine ⟨i, hiS, j, hjS, hmin, hmax, ?_⟩
  exact hgrowth


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings
