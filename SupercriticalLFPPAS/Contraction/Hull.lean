import SupercriticalLFPPAS.Contraction.IntervalCover

/-! Length bounds for the hull of the covered interval and the selected intervals. -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLFPPAS.Contraction

/-- The smallest interval containing a fixed closed interval and a finite family of open
intervals, with witnesses for each endpoint that lies outside the fixed interval. -/
structure D4IntervalHull (U : Finset D4Interval) (a b left right : ℝ) : Prop where
  left_le : left ≤ a
  right_ge : b ≤ right
  intervals_inside : ∀ I ∈ U, left ≤ I.1 ∧ I.2 ≤ right
  left_extreme : left = a ∨ ∃ I ∈ U, I.1 = left
  right_extreme : right = b ∨ ∃ I ∈ U, I.2 = right

/-- A canonical hull exists for every finite interval family. -/
theorem d4_intervalHull_exists (U : Finset D4Interval) (a b : ℝ) :
    ∃ left right, D4IntervalHull U a b left right := by
  classical
  let L := insert a (U.image Prod.fst)
  let R := insert b (U.image Prod.snd)
  have hL : L.Nonempty := ⟨a, Finset.mem_insert_self _ _⟩
  have hR : R.Nonempty := ⟨b, Finset.mem_insert_self _ _⟩
  let left := L.min' hL
  let right := R.max' hR
  refine ⟨left, right, ?_⟩
  constructor
  · exact Finset.min'_le L a (Finset.mem_insert_self _ _)
  · exact Finset.le_max' R b (Finset.mem_insert_self _ _)
  · intro I hI
    constructor
    · have hmem : I.1 ∈ L := Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨I, hI, rfl⟩)
      exact Finset.min'_le L I.1 hmem
    · have hmem : I.2 ∈ R := Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨I, hI, rfl⟩)
      exact Finset.le_max' R I.2 hmem
  · have hmem : left ∈ L := Finset.min'_mem L hL
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Or.inl h
    · obtain ⟨I, hI, hEq⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨I, hI, hEq⟩
  · have hmem : right ∈ R := Finset.max'_mem R hR
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Or.inl h
    · obtain ⟨I, hI, hEq⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨I, hI, hEq⟩

/-- A greedy run's selected intervals are pairwise disjoint. -/
theorem d4_greedyRun_pairwiseDisjoint {F : Finset D4Interval} {l : List D4Interval}
    (hpositive : ∀ I ∈ F, I.1 < I.2) (hRun : D4GreedyRun F l) :
    PairwiseDisjoint (l.toFinset : Set D4Interval) d4IntervalBall := by
  obtain ⟨_, hnodup, hpair, _⟩ := d4_greedyRun_spec hpositive hRun
  exact (List.pairwise_iff_coe_toFinset_pairwise hnodup).mpr hpair

/-- The volume of a finite disjoint union of selected intervals equals the sum of their lengths. -/
theorem d4_disjointIntervalUnion_volume {U : Finset D4Interval}
    (hpositive : ∀ I ∈ U, I.1 < I.2)
    (hdisj : PairwiseDisjoint (U : Set D4Interval) d4IntervalBall) :
    volume (⋃ I ∈ U, d4IntervalBall I) =
      ENNReal.ofReal (∑ I ∈ U, d4IntervalLength I) := by
  have hmeasure : volume (⋃ I ∈ U, d4IntervalBall I) =
      ∑ I ∈ U, volume (d4IntervalBall I) :=
    measure_biUnion_finset hdisj (fun I hI => measurableSet_ball)
  have hballs :
      (∑ I ∈ U, volume (d4IntervalBall I)) =
        ∑ I ∈ U, ENNReal.ofReal (d4IntervalLength I) := by
    apply Finset.sum_congr rfl
    intro I hI
    simp only [d4IntervalBall, Real.volume_ball]
    congr 1
    dsimp [d4IntervalLength]
    ring
  rw [hmeasure, hballs]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  intro I hI
  dsimp [d4IntervalLength]
  linarith [hpositive I hI]

/-- The disjoint selected intervals fit inside their hull, so their total length is at most
the hull length. -/
theorem d4_hull_lower_length_bound {U : Finset D4Interval} {a b left right : ℝ}
    (hpositive : ∀ I ∈ U, I.1 < I.2)
    (hdisj : PairwiseDisjoint (U : Set D4Interval) d4IntervalBall)
    (hhull : D4IntervalHull U a b left right) (hab : a ≤ b) :
    ∑ I ∈ U, d4IntervalLength I ≤ right - left := by
  have hsubset : (⋃ I ∈ U, d4IntervalBall I) ⊆ Ioo left right := by
    intro x hx
    obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hx
    have hxI' : x ∈ Ioo I.1 I.2 := by
      rw [← d4IntervalBall_eq_Ioo I]
      exact hxI
    obtain ⟨hleft, hright⟩ := hhull.intervals_inside I hI
    exact ⟨lt_of_le_of_lt hleft hxI'.1, lt_of_lt_of_le hxI'.2 hright⟩
  have hvol := d4_disjointIntervalUnion_volume hpositive hdisj
  have hleftRight : left ≤ right := le_trans hhull.left_le (le_trans hab hhull.right_ge)
  have hvolle : volume (⋃ I ∈ U, d4IntervalBall I) ≤ volume (Ioo left right) :=
    measure_mono hsubset
  have hsum_nonneg : 0 ≤ ∑ I ∈ U, d4IntervalLength I := by
    apply Finset.sum_nonneg
    intro I hI
    dsimp [d4IntervalLength]
    linarith [hpositive I hI]
  rw [hvol, Real.volume_Ioo] at hvolle
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg_of_le hleftRight)).mp hvolle

/-- The two parts of the hull outside the covered interval lie in its leftmost and rightmost
selected intervals. Thus the hull exceeds the covered interval by at most the total selected
length. -/
theorem d4_hull_upper_length_bound {U : Finset D4Interval} {a b left right : ℝ}
    (hpositive : ∀ I ∈ U, I.1 < I.2)
    (hdisj : PairwiseDisjoint (U : Set D4Interval) d4IntervalBall)
    (hhull : D4IntervalHull U a b left right) (hab : a ≤ b)
    (hmeet : ∀ I ∈ U, (Ioo I.1 I.2 ∩ Icc a b).Nonempty) :
    right - left ≤ (b - a) + ∑ I ∈ U, d4IntervalLength I := by
  have hleftCover : Ioo left a ⊆ ⋃ I ∈ U, Ioo I.1 I.2 := by
    intro x hx
    rcases hhull.left_extreme with hEq | ⟨I, hI, hIleft⟩
    · rw [hEq] at hx
      exact False.elim (lt_irrefl _ (hx.1.trans hx.2))
    · obtain ⟨y, hyI, hyJ⟩ := hmeet I hI
      have haI : a < I.2 := lt_of_le_of_lt hyJ.1 hyI.2
      have hxI : x ∈ Ioo I.1 I.2 := by
        constructor
        · simpa [hIleft] using hx.1
        · exact hx.2.trans haI
      exact Set.mem_iUnion₂.mpr ⟨I, hI, hxI⟩
  have hrightCover : Ioo b right ⊆ ⋃ I ∈ U, Ioo I.1 I.2 := by
    intro x hx
    rcases hhull.right_extreme with hEq | ⟨I, hI, hIright⟩
    · rw [hEq] at hx
      exact False.elim (lt_irrefl _ (hx.1.trans hx.2))
    · obtain ⟨y, hyI, hyJ⟩ := hmeet I hI
      have hIa : I.1 < b := lt_of_lt_of_le hyI.1 hyJ.2
      have hxI : x ∈ Ioo I.1 I.2 := by
        constructor
        · exact hIa.trans hx.1
        · simpa [hIright] using hx.2
      exact Set.mem_iUnion₂.mpr ⟨I, hI, hxI⟩
  have hcoverHull : Ioo left right ⊆
      Icc a b ∪ ⋃ I ∈ U, Ioo I.1 I.2 := by
    intro x hx
    by_cases hxa : x < a
    · exact Or.inr (hleftCover ⟨hx.1, hxa⟩)
    · by_cases hbx : b < x
      · exact Or.inr (hrightCover ⟨hbx, hx.2⟩)
      · exact Or.inl ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩
  have hsubsetVol : volume (Ioo left right) ≤
      volume (Icc a b ∪ ⋃ I ∈ U, Ioo I.1 I.2) := measure_mono hcoverHull
  have hunionBound : volume (Icc a b ∪ ⋃ I ∈ U, Ioo I.1 I.2) ≤
      volume (Icc a b) + volume (⋃ I ∈ U, Ioo I.1 I.2) := measure_union_le _ _
  have hintervalUnion :
      volume (⋃ I ∈ U, Ioo I.1 I.2) =
        ENNReal.ofReal (∑ I ∈ U, d4IntervalLength I) := by
    have hEq : (⋃ I ∈ U, Ioo I.1 I.2) = ⋃ I ∈ U, d4IntervalBall I := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨I, hI, hx⟩
        have hx' : x ∈ d4IntervalBall I := by
          rw [d4IntervalBall_eq_Ioo]
          exact hx
        exact ⟨I, hI, hx'⟩
      · rintro ⟨I, hI, hx⟩
        have hx' : x ∈ Ioo I.1 I.2 := by
          rw [← d4IntervalBall_eq_Ioo]
          exact hx
        exact ⟨I, hI, hx'⟩
    rw [hEq]
    exact d4_disjointIntervalUnion_volume hpositive hdisj
  have hsum_nonneg : 0 ≤ ∑ I ∈ U, d4IntervalLength I := by
    apply Finset.sum_nonneg
    intro I hI
    dsimp [d4IntervalLength]
    linarith [hpositive I hI]
  rw [Real.volume_Ioo] at hsubsetVol
  rw [Real.volume_Icc, hintervalUnion] at hunionBound
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le hab) hsum_nonneg] at hunionBound
  have hcombined : ENNReal.ofReal (right - left) ≤
      ENNReal.ofReal ((b - a) + ∑ I ∈ U, d4IntervalLength I) :=
    hsubsetVol.trans hunionBound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcombined

end SupercriticalLFPPAS.Contraction
