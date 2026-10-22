import HigherDimLQGMetric.DGZ.NondegLocalZero

/-! Measurable cell hits of a local metric zero set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ} {rGrid : ℝ} (i : nd_DomainIndex d rGrid)

def nd_localCellMinAbs (A K : Set (nd_domain rGrid i)) (m : ℕ)
    (s : nd_Joint d rGrid) : ℝ :=
  sInf ((fun x => |nd_localPointInf i A (s.2 (i, m)) x|) '' K)

theorem nd_continuous_localCellMinAbs {A K : Set (nd_domain rGrid i)}
    (hA : IsCompact A) (hK : IsCompact K) (m : ℕ) :
    Continuous (nd_localCellMinAbs i A K m : nd_Joint d rGrid → ℝ) := by
  have hproj : Continuous (fun p : nd_Joint d rGrid × nd_domain rGrid i =>
      (p.1.2 (i, m), p.2)) :=
    ((continuous_apply (i, m)).comp
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd
  have hf : Continuous (fun p : nd_Joint d rGrid × nd_domain rGrid i =>
      |nd_localPointInf i A (p.1.2 (i, m)) p.2|) :=
    (nd_continuous_localPointInf i hA).abs.comp hproj
  exact hK.continuous_sInf hf

theorem nd_localCellMinAbs_nonneg (A K : Set (nd_domain rGrid i)) (m : ℕ)
    (s : nd_Joint d rGrid) : 0 ≤ nd_localCellMinAbs i A K m s := by
  unfold nd_localCellMinAbs
  apply Real.sInf_nonneg
  rintro _ ⟨x, -, rfl⟩
  exact abs_nonneg _

theorem nd_localCellMinAbs_le {A K : Set (nd_domain rGrid i)}
    (m : ℕ) (s : nd_Joint d rGrid) {x : nd_domain rGrid i} (hx : x ∈ K) :
    nd_localCellMinAbs i A K m s ≤ |nd_localPointInf i A (s.2 (i, m)) x| := by
  unfold nd_localCellMinAbs
  exact csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact abs_nonneg _⟩ ⟨x, hx, rfl⟩

theorem nd_exists_localCellMinAbs_eq {A K : Set (nd_domain rGrid i)}
    (hA : IsCompact A) (hK : IsCompact K) (hKne : K.Nonempty)
    (m : ℕ) (s : nd_Joint d rGrid) :
    ∃ x ∈ K, nd_localCellMinAbs i A K m s =
      |nd_localPointInf i A (s.2 (i, m)) x| := by
  have hc : Continuous fun x : nd_domain rGrid i =>
      |nd_localPointInf i A (s.2 (i, m)) x| :=
    (nd_continuous_localPointInf i hA).abs.comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne hc.continuousOn
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · unfold nd_localCellMinAbs
    exact csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact abs_nonneg _⟩ ⟨x, hx, rfl⟩
  · unfold nd_localCellMinAbs
    exact le_csInf (hKne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hmin hy)

def nd_localExhaust (V : Set (Rd d)) (k : ℕ) : Set (nd_domain rGrid i) :=
  {x | x.1 ∈ tcExhaust V k}

theorem nd_localExhaust_isCompact {V : Set (Rd d)}
    (hVU : V ⊆ nd_domain rGrid i) (k : ℕ) :
    IsCompact (nd_localExhaust i V k) := by
  rw [Subtype.isCompact_iff]
  have heq : ((↑) '' nd_localExhaust i V k : Set (Rd d)) = tcExhaust V k := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hVU (tcExhaust_subset V k hx)⟩, hx, rfl⟩
  rw [heq]
  exact tcExhaust_isCompact V k

def nd_localSelectedCell (A : Set (nd_domain rGrid i)) (m j : ℕ)
    (s : nd_Joint d rGrid) (z : Zd d) : Prop :=
  ∃ x : nd_domain rGrid i,
    x ∈ nd_localZeroSet i A m s ∧
      (x : Rd d) ∈ obox (latPt (nd_gridRadius rGrid j) z)
        (2 * nd_gridRadius rGrid j)

theorem nd_localSelectedCell_iff_exists_min_zero
    {A : Set (nd_domain rGrid i)} (hA : IsCompact A)
    (m j : ℕ) (s : nd_Joint d rGrid) (z : Zd d) :
    nd_localSelectedCell i A m j s z ↔
      ∃ k : ℕ,
        (nd_localExhaust i
          (nd_domain rGrid i ∩
            obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)) k).Nonempty ∧
        nd_localCellMinAbs i A
          (nd_localExhaust i
            (nd_domain rGrid i ∩
              obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)) k) m s = 0 := by
  let V := nd_domain rGrid i ∩
    obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)
  have hVopen : IsOpen V :=
    (nd_isOpen_domain rGrid i).inter (HigherDimLFPP.DGZ.isOpen_obox _ _)
  have hVU : V ⊆ nd_domain rGrid i := inter_subset_left
  constructor
  · rintro ⟨x, hx0, hxB⟩
    obtain ⟨k, hk⟩ := tcExhaust_mem_nhds hVopen ⟨x.2, hxB⟩
    have hxK : x ∈ nd_localExhaust i V k := by
      change (x : Rd d) ∈ tcExhaust V k
      exact mem_of_mem_nhds hk
    refine ⟨k, ⟨x, hxK⟩, le_antisymm ?_
      (nd_localCellMinAbs_nonneg i A _ m s)⟩
    have hle := nd_localCellMinAbs_le i (A := A) m s hxK
    change nd_localPointInf i A (s.2 (i, m)) x = 0 at hx0
    rw [hx0, abs_zero] at hle
    exact hle
  · rintro ⟨k, hne, hzero⟩
    obtain ⟨x, hxK, hmin⟩ := nd_exists_localCellMinAbs_eq i hA
      (nd_localExhaust_isCompact i hVU k) hne m s
    have hx0 : x ∈ nd_localZeroSet i A m s := by
      change nd_localCellMinAbs i A (nd_localExhaust i V k) m s = 0 at hzero
      rw [hzero] at hmin
      exact abs_eq_zero.mp hmin.symm
    have hxV : (x : Rd d) ∈ V := tcExhaust_subset V k hxK
    exact ⟨x, hx0, hxV.2⟩

theorem nd_measurableSet_localSelectedCell
    {A : Set (nd_domain rGrid i)} (hA : IsCompact A)
    (m j : ℕ) (z : Zd d) :
    MeasurableSet {s : nd_Joint d rGrid | nd_localSelectedCell i A m j s z} := by
  rw [show {s : nd_Joint d rGrid | nd_localSelectedCell i A m j s z} =
      ⋃ k : ℕ, {s | (nd_localExhaust i
        (nd_domain rGrid i ∩
          obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)) k).Nonempty ∧
        nd_localCellMinAbs i A
          (nd_localExhaust i
            (nd_domain rGrid i ∩
              obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)) k) m s = 0} by
        ext s; simp only [Set.mem_ofPred_eq, Set.mem_iUnion];
        exact nd_localSelectedCell_iff_exists_min_zero i hA m j s z]
  apply MeasurableSet.iUnion
  intro k
  let V := nd_domain rGrid i ∩
    obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)
  have hVU : V ⊆ nd_domain rGrid i := inter_subset_left
  change MeasurableSet {s : nd_Joint d rGrid |
    (nd_localExhaust i V k).Nonempty ∧
      nd_localCellMinAbs i A (nd_localExhaust i V k) m s = 0}
  by_cases hne : (nd_localExhaust i V k).Nonempty
  · simpa only [hne, true_and] using
      (isClosed_eq (nd_continuous_localCellMinAbs i hA
        (nd_localExhaust_isCompact i hVU k) m) continuous_const).measurableSet
  · simp only [hne, false_and, Set.ofPred_false, MeasurableSet.empty]

def nd_localSelectedEq (A : Set (nd_domain rGrid i))
    (m j : ℕ) (S : Finset (Zd d)) : Set (nd_Joint d rGrid) :=
  {s | ∀ z : Zd d, nd_localSelectedCell i A m j s z ↔ z ∈ S}

theorem nd_measurableSet_localSelectedEq
    {A : Set (nd_domain rGrid i)} (hA : IsCompact A)
    (m j : ℕ) (S : Finset (Zd d)) :
    MeasurableSet (nd_localSelectedEq i A m j S) := by
  rw [show nd_localSelectedEq i A m j S = ⋂ z : Zd d,
      {s : nd_Joint d rGrid | nd_localSelectedCell i A m j s z ↔ z ∈ S} by
        ext s; simp [nd_localSelectedEq]]
  apply MeasurableSet.iInter
  intro z
  by_cases hz : z ∈ S
  · simpa only [hz, iff_true] using nd_measurableSet_localSelectedCell i hA m j z
  · simpa only [hz, iff_false, Set.compl_ofPred] using
      (nd_measurableSet_localSelectedCell i hA m j z).compl

end HigherDimLQGMetric.DGZ
