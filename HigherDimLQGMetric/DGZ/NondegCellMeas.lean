import HigherDimLQGMetric.DGZ.NondegThickening

/-!
# Measurability of the lattice cells selected by a zero set

The existing compact exhaustion of an open set reduces a hit of a random zero
set to countably many continuous compact minima. This avoids a hyperspace or
Hausdorff-limit construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ}
variable {rGrid : ℝ}

/-- Minimum absolute distance-to-sphere value on a compact test set. -/
def nd_cellMinAbs (A K : Set (Rd d)) (s : nd_Joint d rGrid) : ℝ :=
  sInf ((fun x => |nd_pointSetInf A s.1 x|) '' K)

theorem nd_continuous_cellMinAbs {A : Set (Rd d)} (hA : IsCompact A)
    {K : Set (Rd d)} (hK : IsCompact K) :
    Continuous (nd_cellMinAbs A K : nd_Joint d rGrid → ℝ) := by
  have hf : Continuous (fun p : nd_Joint d rGrid × Rd d =>
      |nd_pointSetInf A p.1.1 p.2|) :=
    (nd_continuous_pointSetInf hA).abs.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact hK.continuous_sInf hf

theorem nd_cellMinAbs_nonneg (A K : Set (Rd d)) (s : nd_Joint d rGrid) :
    0 ≤ nd_cellMinAbs A K s := by
  unfold nd_cellMinAbs
  apply Real.sInf_nonneg
  rintro _ ⟨x, -, rfl⟩
  exact abs_nonneg _

theorem nd_cellMinAbs_le {A K : Set (Rd d)}
    (s : nd_Joint d rGrid) {x : Rd d} (hx : x ∈ K) :
    nd_cellMinAbs A K s ≤ |nd_pointSetInf A s.1 x| := by
  unfold nd_cellMinAbs
  exact csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact abs_nonneg _⟩ ⟨x, hx, rfl⟩

theorem nd_exists_cellMinAbs_eq {A K : Set (Rd d)} (hA : IsCompact A)
    (hK : IsCompact K) (hKne : K.Nonempty) (s : nd_Joint d rGrid) :
    ∃ x ∈ K, nd_cellMinAbs A K s = |nd_pointSetInf A s.1 x| := by
  have hc : Continuous fun x : Rd d => |nd_pointSetInf A s.1 x| :=
    (nd_continuous_pointSetInf hA).abs.comp (continuous_const.prodMk continuous_id)
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne hc.continuousOn
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · unfold nd_cellMinAbs
    exact csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact abs_nonneg _⟩ ⟨x, hx, rfl⟩
  · unfold nd_cellMinAbs
    exact le_csInf (hKne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hmin hy)

/-- A cell meets the zero set precisely when a compact exhaustion stage has
zero minimum. The nonempty guard excludes the empty-set convention for `sInf`. -/
theorem nd_selectedCell_iff_exists_cellMinAbs_zero {rGrid r : ℝ} (j : ℕ)
    (s : nd_Joint d rGrid) (z : Zd d) :
    nd_selectedCell rGrid r j s z ↔
      ∃ k : ℕ, (tcExhaust
          (obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)) k).Nonempty ∧
        nd_cellMinAbs (lsph 0 r)
          (tcExhaust (obox (latPt (nd_gridRadius rGrid j) z)
            (2 * nd_gridRadius rGrid j)) k) s = 0 := by
  let U := obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)
  have hU : IsOpen U := HigherDimLFPP.DGZ.isOpen_obox _ _
  have hA : IsCompact (lsph (0 : Rd d) r) := tn_isCompact_lsph 0 r
  constructor
  · rintro ⟨x, hx0, hxU⟩
    obtain ⟨k, hk⟩ := tcExhaust_mem_nhds hU hxU
    have hxK : x ∈ tcExhaust U k := mem_of_mem_nhds hk
    refine ⟨k, ⟨x, hxK⟩, le_antisymm ?_ (nd_cellMinAbs_nonneg _ _ _)⟩
    have hle := nd_cellMinAbs_le (A := lsph 0 r) s hxK
    change nd_pointSetInf (lsph 0 r) s.1 x = 0 at hx0
    rw [hx0, abs_zero] at hle
    exact hle
  · rintro ⟨k, hne, hzero⟩
    obtain ⟨x, hxK, hmin⟩ := nd_exists_cellMinAbs_eq hA
      (tcExhaust_isCompact U k) hne s
    have hx0 : nd_pointSetInf (lsph 0 r) s.1 x = 0 := by
      change nd_cellMinAbs (lsph 0 r) (tcExhaust U k) s = 0 at hzero
      rw [hzero] at hmin
      exact abs_eq_zero.mp hmin.symm
    exact ⟨x, hx0, tcExhaust_subset U k hxK⟩

theorem nd_measurableSet_selectedCell (rGrid r : ℝ) (j : ℕ) (z : Zd d) :
    MeasurableSet {s : nd_Joint d rGrid | nd_selectedCell rGrid r j s z} := by
  rw [show {s : nd_Joint d rGrid | nd_selectedCell rGrid r j s z} =
      ⋃ k : ℕ, {s | (tcExhaust
        (obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)) k).Nonempty ∧
        nd_cellMinAbs (lsph 0 r)
          (tcExhaust (obox (latPt (nd_gridRadius rGrid j) z)
            (2 * nd_gridRadius rGrid j)) k) s = 0} by
        ext s; simp only [Set.mem_ofPred_eq, Set.mem_iUnion];
        exact nd_selectedCell_iff_exists_cellMinAbs_zero j s z]
  apply MeasurableSet.iUnion
  intro k
  by_cases hne : (tcExhaust
      (obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)) k).Nonempty
  · simpa only [hne, true_and] using
      (isClosed_eq (nd_continuous_cellMinAbs (tn_isCompact_lsph 0 r)
        (tcExhaust_isCompact _ k)) continuous_const).measurableSet
  · simp only [hne, false_and, Set.ofPred_false, MeasurableSet.empty]

theorem nd_thickening_eq_boxUnion_of_selected (rGrid r : ℝ)
    (j : ℕ) (s : nd_Joint d rGrid) (S : Finset (Zd d))
    (hsel : ∀ z : Zd d, nd_selectedCell rGrid r j s z ↔ z ∈ S) :
    nd_thickening rGrid r j s = nd_boxUnion rGrid j S := by
  ext x
  simp only [nd_thickening, nd_boxUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz, hx⟩
    exact ⟨z, (hsel z).mp hz, hx⟩
  · rintro ⟨z, hz, hx⟩
    exact ⟨z, (hsel z).mpr hz, hx⟩

/-- The selected finite set is a measurable code for the random domain. -/
def nd_selectedEq (rGrid r : ℝ) (j : ℕ) (S : Finset (Zd d)) :
    Set (nd_Joint d rGrid) :=
  {s | ∀ z : Zd d, nd_selectedCell rGrid r j s z ↔ z ∈ S}

theorem nd_measurableSet_selectedEq (rGrid r : ℝ) (j : ℕ)
    (S : Finset (Zd d)) : MeasurableSet (nd_selectedEq rGrid r j S) := by
  rw [show nd_selectedEq rGrid r j S = ⋂ z : Zd d,
      {s : nd_Joint d rGrid | nd_selectedCell rGrid r j s z ↔ z ∈ S} by
        ext s; simp [nd_selectedEq]]
  apply MeasurableSet.iInter
  intro z
  by_cases hz : z ∈ S
  · simpa only [hz, iff_true] using nd_measurableSet_selectedCell rGrid r j z
  · simpa only [hz, iff_false, Set.compl_ofPred] using
      (nd_measurableSet_selectedCell rGrid r j z).compl

theorem nd_thickening_eq_domain_of_selectedEq (rGrid r : ℝ)
    (i : nd_DomainIndex d rGrid) (s : nd_Joint d rGrid)
    (hsel : s ∈ nd_selectedEq rGrid r i.1.1 i.1.2) :
    nd_thickening rGrid r i.1.1 s = nd_domain rGrid i :=
  nd_thickening_eq_boxUnion_of_selected rGrid r i.1.1 s i.1.2 hsel

end HigherDimLQGMetric.DGZ
