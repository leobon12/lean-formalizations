import HigherDimLQGContinuity.Grid.Interp
import HigherDimLQGContinuity.Grid.Bad

/-! Deterministic consequences of the two comparison families at successive grids. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

theorem posBad_lower_bound {d : ℕ} {lo hi R : ℝ} {j m : ℕ}
    (hm : m ≤ 2 ^ posLevel (j + 1)) {g : DistRd d}
    (hg : g ∉ posBad d lo hi R j) :
    supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
      (gridProfile d (posNode lo hi j (posBracket j m)) g) ≤
        ENNReal.ofReal (posDelta j) := by
  have hnot : g ∉ posLowerBad d lo hi R j := (not_or.mp hg).1
  have hmS : m ∈ Finset.range (2 ^ posLevel (j + 1) + 1) := by
    simp only [Finset.mem_range]
    omega
  have hlocal : g ∉ {g | ENNReal.ofReal (posDelta j) <
      supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
        (gridProfile d (posNode lo hi j (posBracket j m)) g)} := by
    intro hmem
    apply hnot
    exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hmS, hmem⟩⟩
  exact le_of_not_gt hlocal

theorem posBad_upper_bound {d : ℕ} {lo hi R : ℝ} {j m : ℕ}
    (hm : m ≤ 2 ^ posLevel (j + 1))
    (hbr : posBracket j m < 2 ^ posLevel j) {g : DistRd d}
    (hg : g ∉ posBad d lo hi R j) :
    supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
      (gridProfile d (posNode lo hi j (posBracket j m + 1)) g) ≤
        ENNReal.ofReal (posDelta j) := by
  have hnot : g ∉ posUpperBad d lo hi R j := (not_or.mp hg).2
  have hmS : m ∈ Finset.range (2 ^ posLevel (j + 1) + 1) := by
    simp only [Finset.mem_range]
    omega
  have hlocal : g ∉ {g | ENNReal.ofReal (posDelta j) <
      supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
        (gridProfile d (posNode lo hi j (posBracket j m + 1)) g)} := by
    intro hmem
    apply hnot
    unfold posUpperBad
    refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hmS, ?_⟩⟩
    simpa [hbr] using hmem
  exact le_of_not_gt hlocal

/-- A fine grid node differs by at most `δ_j` from the previous interpolant. -/
theorem supd_interpProfile_fine_node_le (d : ℕ) {lo hi R : ℝ}
    (h : lo < hi) (j m : ℕ) (hm : m ≤ 2 ^ posLevel (j + 1))
    {g : DistRd d} (hg : g ∉ posBad d lo hi R j) :
    supDistLU d R (interpProfile d lo hi (j + 1) (posNode lo hi (j + 1) m) g)
      (interpProfile d lo hi j (posNode lo hi (j + 1) m) g) ≤
        ENNReal.ofReal (posDelta j) := by
  let n := posBracket j m
  have hn : n ≤ 2 ^ posLevel j := posBracket_le hm
  have hξ := posNode_mem h hm
  by_cases hlast : n = 2 ^ posLevel j
  · have hnode : posNode lo hi (j + 1) m = posNode lo hi j n := by
      have hlow := posNode_bracket_le h j m
      have hhi := (posNode_mem h hm).2
      change posNode lo hi j n ≤ posNode lo hi (j + 1) m at hlow
      rw [hlast, posNode_last] at hlow
      have hcoarse := posNode_last lo hi j
      rw [hlast, hcoarse]
      linarith
    rw [interpProfile_node d h (j + 1) hm g, hnode,
      interpProfile_node d h j hn g]
    simp [supDistLU]
  · have hnlt : n < 2 ^ posLevel j := Nat.lt_of_le_of_ne hn hlast
    have hcell : posNode lo hi (j + 1) m ∈
        Icc (posNode lo hi j n) (posNode lo hi j (n + 1)) := by
      constructor
      · exact posNode_bracket_le h j m
      · have hbound := posNode_sub_bracket_le h j m
        rw [posNode_step]
        linarith
    let a := (posNode lo hi (j + 1) m - posNode lo hi j n) / posWidth lo hi j
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.2 hcell.1) (posWidth_pos h j).le
    have ha1 : a ≤ 1 := by
      apply (div_le_iff₀ (posWidth_pos h j)).2
      rw [posNode_step] at hcell
      linarith [hcell.2]
    rw [interpProfile_node d h (j + 1) hm g,
      interpProfile_cell d h j n hξ hnlt hcell g]
    exact supDistLU_convex_le d (posDelta_pos j).le ha ha1
      (posBad_lower_bound hm hg) (posBad_upper_bound hm hnlt hg)

theorem supd_interpProfile_succ_le_on (d : ℕ) {lo hi R ξ : ℝ}
    (h : lo < hi) (j : ℕ) (hξ : ξ ∈ Icc lo hi)
    {g : DistRd d} (hg : g ∉ posBad d lo hi R j) :
    supDistLU d R (interpProfile d lo hi (j + 1) ξ g)
      (interpProfile d lo hi j ξ g) ≤ ENNReal.ofReal (posDelta j) := by
  obtain ⟨m, hm, hcell⟩ := exists_posNode_cell h hξ (j + 1)
  let x := posNode lo hi (j + 1) m
  let y := posNode lo hi (j + 1) (m + 1)
  let a := (ξ - x) / posWidth lo hi (j + 1)
  let n := posBracket j m
  have hm1 : m + 1 ≤ 2 ^ posLevel (j + 1) := by omega
  have hn : n < 2 ^ posLevel j := posBracket_lt_of_lt hm
  have hx : x ∈ Icc lo hi := posNode_mem h hm.le
  have hy : y ∈ Icc lo hi := posNode_mem h hm1
  have hcoarse := posFineCell_mem_coarse h j m
  have hxc : x ∈ Icc (posNode lo hi j n) (posNode lo hi j (n + 1)) := hcoarse.1
  have hyc : y ∈ Icc (posNode lo hi j n) (posNode lo hi j (n + 1)) := hcoarse.2
  have hξc : ξ ∈ Icc (posNode lo hi j n) (posNode lo hi j (n + 1)) :=
    ⟨hxc.1.trans hcell.1, hcell.2.trans hyc.2⟩
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.2 hcell.1) (posWidth_pos h (j + 1)).le
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ (posWidth_pos h (j + 1))).2
    have hstep := posNode_step lo hi (j + 1) m
    linarith [hcell.2]
  have hza : ξ = (1 - a) * x + a * y := by
    have hstep := posNode_step lo hi (j + 1) m
    change y = x + posWidth lo hi (j + 1) at hstep
    dsimp [a]
    have hw : posWidth lo hi (j + 1) ≠ 0 := (posWidth_pos h (j + 1)).ne'
    rw [hstep]
    field_simp
    ring
  have hfine : interpProfile d lo hi (j + 1) ξ g =
      (1 - a) • interpProfile d lo hi (j + 1) x g +
        a • interpProfile d lo hi (j + 1) y g := by
    rw [interpProfile_cell d h (j + 1) m hξ hm hcell g,
      interpProfile_node d h (j + 1) hm.le g,
      interpProfile_node d h (j + 1) hm1 g]
  have hcoarseEq : interpProfile d lo hi j ξ g =
      (1 - a) • interpProfile d lo hi j x g +
        a • interpProfile d lo hi j y g :=
    interpProfile_affine_on_cell d h j n hn hx hy hξ hxc hyc hξc hza g
  rw [hfine, hcoarseEq]
  exact supDistLU_convex_pair_le d (posDelta_pos j).le ha ha1
    (supd_interpProfile_fine_node_le d h j m hm.le hg)
    (supd_interpProfile_fine_node_le d h j (m + 1) hm1 hg)

/-- On a good comparison event, the consecutive interpolants are uniformly close
over the whole parameter line and the given spatial ball. -/
theorem supd_interpProfile_succ_le (d : ℕ) {lo hi R : ℝ}
    (h : lo < hi) (j : ℕ) (ξ : ℝ)
    {g : DistRd d} (hg : g ∉ posBad d lo hi R j) :
    supDistLU d R (interpProfile d lo hi (j + 1) ξ g)
      (interpProfile d lo hi j ξ g) ≤ ENNReal.ofReal (posDelta j) := by
  let η := posClip lo hi ξ
  have hη : η ∈ Icc lo hi := posClip_mem h.le
  have h1 := interpProfile_clip d h.le (j + 1) ξ g
  have h0 := interpProfile_clip d h.le j ξ g
  change interpProfile d lo hi (j + 1) η g = _ at h1
  change interpProfile d lo hi j η g = _ at h0
  rw [← h1, ← h0]
  exact supd_interpProfile_succ_le_on d h j hη hg

end HigherDimLQGContinuity
