import SupercriticalLQGUniqueness.B2.DG20Lim.Positivity
import Mathlib.Topology.Semicontinuity.Basic

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem RData.lowerSemicontinuous_DfromR (R : RData) :
    LowerSemicontinuous (fun p : ℂ × ℂ => R.DfromR p.1 p.2) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨z, w⟩ ha
  have hzw : z ≠ w := by
    intro h
    subst w
    simp only [mem_preimage, mem_Ioi, DfromR_self] at ha
    exact not_lt_of_ge zero_le ha
  change a < R.DfromR z w at ha
  simp only [RData.DfromR, hzw, ↓reduceIte, lt_iSup_iff] at ha
  obtain ⟨O, hO, P, hP, hdisj, haOP⟩ := ha
  have hopen : IsOpen {q : ℂ × ℂ | q.1 ∈ O.openDisk ∧ q.2 ∈ P.openDisk} :=
    (isOpen_ball.preimage continuous_fst).inter
      (isOpen_ball.preimage continuous_snd)
  apply Filter.mem_of_superset (hopen.mem_nhds ⟨hO.2, hP.2⟩)
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  change a < R.DfromR u v
  have huv : u ≠ v := by
    intro h
    subst v
    exact (Set.disjoint_left.mp hdisj)
      (O.openDisk_subset_closedDisk hu) (P.openDisk_subset_closedDisk hv)
  exact haOP.trans_le (R.across_le_DfromR huv O P
    ⟨hO.1, hu⟩ ⟨hP.1, hv⟩ hdisj)

end SupercriticalLQGUniqueness.B2.DG20Lim
