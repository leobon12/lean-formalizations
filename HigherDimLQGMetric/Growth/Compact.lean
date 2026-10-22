import HigherDimLQGMetric.Growth.SmallLimit

/-!
# Compact-parameter bounds for the sphere-average field

Packet L2a. Joint continuity from F3 makes the field bounded on every compact
positive-radius parameter block.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem l2a_compact_sphereAvg_bound (g : DistRd d)
    (hg : ContinuousOn (fun p : ℝ × Rd d => sphereAvg g p.1 p.2) (Ioi 0 ×ˢ univ))
    {a b R : ℝ} (ha : 0 < a) (_hab : a ≤ b) (_hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, a ≤ r → r ≤ b →
      ∀ z ∈ closedBall (0 : Rd d) R, |sphereAvg g r z| ≤ M := by
  let L : Set (ℝ × Rd d) := Icc a b ×ˢ closedBall (0 : Rd d) R
  have hL : IsCompact L := isCompact_Icc.prod (isCompact_closedBall _ _)
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hmap : Continuous fun p : L => (p.1.1, p.1.2) := continuous_subtype_val
  have hmem : ∀ p : L, (p.1.1, p.1.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) :=
    fun p => ⟨ha.trans_le p.2.1.1, mem_univ _⟩
  have h0 := hg.comp_continuous hmap hmem
  have hc : Continuous fun p : L => |sphereAvg g p.1.1 p.1.2| := h0.abs
  obtain ⟨M, hM⟩ := (isCompact_range hc).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun r hr hr' z hz => ?_⟩
  have hp : ((r, z) : ℝ × Rd d) ∈ L := ⟨⟨hr, hr'⟩, hz⟩
  exact (hM ⟨⟨(r, z), hp⟩, rfl⟩).trans (le_max_left _ _)

theorem l2a_sphereAvg_le_iSup (g : DistRd d)
    (hg : ContinuousOn (fun p : ℝ × Rd d => sphereAvg g p.1 p.2) (Ioi 0 ×ˢ univ))
    {r R : ℝ} (hr : 0 < r) {z : Rd d}
    (hz : z ∈ closedBall (0 : Rd d) R) :
    |sphereAvg g r z| ≤ ⨆ w : closedBall (0 : Rd d) R, |sphereAvg g r w.1| := by
  let L : Set (Rd d) := closedBall (0 : Rd d) R
  let : CompactSpace L := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hmap : Continuous fun w : L => (r, w.1) :=
    continuous_const.prodMk continuous_subtype_val
  have hmem : ∀ w : L, (r, w.1) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) :=
    fun _ => ⟨hr, mem_univ _⟩
  have h0 := hg.comp_continuous hmap hmem
  have hc : Continuous fun w : L => |sphereAvg g r w.1| := h0.abs
  have hb : BddAbove (Set.range fun w : L => |sphereAvg g r w.1|) :=
    (isCompact_range hc).bddAbove
  exact le_ciSup hb ⟨z, hz⟩

end HigherDimLQGMetric
