import HigherDimLQGMetric.Growth.LargeBlock

/-!
# Continuous sphere-average blocks

Packet L2a. On the almost-sure continuity event from F3, an `iSup` tail controls
every point of its compact block.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem l2a_continuous_affine_block (g : DistRd d)
    (hg : ContinuousOn (fun p : ℝ × Rd d => sphereAvg g p.1 p.2) (Ioi 0 ×ˢ univ))
    {L : Set (ℝ × Rd d)} (hL0 : ∀ p ∈ L, 0 < p.1)
    {a : ℝ} (ha : 0 < a) (w : Rd d) :
    Continuous fun p : L =>
      sphereAvg g (a * p.1.1) (a • p.1.2 + w) - sphereAvg g a w := by
  have hmap : Continuous fun p : L => (a * p.1.1, a • p.1.2 + w) := by
    fun_prop
  have hmem : ∀ p : L, (a * p.1.1, a • p.1.2 + w) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) :=
    fun p => ⟨mul_pos ha (hL0 p.1 p.2), mem_univ _⟩
  have hc := hg.comp_continuous hmap hmem
  exact hc.sub continuous_const

theorem l2a_block_point_le_of_sup_lt (g : DistRd d)
    (hg : ContinuousOn (fun p : ℝ × Rd d => sphereAvg g p.1 p.2) (Ioi 0 ×ˢ univ))
    {L : Set (ℝ × Rd d)} (hL : IsCompact L) (hL0 : ∀ p ∈ L, 0 < p.1)
    {a : ℝ} (ha : 0 < a) (w : Rd d) {A : ℝ}
    (hA : ¬ A ≤ ⨆ p : L,
      |sphereAvg g (a * p.1.1) (a • p.1.2 + w) - sphereAvg g a w|)
    (p : L) :
    |sphereAvg g (a * p.1.1) (a • p.1.2 + w) - sphereAvg g a w| ≤ A := by
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hc : Continuous fun p : L =>
      |sphereAvg g (a * p.1.1) (a • p.1.2 + w) - sphereAvg g a w| :=
    (l2a_continuous_affine_block g hg hL0 ha w).abs
  have hb : BddAbove (Set.range fun p : L =>
      |sphereAvg g (a * p.1.1) (a • p.1.2 + w) - sphereAvg g a w|) :=
    (isCompact_range hc).bddAbove
  exact (le_ciSup hb p).trans (lt_of_not_ge hA).le

end HigherDimLQGMetric
