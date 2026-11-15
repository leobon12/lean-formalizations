/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS3ProofReach

/-!
# The reach set is open in the uniform path topology

Packet PROVE-T14-TIP7, ruling R53 (follow-up note A.3: "It is an open event in the uniform path topology: each witness
`t` has strict positive margins on a compact interval"). For the Portmanteau step of DS2–DS3 in reach form
(`DSReach.DS2ReachStatement`, `DS3ReachStatement`): the set of continuous paths `f : [0, T] → X` (any metric space `X`,
e.g. the state space `ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)`) that reach an open target `O` at some time `t < T` while staying
in an open buffer `B` on `[0, t]` is open for the uniform metric.

Proof: for a witness `t`, the image of `[0, t]` is compact and contained in the open `B`, so a uniform thickening of
it is contained in `B` (`IsCompact.exists_thickening_subset_open`); a ball around `f(t)` is contained in `O`. A path
uniformly closer than both radii has the same witness.

* `reachSet`, **`isOpen_reachSet`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace InteractingSLE

namespace Supp12

namespace DSReach

variable {X : Type*} [MetricSpace X]

/-- The **reach set** of continuous paths on `[0, T]`: some time `t < T` has `f t ∈ O`, and `f u ∈ B` for all
`u ≤ t`. -/
def reachSet (T : ℝ≥0) (O B : Set X) : Set C(Set.Icc (0 : ℝ≥0) T, X) :=
  {f | ∃ t : Set.Icc (0 : ℝ≥0) T, (t : ℝ≥0) < T ∧ f t ∈ O ∧ ∀ u : Set.Icc (0 : ℝ≥0) T, u ≤ t → f u ∈ B}

/-- **The reach set is open** for the uniform metric when the target and the buffer are open. -/
theorem isOpen_reachSet (T : ℝ≥0) {O B : Set X} (hO : IsOpen O) (hB : IsOpen B) :
    IsOpen (reachSet T O B) := by
  rw [Metric.isOpen_iff]
  rintro f ⟨t, htT, hft, hfB⟩
  -- the image of `[0, t]` is compact and lies in `B`
  set K : Set X := f '' {u | u ≤ t} with hK
  have hKc : IsCompact K := ((isClosed_le continuous_id continuous_const).isCompact).image f.continuous
  have hKB : K ⊆ B := by
    rintro _ ⟨u, hu, rfl⟩
    exact hfB u hu
  obtain ⟨δ₁, hδ₁, hthick⟩ := hKc.exists_thickening_subset_open hB hKB
  obtain ⟨δ₂, hδ₂, hball⟩ := Metric.isOpen_iff.1 hO (f t) hft
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun g hg => ⟨t, htT, ?_, fun u hu => ?_⟩⟩
  · have hd : dist (g t) (f t) < δ₂ :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist t) ((mem_ball.1 hg).trans_le (min_le_right _ _))
    exact hball (mem_ball.2 hd)
  · have hd : dist (g u) (f u) < δ₁ :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist u) ((mem_ball.1 hg).trans_le (min_le_left _ _))
    refine hthick (Metric.mem_thickening_iff.2 ⟨f u, ⟨u, hu, rfl⟩, hd⟩)

end DSReach

end Supp12

end InteractingSLE
