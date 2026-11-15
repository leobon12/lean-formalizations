/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailLimit
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# A nonterminal current boundary point is on the old boundary

PROVE-POCKET-SIDEIN. Inside the initial pocket, the frontier of the current
filled-trace complement lies on the compact trace. Away from the terminal
tip, its hitting time is strictly earlier. Outside the initial pocket it
is excluded from every old pocket domain already.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A reference time sufficiently close to the current time sees the
specified nonterminal current boundary point on its own boundary. -/
theorem exists_old_interval_excluding_current_frontier {η : ℝ → ℂ}
    (hη : ContinuousOn η (Ici 0)) {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H)
    {a₀ T : ℝ} (ha₀ : 0 ≤ a₀) (haT : a₀ < T) {p : ℂ}
    (hFrontier : p ∈ frontier (C ∩ (H \ fillH (η '' Icc 0 T)))) (hNotTip : p ≠ η T) :
    ∃ a : ℝ, 0 ≤ a ∧ a₀ ≤ a ∧ a < T ∧
      ∀ s : ℝ, a < s → p ∉ C ∩ (H \ fillH (η '' Icc 0 s)) := by
  by_cases hpC : p ∈ C
  · have hpF : p ∈ frontier (H \ fillH (η '' Icc 0 T)) := by
      rcases frontier_inter_subset C (H \ fillH (η '' Icc 0 T)) hFrontier with ⟨hp, -⟩ | ⟨-, hp⟩
      · rw [hCo.frontier_eq] at hp
        exact False.elim (hp.2 hpC)
      · exact hp
    have hCompact : IsCompact (η '' Icc 0 T) := isCompact_Icc.image_of_continuousOn (hη.mono Icc_subset_Ici_self)
    have hpTrace : p ∈ η '' Icc 0 T := by
      rcases frontier_H_diff_fillH_subset hCompact.isBounded hpF with hp | hp
      · exact False.elim ((ne_of_gt (hCH hpC)) hp)
      · rwa [hCompact.isClosed.closure_eq] at hp
    obtain ⟨u, hu, hup⟩ := hpTrace
    have huT : u < T := hu.2.lt_of_ne fun he => hNotTip (by rw [← hup, he])
    refine ⟨max a₀ u, ha₀.trans (le_max_left _ _), le_max_left _ _, max_lt haT huT, ?_⟩
    intro s hs hp
    apply hp.2.2
    exact mem_fillH_of_mem_closure hp.2.1 (subset_closure
      ⟨u, ⟨hu.1, (le_max_right a₀ u).trans hs.le⟩, hup⟩)
  · exact ⟨a₀, ha₀, le_rfl, haT, fun _ _ hp => hpC hp.1⟩

end InteractingSLE.Sec7.PocketStopSide
