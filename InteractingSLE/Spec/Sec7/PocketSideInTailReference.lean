/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailGeometry

/-!
# Rational reference times with actual unfilled incident collars

PROVE-POCKET-SIDEIN. The terminal trace determines the rational old time.
For that reference, the selected old access must land at the specified
physical point and be incident to the current domain. The theorem constructs
the collar, rather than assuming that a whole old filled hull is separated.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- At a fixed old time, incident access and terminal-trace separation
give a half-disc whose physical image lies in the actual current domain. -/
theorem exists_old_trace_halfDisc_in_current_domain {η : ℝ → ℂ}
    (hη : ContinuousOn η (Ici 0)) {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T)
    {old : Chart} (hOld : old.IsConformal) {C : Set ℂ}
    (hOldDomain : (old.dom : Set ℂ) = C ∩ (H \ fillH (η '' Icc 0 s)))
    {x : ℝ} {p : ℂ} (hLanding : Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    (hIncident : (x : ℂ) ∈ closure (old.1 '' (C ∩ (H \ fillH (η '' Icc 0 T)))))
    {r : ℝ} (hr : 0 < r) (hTail : Disjoint (η '' Icc s T) (closedBall p r)) :
    ∃ d > 0,
      old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ ball p r ∧
      old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ C ∩ (H \ fillH (η '' Icc 0 T)) ∧
      H ∩ ball (x : ℂ) d ⊆ old.1 '' (C ∩ (H \ fillH (η '' Icc 0 T))) := by
  have hTrace : η '' Icc 0 s ∪ η '' Icc s T = η '' Icc 0 T := by
    rw [← image_union, Icc_union_Icc_eq_Icc hs hsT]
  have hClosed : IsClosed (η '' Icc 0 s ∪ η '' Icc s T) := by
    rw [hTrace]
    exact (isCompact_Icc.image_of_continuousOn (hη.mono Icc_subset_Ici_self)).isClosed
  have hIncident' : (x : ℂ) ∈
      closure (old.1 '' (C ∩ (H \ fillH (η '' Icc 0 s ∪ η '' Icc s T)))) := by
    rwa [hTrace]
  simpa only [hTrace] using exists_old_halfDisc_in_current_domain
    hOld hOldDomain hClosed hLanding hIncident' hr hTail

/-- R.5's rational reference and its unfilled collar are selected together.
The named access premises are required only for the rational reference family. -/
theorem exists_rat_reference_unfilled_collar {η : ℝ → ℂ}
    (hη : ContinuousOn η (Ici 0)) {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {C : Set ℂ} {p : ℂ} (hp : p ≠ η T) {old : ℚ → Chart} {x : ℚ → ℝ}
    (hReference : ∀ s : ℚ, a < (s : ℝ) → (s : ℝ) < T →
      (old s).IsConformal ∧ (old s).dom = C ∩ (H \ fillH (η '' Icc 0 (s : ℝ))))
    (hLanding : ∀ s : ℚ, a < (s : ℝ) → (s : ℝ) < T →
      Tendsto (old s).2.1 (𝓝[H] (x s : ℂ)) (𝓝 p))
    (hIncident : ∀ s : ℚ, a < (s : ℝ) → (s : ℝ) < T →
      (x s : ℂ) ∈ closure ((old s).1 '' (C ∩ (H \ fillH (η '' Icc 0 T))))) :
    ∃ s : ℚ, a < (s : ℝ) ∧ (s : ℝ) < T ∧ ∃ r > 0, ∃ d > 0,
      Disjoint (η '' Icc (s : ℝ) T) (closedBall p r) ∧
      (old s).2.1 '' (H ∩ ball (x s : ℂ) d) ⊆ ball p r ∧
      (old s).2.1 '' (H ∩ ball (x s : ℂ) d) ⊆ C ∩ (H \ fillH (η '' Icc 0 T)) ∧
      H ∩ ball (x s : ℂ) d ⊆ (old s).1 '' (C ∩ (H \ fillH (η '' Icc 0 T))) := by
  obtain ⟨s, has, hsT, r, hr, hTail⟩ := exists_rat_terminal_trace_avoids hη ha haT hp
  obtain ⟨d, hd, hBall, hCurrent, hCoordinate⟩ := exists_old_trace_halfDisc_in_current_domain
    hη (ha.trans has.le) hsT.le (hReference s has hsT).1 (hReference s has hsT).2
    (hLanding s has hsT) (hIncident s has hsT) hr hTail
  exact ⟨s, has, hsT, r, hr, d, hd, hTail, hBall, hCurrent, hCoordinate⟩

end InteractingSLE.Sec7.PocketStopSide
