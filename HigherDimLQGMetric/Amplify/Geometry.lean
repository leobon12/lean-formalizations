import HigherDimLQGMetric.Core.Defs

/-! Elementary annulus geometry for the trial collar. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The closed witness core lies in the open trial annulus. -/
theorem amplify_core_subset_open {s : ℝ} (hs : 0 < s) (w : Rd d) :
    annCl w s (2 * s) ⊆ ann w (3 * s / 4) (3 * s) := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The closure of the trial annulus lies in the larger shell. -/
theorem amplify_closure_open_subset_shell {s : ℝ} (hs : 0 < s) (w : Rd d) :
    closure (ann w (3 * s / 4) (3 * s)) ⊆ ann w (s / 2) (5 * s) := by
  have hcl : closure (ann w (3 * s / 4) (3 * s)) ⊆
      annCl w (3 * s / 4) (3 * s) :=
    closure_minimal (ann_subset_annCl _ _ _) (isClosed_annCl _ _ _)
  intro x hx
  have h := hcl hx
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The frontier of the trial annulus is contained in its two boundary spheres. -/
theorem amplify_frontier_open_subset_spheres (s : ℝ) (w : Rd d) :
    frontier (ann w (3 * s / 4) (3 * s)) ⊆
      Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s) := by
  intro x hx
  have hcl : x ∈ annCl w (3 * s / 4) (3 * s) :=
    (closure_minimal (ann_subset_annCl _ _ _) (isClosed_annCl _ _ _)) hx.1
  have hnot : x ∉ ann w (3 * s / 4) (3 * s) := by
    simpa only [(isOpen_ann w _ _).interior_eq] using hx.2
  have hn : 3 * s / 4 = ‖x - w‖ ∨ ‖x - w‖ = 3 * s := by
    change ¬(3 * s / 4 < ‖x - w‖ ∧ ‖x - w‖ < 3 * s) at hnot
    by_cases h : 3 * s / 4 < ‖x - w‖
    · right; have h' : ¬ ‖x - w‖ < 3 * s := fun hh => hnot ⟨h, hh⟩
      linarith [hcl.2]
    · left; linarith [hcl.1]
  rcases hn with hn | hn
  · left
    change dist x w = 3 * s / 4
    rw [dist_eq_norm]
    exact hn.symm
  · right
    change dist x w = 3 * s
    rw [dist_eq_norm]
    exact hn

end HigherDimLQGMetric
