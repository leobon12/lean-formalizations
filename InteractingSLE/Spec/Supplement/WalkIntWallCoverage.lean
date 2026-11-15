/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntWallCollar

/-!
# Compact coordinate segments lie in one incident interval

For a nested retained raw family, the supported-coordinate interiors form
an increasing open family. The existing directed compact-cover theorem
puts the entire segment from the anchor to a coordinate in one member.
Connectedness then puts that segment in the anchor's incident interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex

namespace InteractingSLE.Theorem14.WalkIntWall

open WalkIntNeighborhood

/-- Pointwise supported neighborhoods cover the whole compact coordinate
segment in one retained incident interval. -/
theorem exists_incidentInterval_cover_uIcc (c : Chart) (F : ℕ → Set ℂ)
    (hmono : Monotone F) (anchor x : ℝ)
    (hcover : ∀ y ∈ uIcc anchor x, ∃ i, y ∈ interior (landingCoordinates c (F i))) :
    ∃ i, uIcc anchor x ⊆ incidentInterval c (F i) anchor := by
  let U : ℕ → Set ℝ := fun i => interior (landingCoordinates c (F i))
  have hUmono : Monotone U := fun i j hij =>
    interior_mono (landingCoordinates_mono c (hmono hij))
  have hUcover : uIcc anchor x ⊆ ⋃ i, U i := by
    intro y hy
    obtain ⟨i, hi⟩ := hcover y hy
    exact mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨i, hi⟩ := (isCompact_uIcc : IsCompact (uIcc anchor x)).elim_directed_cover U
    (fun _ => isOpen_interior) hUcover
    (fun i j => ⟨max i j, hUmono (le_max_left i j), hUmono (le_max_right i j)⟩)
  exact ⟨i, isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hi⟩

/-- Coverage can be obtained above any prescribed retained index. This
allows later matching arguments to preserve an already chosen hull bound. -/
theorem exists_incidentInterval_cover_uIcc_ge (c : Chart) (F : ℕ → Set ℂ)
    (hmono : Monotone F) (anchor x : ℝ) (lower : ℕ)
    (hcover : ∀ y ∈ uIcc anchor x, ∃ i, y ∈ interior (landingCoordinates c (F i))) :
    ∃ i, lower ≤ i ∧ uIcc anchor x ⊆ incidentInterval c (F i) anchor := by
  obtain ⟨i, hi⟩ := exists_incidentInterval_cover_uIcc c F hmono anchor x hcover
  exact ⟨max lower i, le_max_left _ _,
    hi.trans (incidentInterval_mono c anchor (hmono (le_max_right lower i)))⟩

end InteractingSLE.Theorem14.WalkIntWall
