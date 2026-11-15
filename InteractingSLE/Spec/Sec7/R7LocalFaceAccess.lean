/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7FaceSelectLoewner

/-!
# An untouched unbounded exterior pins the fresh target

PROVE-R7-GAPEQ. A preconnected unbounded set avoiding the frontier of a bounded open
pocket stays outside its closure. An adhering exterior whose chart image is outer thus
supplies the physical exterior access needed for the local side-identification argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Sec7.R7LocalFace

open Sec6

/-- A preconnected unbounded set disjoint from the frontier of a bounded open pocket
lies outside the pocket's closure. -/
theorem exterior_subset_compl_closure {C E : Set ℂ}
    (hCo : IsOpen C) (hCb : IsBounded C) (hE : IsPreconnected E)
    (hEb : ¬ IsBounded E) (hEfr : Disjoint E (frontier C)) : E ⊆ (closure C)ᶜ := by
  intro z hz hcl
  have hn : z ∉ C := by
    intro hC
    have hsub := subset_of_isPreconnected_of_disjoint_frontier hE hCo
      ⟨z, hz, hC⟩ hEfr
    exact hEb (hCb.subset hsub)
  exact Set.disjoint_left.1 hEfr hz ⟨hcl, by rwa [hCo.interior_eq]⟩

/-- Adherence to an exterior in the actual domain supplies an exterior access on the
outer chart side. This is an interior-domain assertion, not a prime-end identification. -/
theorem mem_closure_exterior_access {W : ℝ → ℝ} {r : ℝ} {C Γ E : Set ℂ} {x : ℂ}
    (hx : x ∈ closure E) (hED : E ⊆ H \ fwdHull W r)
    (hEC : E ⊆ (closure C)ᶜ) (hEO : fwdMap W r '' E ⊆ outerSide Γ) :
    x ∈ closure ((H \ fwdHull W r) ∩ (closure C)ᶜ ∩ (fwdMap W r ⁻¹' outerSide Γ)) := by
  apply closure_mono _ hx
  intro z hz
  exact ⟨⟨hED hz, hEC hz⟩, hEO ⟨z, hz, rfl⟩⟩

end InteractingSLE.Sec7.R7LocalFace
