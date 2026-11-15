/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37GermCf

/-!
# Aux. lemma 37's assembly: a ball avoiding the range is filled entirely or not at all

Packet PROVE-STRIPSYS36 (continuation), bridge (b) of the handoff §5: "the hull is empty near the witness at `r`". At a
witness the arc `J` keeps a positive distance `δ` from the range `R_r` (`Aux37Witness`'s collar, item 2). A ball of
radius `δ` about a point of `J` meets `ℍ` in a convex set avoiding `closure R_r`, so it lies in one component of
`ℍ ∖ closure R_r`; hence it meets the filling `fillH R_r` (the Loewner hull of a generating trace,
`SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace`) either everywhere in `ℍ` or nowhere:

* **`inter_fillH_eq_empty_of_avoid`**: if `ball p δ` avoids `closure A` and one point of `ball p δ ∩ ℍ` is not in
  `fillH A`, then `ball p δ ∩ fillH A = ∅`.

The unfilled witness point (a pocket point of the collar at time `r`, or a later trace point) is supplied by the
assembly. Deterministic; no Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bornology

namespace InteractingSLE.Sec7.Aux37Germ

open QuantumZipper (H)

/-- **A ball avoiding the closure of `A` is filled entirely or not at all**: if `ball p δ ∩ closure A = ∅` and some
`w ∈ ball p δ ∩ ℍ` is not in `fillH A`, then no point of `ball p δ` is in `fillH A`. -/
theorem inter_fillH_eq_empty_of_avoid {A : Set ℂ} {p : ℂ} {δ : ℝ} (hav : ball p δ ∩ closure A = ∅) {w : ℂ}
    (hwb : w ∈ ball p δ) (hwH : w ∈ H) (hwf : w ∉ fillH A) : ball p δ ∩ fillH A = ∅ := by
  have hsub : ball p δ ∩ H ⊆ H \ closure A := fun z hz => ⟨hz.2, fun hzA => by
    have : z ∈ ball p δ ∩ closure A := ⟨hz.1, hzA⟩
    rw [hav] at this
    exact this⟩
  have hpc : IsPreconnected (ball p δ ∩ H) :=
    ((convex_ball p δ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hwA : w ∉ closure A := (hsub ⟨hwb, hwH⟩).2
  have hwunb : ¬ IsBounded (connectedComponentIn (H \ closure A) w) := fun hb => hwf ⟨hwH, Or.inr hb⟩
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hzb hzf
  have hzH : z ∈ H := hzf.1
  have hzA : z ∉ closure A := (hsub ⟨hzb, hzH⟩).2
  have hcw : ball p δ ∩ H ⊆ connectedComponentIn (H \ closure A) w :=
    hpc.subset_connectedComponentIn ⟨hwb, hwH⟩ hsub
  have hz_mem : z ∈ connectedComponentIn (H \ closure A) w := hcw ⟨hzb, hzH⟩
  rw [connectedComponentIn_eq hz_mem] at hwunb
  rcases hzf.2 with h | h
  · exact hzA h
  · exact hwunb h

end InteractingSLE.Sec7.Aux37Germ
