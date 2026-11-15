/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberChart

/-!
# Lemma 7.1: the geometric clause of the mapped segment from the three-curve geometry

Packet PROVE-LEMMA71B. Specification, proof of Lemma 7.1 (`source/spec/p193-240.md` L583–L598, pp. 223–224: the
contact order (Aux. 93), the pockets (Aux. 33), the traversal of every pocket between its endpoint hits) and Remark
6.14 (pp. 217–218: "Its Jordan boundary homeomorphism makes `ψ(η_C)` a continuous simple path from zero to infinity",
"the mapped segment does not spend a nontrivial interval on `ℝ`").

The deterministic part is PROVE-WW-B4's `WangWu.IsOrderedArcs.lemma422` (Wang–Wu Lemma 4.22, the same chamber
argument). This file reads off from it the geometric clause of `Sec7.Lemma71.Lemma71MappedSegmentStatement` and of
`Lemma71B.Lemma71KilledSegmentStatement`: for three ordered simple proper arcs `η_{θ₁}` (right wall), `η` (middle),
`η_{θ₂}` (left wall) of `ℍ` whose middle-wall contact times have empty interior (Lemma 6.13's (MD1) exclusion), and
every component `C` between the walls, the middle arc traverses `C` along a clock `κ`, a boundary chart `Ψ` of `C`
exists, and the mapped segment `u ↦ Ψ(η(κ u))` is a continuous simple path in `ℍ̄` from `0` tending to `∞` whose
real-boundary times have empty interior.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.Lemma71B

/-- **The geometric clause of Lemma 7.1's mapped segment** (proof of Lemma 7.1, pp. 223–224, with Remark 6.14;
`WangWu.IsOrderedArcs.lemma422`). For three ordered simple proper arcs `R, M, L` of `ℍ` whose middle-wall contact times
have empty interior, and a component `C` between the walls, there are a traversal clock `κ` of `C` and a boundary
chart `Ψ` of `C` (`Ψ(C) ⊆ ℍ`) such that the mapped segment `u ↦ Ψ(M(κ u))` is continuous and injective on `[0, ∞)`,
lies in `ℍ̄`, starts at `0`, tends to `∞`, and its real-boundary times have empty interior. -/
theorem exists_mappedSegment_geom {R M L : ℝ → ℂ} (h : WangWu.IsOrderedArcs R M L)
    (hcR : interior {t ∈ Ici (0 : ℝ) | M t ∈ WangWu.arcRange R} = ∅)
    (hcL : interior {t ∈ Ici (0 : ℝ) | M t ∈ WangWu.arcRange L} = ∅) {C : Set ℂ}
    (hC : C ∈ betweenComponents (WangWu.arcRange R) (WangWu.arcRange L)) :
    ∃ (κ : ℝ → ℝ) (Ψ : ℂ → ℂ), ContinuousOn κ (Ici 0) ∧ StrictMonoOn κ (Ici 0) ∧
      (∀ u, 0 ≤ u → M (κ u) ∈ closure C) ∧ (∀ t, 0 ≤ t → M t ∈ C → ∃ u, 0 ≤ u ∧ κ u = t) ∧
      MapsTo Ψ C H ∧
      ContinuousOn (fun u => Ψ (M (κ u))) (Ici 0) ∧ InjOn (fun u => Ψ (M (κ u))) (Ici 0) ∧
      MapsTo (fun u => Ψ (M (κ u))) (Ici 0) Hbar ∧ Ψ (M (κ 0)) = 0 ∧
      Tendsto (fun u => ‖Ψ (M (κ u))‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (Ψ (M (κ u))).im = 0} = ∅ := by
  obtain ⟨κ, hκc, hκm, -, -, hκC, hκcov, E, yF, -, -, -, -, ⟨Ψ, hΨc, hΨi, hΨH, hΨC, hΨ0, hΨinf⟩, hall⟩ :=
    h.lemma422 hcR hcL hC
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hall Ψ hΨc hΨi hΨH hΨC hΨ0 hΨinf
  exact ⟨κ, Ψ, hκc, hκm, hκC, hκcov, hΨC, h1, h2, h3, h4, h5, h6⟩

end InteractingSLE.Sec7.Lemma71B
