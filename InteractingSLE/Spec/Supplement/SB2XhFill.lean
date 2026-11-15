/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XdChart
import InteractingSLE.Spec.Supplement.OrdGapWord

/-!
# (G1): the physical fill identity of the stage-coordinate domain

Packet PROVE-T14-SB2LIFT (round 25; the hypothesis `hfill` of `isDomainChart_stageRelChart_of_fill`). The relative
prefix at stage `j` is the lift image of B's prefix at `ℓ` (the history correspondence of the lockstep); its boundary
image under the shifted upper chart is the tail part of B's prefix, and B's head lies in the hull of the upper prefix:

* **`image_ext_liftImage`**: the boundary extension of the upper-chart inverse, shifted by `m`, maps the lift image
  of `S` onto `S ∩ β₀ '' [t_L, ∞)` (`IsTailLiftCurve`: the boundary value at `γ s − m` is `β₀ (t_L + s)`);
* **`fillH_tail_eq`**: if B's prefix lies on `β₀`, is compact, and B's head `β₀ '' [0, t_L]` lies in `hullK A`, then
  `fill (A ∪ (B ∩ β₀ '' [t_L, ∞))) = fill (A ∪ B)` (`RLC.OrdGap.fillH_union_eq_of_subset`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Lk

/-- **The shifted boundary extension of the upper chart maps a lift image to the tail part.** -/
theorem image_ext_liftImage {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) {ĝ : ℂ → ℂ} (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p)))
    (S : Set ℂ) : (fun y => ĝ (y - (m : ℂ))) '' liftImage β₀ tL γ S = S ∩ β₀ '' Ici tL := by
  have hval : ∀ s : ℝ≥0, ĝ (γ s - (m : ℂ)) = β₀ (tL + s) := fun s => by
    have hmem : γ s - (m : ℂ) ∈ Hbar := show 0 ≤ (γ s - (m : ℂ)).im by simpa using hγ.2.1.2.2.1 s
    have : (𝓝[H] (γ s - (m : ℂ))).NeBot := GW1P.neBot_nhdsWithin_H hmem
    exact tendsto_nhds_unique (hĝ _ hmem) (hγ.2.2.2 s)
  ext z
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    show ĝ (γ s - (m : ℂ)) ∈ S ∩ β₀ '' Ici tL
    rw [hval s]
    exact ⟨hs, tL + s, (show tL ≤ tL + s from le_self_add), rfl⟩
  · rintro ⟨hzS, x, hx, rfl⟩
    have hx' : tL + (x - tL) = x := add_tsub_cancel_of_le (show tL ≤ x from hx)
    refine ⟨γ (x - tL), ⟨x - tL, show β₀ (tL + (x - tL)) ∈ S by rw [hx']; exact hzS, rfl⟩, ?_⟩
    show ĝ (γ (x - tL) - (m : ℂ)) = β₀ x
    rw [hval, hx']

/-- **The fill of the upper prefix with B's tail part is the fill of the retained union**, when B's prefix lies on
`β₀` and B's head lies in the hull of the upper prefix. -/
theorem fillH_tail_eq {A B : Set ℂ} {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} (hβ : Continuous β₀) (hA : IsCompact A)
    (hB : IsCompact B) (hBr : B ⊆ range β₀) (hhead : β₀ '' Icc 0 tL ⊆ hullK A)
    (hcl : IsClosed (β₀ '' Ici tL)) :
    fillH (A ∪ (B ∩ β₀ '' Ici tL)) = fillH (A ∪ B) := by
  have hK : IsCompact (β₀ '' Icc 0 tL) := isCompact_Icc.image hβ
  have hA' : IsCompact (B ∩ β₀ '' Icc 0 tL) := hB.inter_right hK.isClosed
  have hB' : IsCompact (A ∪ (B ∩ β₀ '' Ici tL)) := hA.union (hB.inter_right hcl)
  have hsub : (B ∩ β₀ '' Icc 0 tL) ∩ H ⊆ fillH (A ∪ (B ∩ β₀ '' Ici tL)) := by
    rintro z ⟨⟨-, hzh⟩, hzH⟩
    rcases hhead hzh with h | ⟨x, -, rfl⟩
    · exact fillH_mono subset_union_left h
    · exact absurd hzH (by simp [QuantumZipper.H])
  have hU : (B ∩ β₀ '' Icc 0 tL) ∪ (A ∪ (B ∩ β₀ '' Ici tL)) = A ∪ B := by
    ext z
    constructor
    · rintro ((⟨hz, -⟩) | (hz | ⟨hz, -⟩))
      · exact Or.inr hz
      · exact Or.inl hz
      · exact Or.inr hz
    · rintro (hz | hz)
      · exact Or.inr (Or.inl hz)
      · obtain ⟨t, rfl⟩ := hBr hz
        rcases le_total t tL with h | h
        · exact Or.inl ⟨hz, t, ⟨zero_le, h⟩, rfl⟩
        · exact Or.inr (Or.inr ⟨hz, t, h, rfl⟩)
  rw [← hU, RLC.OrdGap.fillH_union_eq_of_subset hA' hB' hsub]

end InteractingSLE.Theorem14.SB.Mn
