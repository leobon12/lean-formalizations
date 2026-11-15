/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeRoot

/-!
# The pulled-back relative hull is the joint fill

Packet PROVE-AUX61-NOJUMP (round 22, component D), deterministic. Let `X` be compact with `fill X` a hull, and `Φ` its
hull chart (offset `x₀`). Let `p` be a continuous path on a compact parameter set `I`, with a continuous chart image
`γ`: `γ = Φ ∘ p` wherever `p` is in the chart's domain, and `Φ⁻¹ ∘ γ = p` wherever `γ` is in `ℍ`. Then the
complement of the joint fill is the pulled-back complement of the relative fill:

  **`H_diff_fillH_union_eq`**: `ℍ ∖ fill (X ∪ p(I)) = Φ⁻¹(ℍ ∖ fill γ(I))`.

The proof is the one of `Restart.fwd_image_relDomain_subset` / `Restart.inv_image_subset_relDomain` (unbounded
preconnected images avoiding a closed bounded set lie off its fill).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Ne

variable {A : Set ℂ}

theorem hullChart_fwd_spec (hA : IsHPHull A) (x₀ : ℝ) {z : ℂ} (hz : z ∈ H \ A) :
    (Mo.hullChart A x₀).1 z ∈ H ∧ (Mo.hullChart A x₀).2.1 ((Mo.hullChart A x₀).1 z) = z := by
  have hd := Mo.isDomainChart_hullChart hA x₀
  rw [← hd.2.1] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [hd.1.2.2 w hw]
  exact ⟨hw, rfl⟩

theorem hullChart_inv_mem (hA : IsHPHull A) (x₀ : ℝ) {w : ℂ} (hw : w ∈ H) : (Mo.hullChart A x₀).2.1 w ∈ H \ A := by
  have hd := Mo.isDomainChart_hullChart hA x₀
  rw [← hd.2.1]
  exact ⟨w, hw, rfl⟩

theorem continuousOn_hullChart_fwd (hA : IsHPHull A) (x₀ : ℝ) : ContinuousOn (Mo.hullChart A x₀).1 (H \ A) := by
  have h := (ConformalImage.isMapOut_mapOut hA).1.1.continuousOn
  exact h.sub continuousOn_const

theorem continuousOn_hullChart_inv (hA : IsHPHull A) (x₀ : ℝ) : ContinuousOn (Mo.hullChart A x₀).2.1 H :=
  (Mo.isConformal_hullChart hA x₀).1.continuousOn

/-- **The pulled-back relative hull is the joint fill**, for a piece `p` and its chart image `γ` on any compact parameter
set `I`: `γ = Φ ∘ p` where `p` is in the chart's domain, and `Φ⁻¹ ∘ γ = p` where `γ` is in `ℍ`. -/
theorem H_diff_fillH_union_eq {X : Set ℂ} (hXc : IsCompact X) (hA : IsHPHull (fillH X)) (x₀ : ℝ) {ι : Type*}
    [TopologicalSpace ι] {I : Set ι} (hI : IsCompact I) {γ p : ι → ℂ} (hpc : ContinuousOn p I)
    (hγc : ContinuousOn γ I) (hinv : ∀ s ∈ I, γ s ∈ H → (Mo.hullChart (fillH X) x₀).2.1 (γ s) = p s)
    (hgood : ∀ s ∈ I, p s ∈ H \ fillH X → γ s = (Mo.hullChart (fillH X) x₀).1 (p s)) :
    H \ fillH (X ∪ p '' I) = (Mo.hullChart (fillH X) x₀).2.1 '' (H \ fillH (γ '' I)) := by
  set Φ := Mo.hullChart (fillH X) x₀ with hΦ
  set P := p '' I with hPdef
  set Γ := γ '' I with hΓdef
  have hPc : IsCompact P := hI.image_of_continuousOn hpc
  have hΓc : IsCompact Γ := hI.image_of_continuousOn hγc
  have hXPc : IsCompact (X ∪ P) := hXc.union hPc
  obtain ⟨M, hM⟩ := Mo.hullChart_inv_bounded hA x₀
  have hXH : ∀ z ∈ H \ fillH X, z ∉ X := fun z hz hzX => hz.2 (mem_fillH_of_mem_closure hz.1 (subset_closure hzX))
  have hsub : H \ fillH (X ∪ P) ⊆ H \ fillH X := sdiff_subset_sdiff_right (fillH_mono subset_union_left)
  refine Subset.antisymm (fun z hz => ?_) ?_
  · -- the forward image of the joint complement avoids the relative curve
    have hY : Φ.1 '' (H \ fillH (X ∪ P)) ⊆ H \ fillH Γ := by
      refine HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hΓc.isClosed
        ((HalfPlaneSep.isPreconnected_H_diff_fillH hXPc.isClosed hXPc.isBounded).image _
          ((continuousOn_hullChart_fwd hA x₀).mono hsub)) ?_ ?_
      · intro hB
        obtain ⟨R, hR⟩ := hB.subset_closedBall 0
        refine HalfPlaneSep.not_isBounded_H_diff_fillH hXPc.isClosed hXPc.isBounded
          ((isBounded_closedBall (x := (0 : ℂ)) (r := R + M)).subset fun z' hz' => ?_)
        obtain ⟨h1, h2⟩ := hullChart_fwd_spec hA x₀ (hsub hz')
        have hb := hR ⟨z', hz', rfl⟩
        have hm := hM _ h1
        rw [h2] at hm
        rw [mem_closedBall_zero_iff] at hb ⊢
        calc ‖z'‖ ≤ ‖Φ.1 z'‖ + ‖z' - Φ.1 z'‖ := by
              have := norm_sub_le (Φ.1 z') (Φ.1 z' - z'); rw [sub_sub_cancel] at this
              rw [norm_sub_rev]; linarith [this, norm_sub_rev z' (Φ.1 z')]
          _ ≤ R + M := add_le_add hb hm
      · rintro _ ⟨z', hz', rfl⟩
        obtain ⟨h1, h2⟩ := hullChart_fwd_spec hA x₀ (hsub hz')
        refine ⟨h1, ?_⟩
        rintro ⟨s, hs, hse⟩
        have hzp : z' = p s := by rw [← h2, ← hse, hinv s hs (hse ▸ h1)]
        exact hz'.2 (mem_fillH_of_mem_closure hz'.1 (subset_closure (Or.inr ⟨s, hs, hzp.symm⟩)))
    obtain ⟨h1, h2⟩ := hullChart_fwd_spec hA x₀ (hsub hz)
    exact ⟨Φ.1 z, hY ⟨z, hz, rfl⟩, h2⟩
  · -- the inverse image of the relative complement avoids the joint set
    refine HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hXPc.isClosed
      ((HalfPlaneSep.isPreconnected_H_diff_fillH hΓc.isClosed hΓc.isBounded).image _
        ((continuousOn_hullChart_inv hA x₀).mono sdiff_subset)) ?_ ?_
    · intro hB
      obtain ⟨R, hR⟩ := hB.subset_closedBall 0
      refine HalfPlaneSep.not_isBounded_H_diff_fillH hΓc.isClosed hΓc.isBounded
        ((isBounded_closedBall (x := (0 : ℂ)) (r := R + M)).subset fun w hw => ?_)
      have h1 := hR ⟨w, hw, rfl⟩
      have h2 := hM w hw.1
      rw [mem_closedBall_zero_iff] at h1 ⊢
      calc ‖w‖ ≤ ‖Φ.2.1 w‖ + ‖Φ.2.1 w - w‖ := by
            have := norm_sub_le (Φ.2.1 w) (Φ.2.1 w - w); rwa [sub_sub_cancel] at this
        _ ≤ R + M := add_le_add h1 h2
    · rintro _ ⟨w, hw, rfl⟩
      have hzD := hullChart_inv_mem hA x₀ hw.1
      refine ⟨hzD.1, ?_⟩
      rintro (hzX | ⟨s, hs, hse⟩)
      · exact hXH _ hzD hzX
      · have hγs : γ s = w := by
          rw [hgood s hs (hse ▸ hzD), hse]
          exact (Mo.isConformal_hullChart hA x₀).2.2 w hw.1
        exact hw.2 (mem_fillH_of_mem_closure hw.1 (subset_closure ⟨s, hs, hγs⟩))

end InteractingSLE.Theorem14.SB.Ne
