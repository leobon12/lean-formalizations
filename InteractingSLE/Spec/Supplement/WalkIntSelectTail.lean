/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntSelectPrefix
import InteractingSLE.Spec.Supplement.WalkIntEnvelopeRetained

/-!
# Admissible retained pairs are directed

Coordinatewise unions use actual prefixes. Choose the later of two common
exits; common-contact order makes it later on both physical curves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntSelect

open WalkIntFill WalkIntActive

/-- The existing strict contact order also preserves the non-strict order. -/
theorem common_contact_le {α β : ℝ≥0 → ℂ}
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {s s' t t' : ℝ≥0} (h : α s = β t) (h' : α s' = β t') (hss : s ≤ s') :
    t ≤ t' :=
  le_of_not_gt fun htt => (not_lt_of_ge hss) ((horder s' s t' t h' h).2 htt)

/-- A coordinatewise raw union remains before the later common exit. -/
def beforeExitOfRawUnion {sR sL : ExplState} {J K M : RetainedPair sR sL}
    {C : Set ℂ} {α β : ℝ≥0 → ℂ}
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    (hR : M.right.raw = J.right.raw ∪ K.right.raw)
    (hL : M.left.raw = J.left.raw ∪ K.left.raw)
    (B : BeforeExit J C α β) (D : BeforeExit K C α β) : BeforeExit M C α β := by
  have hex : ∃ s t : ℝ≥0,
      B.rightExit ≤ s ∧ D.rightExit ≤ s ∧ B.leftExit ≤ t ∧ D.leftExit ≤ t ∧
        α s = β t ∧ α s ∈ closure C := by
    rcases le_total B.rightExit D.rightExit with h | h
    · exact ⟨D.rightExit, D.leftExit, h, le_rfl,
        common_contact_le horder B.meet D.meet h, le_rfl, D.meet, D.exit_closure⟩
    · exact ⟨B.rightExit, B.leftExit, le_rfl, h, le_rfl,
        common_contact_le horder D.meet B.meet h, B.meet, B.exit_closure⟩
  let s := hex.choose
  let t := hex.choose_spec.choose
  obtain ⟨hBs, hDs, hBt, hDt, hmeet, hC⟩ := hex.choose_spec.choose_spec
  refine ⟨max B.rightTime D.rightTime, max B.leftTime D.leftTime, s, t,
    ?_, ?_, max_lt_iff.2 ⟨B.right_lt.trans_le hBs, D.right_lt.trans_le hDs⟩,
    max_lt_iff.2 ⟨B.left_lt.trans_le hBt, D.left_lt.trans_le hDt⟩, hmeet, hC⟩
  · rw [hR]
    exact union_subset
      (B.right_raw.trans (image_mono (Icc_subset_Icc le_rfl (le_max_left _ _))))
      (D.right_raw.trans (image_mono (Icc_subset_Icc le_rfl (le_max_right _ _))))
  · rw [hL]
    exact union_subset
      (B.left_raw.trans (image_mono (Icc_subset_Icc le_rfl (le_max_left _ _))))
      (D.left_raw.trans (image_mono (Icc_subset_Icc le_rfl (le_max_right _ _))))

/-- Actual pairs satisfying the bounded-component exit condition are
directed by raw inclusion; no directedness hypothesis is needed. -/
theorem exists_admissible_upper {sR sL : ExplState} (J K : RetainedPair sR sL)
    {C : Set ℂ} {α β : ℝ≥0 → ℂ}
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    (hJ : Bornology.IsBounded C → Nonempty (BeforeExit J C α β))
    (hK : Bornology.IsBounded C → Nonempty (BeforeExit K C α β)) :
    ∃ M : RetainedPair sR sL, J.raw ⊆ M.raw ∧ K.raw ⊆ M.raw ∧
      (Bornology.IsBounded C → Nonempty (BeforeExit M C α β)) := by
  obtain ⟨M, hR, hL⟩ := exists_retained_raw_union J K
  refine ⟨M, union_subset_union ?_ ?_, union_subset_union ?_ ?_, ?_⟩
  · rw [hR]
    exact subset_union_left
  · rw [hL]
    exact subset_union_left
  · rw [hR]
    exact subset_union_right
  · rw [hL]
    exact subset_union_right
  · intro hb
    obtain ⟨B⟩ := hJ hb
    obtain ⟨D⟩ := hK hb
    exact ⟨beforeExitOfRawUnion horder hR hL B D⟩

end InteractingSLE.Theorem14.WalkIntSelect
