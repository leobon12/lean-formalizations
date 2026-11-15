/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCThresholdDriverAEInputs
import InteractingSLE.Spec.Restart.RetPlumbProofSplit
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas

/-!
# Force-type branches for first-contact K2 realization

The explicit common-contact word has a fixed finite height palette. Almost-sure
force bounds suffice for measurable branches, including when the chosen word has
arbitrary exceptional values. No everywhere bound on those values is imposed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCPlumb

open RetAux79
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- The explicit first-contact word uses only the original heights and the two
exposed side heights. This assertion does not require geometric ordering. -/
theorem firstContact_word_length_heights (d : PairData Ω) (c₀ : BoundaryWord)
    (hL hR : ℝ) (ω : Ω) :
    (d.word c₀ hL hR ω).1 ≤ 2 * c₀.1 + 3 ∧
      ∀ j ≤ (d.word c₀ hL hR ω).1,
        (d.word c₀ hL hR ω).2.2 j ∈ retainedHeightPalette c₀ hL hR hL hR := by
  classical
  have hk : d.wordK c₀ ω ≤ c₀.1 := card_filter_le_range _
  have hl : d.wordLe c₀ ω ≤ c₀.1 := card_filter_le_range _
  refine ⟨by dsimp [PairData.word]; omega, ?_⟩
  intro j hj
  have hq (i : ℕ) (hi : i ≤ c₀.1) :
      c₀.2.2 i ∈ retainedHeightPalette c₀ hL hR hL hR :=
    Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
  dsimp [PairData.word] at hj ⊢
  split_ifs with h₁ h₂ h₃
  · exact hq j (h₁.trans hk)
  · simp [retainedHeightPalette]
  · simp [retainedHeightPalette]
  · exact hq _ (by omega)

omit mΩ in
/-- Uniform finite force types for the explicit first-contact word, including
the truncation used by the measurable word construction. -/
theorem hasBoundedForceType_firstContact_word {κ θ : ℝ} (d : PairData Ω)
    (c₀ : BoundaryWord) (hL hR : ℝ) (ω : Ω) :
    HasBoundedForceType κ θ (2 * c₀.1 + 4)
      (flowWeightPalette κ θ (retainedHeightPalette c₀ hL hR hL hR))
      (d.word c₀ hL hR ω).trunc := by
  obtain ⟨hn, hh⟩ := firstContact_word_length_heights d c₀ hL hR ω
  exact hasBoundedForceType_of_heights (c := (d.word c₀ hL hR ω).trunc) hn hh

/-- Initial measurable fixed-type branches with an almost-sure cover. The
enumeration is finite, padded by empty sets to the record's `ℕ` index. -/
theorem exists_ae_forceType_branches {P : Measure Ω} {κ θ : ℝ} {N : ℕ}
    {weights : Finset ℝ} {𝒢 : MeasurableSpace Ω} {β : Ω → BoundaryWord} {M : Set Ω}
    (hβ : Measurable[𝒢] β) (hM : MeasurableSet[𝒢] M)
    (hb : ∀ᵐ ω ∂P, ω ∈ M → HasBoundedForceType κ θ N weights (β ω)) :
    ∃ (a : ℕ → ForceWordType) (B : ℕ → Set Ω),
      (∀ i, MeasurableSet[𝒢] (B i)) ∧
      (∀ i, B i ⊆ M ∩ β ⁻¹' forceTypeSet κ θ (a i)) ∧
      ∀ᵐ ω ∂P, ω ∈ M → ∃ i, ω ∈ B i := by
  classical
  let e := Fintype.equivFin (BoundedForceTypes N weights)
  let a (i : ℕ) : ForceWordType :=
    if hi : i < Fintype.card (BoundedForceTypes N weights) then
      boundedForceType N weights (e.symm ⟨i, hi⟩) else ⟨0, 0, 0, 0⟩
  let B (i : ℕ) : Set Ω :=
    if i < Fintype.card (BoundedForceTypes N weights) then
      M ∩ β ⁻¹' forceTypeSet κ θ (a i) else ∅
  refine ⟨a, B, ?_, ?_, ?_⟩
  · intro i
    dsimp [B]
    split_ifs
    · exact hM.inter (hβ (measurableSet_forceTypeSet κ θ (a i)))
    · exact MeasurableSet.empty
  · intro i
    dsimp [B]
    split_ifs
    · exact Subset.rfl
    · exact empty_subset _
  · filter_upwards [hb] with ω hω hωM
    obtain ⟨j, hj⟩ := exists_boundedForceType (hω hωM)
    refine ⟨(e j).val, ?_⟩
    have ha : a (e j).val = boundedForceType N weights j := by
      simp only [a, (e j).isLt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
    simpa only [B, (e j).isLt, ↓reduceIte, ha, mem_inter_iff, mem_preimage] using
      (show ω ∈ M ∧ β ω ∈ forceTypeSet κ θ (boundedForceType N weights j) from ⟨hωM, hj⟩)

end InteractingSLE.Restart.FCPlumb
