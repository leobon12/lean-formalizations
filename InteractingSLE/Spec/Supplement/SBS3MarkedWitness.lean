/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedKernel
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas

/-!
# S3: one sorted conditional word with its actual value genealogy

Keep sortedness, the conditional law and the value origins in the same
witness. At positive stages the explicit stopped word is sorted regardless
of the representation chosen at earlier launches. Transfer this witness
back to the original retained records using R51 regularization.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- Choose the actual stage word to be sorted, with the earlier numerical
genealogy on the same launch event. -/
theorem exists_stageWitness_sorted_heightOrigin {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (β ω).IsSorted ∧ ∀ y ∉ (β ω).jumps,
          StageHeight κ b jumps spec (fun j => E j ω) k ((β ω).fn y) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨c₀, hc₀, hc₀J, hcb⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
    have hc : c₀.IsSorted := fun i j hij hj => hc₀.monotoneOn (lt_of_le_of_lt hij hj) hj hij
    refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀,
      fun ω => Exist.flowField spec.1 0 (h ω), GW1W.isStageWitness_zero hh hc₀J hcb,
      Eventually.of_forall fun ω _ => ⟨BoundaryWord.isSorted_shiftW hc _, ?_⟩⟩
    refine shiftW_values_of_predicate (fun x hx => ?_) spec.1
    have hxJ : x ∉ jumps := by rwa [← hc₀J]
    exact Or.inl ⟨x, hxJ, hcb x hxJ⟩
  · choose β Y hW hval using fun ℓ => exists_stageWitness_heightOrigin hκ hb hh hE hreg ℓ
    obtain ⟨βk, Yk, hWk, hexpl⟩ := GW1W.isStageWitness_succ_expl
      (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh hk
      (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j)
      β Y (fun ℓ _ => hW ℓ)
    refine ⟨βk, Yk, hWk, ?_⟩
    filter_upwards [ae_all_iff.2 hval] with ω hω hlk
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, -⟩ :=
      exists_last_launch spec (fun j => E j ω) hk hcθ
    have hlℓ : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hl']
      exact Option.some_ne_none _
    rw [hexpl ℓ ω hℓk hlk hlℓ hn]
    refine ⟨BoundaryWord.isSorted_shiftW (isSorted_stopWord κ _) _, ?_⟩
    apply shiftW_values_of_predicate
    refine stopWord_values_of_predicate hκ ?_ (instrAngle spec ℓ)
      (pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)) ?_ ?_
    · exact fun y hy => (hω ℓ hlℓ y hy).mono hℓk.le
    · exact Or.inr ⟨ℓ, hℓk, hlℓ, Or.inr rfl⟩
    · exact Or.inr ⟨ℓ, hℓk, hlℓ, Or.inl rfl⟩

/-- Sortedness and genealogy for the original family, with exactly R51's
almost-sure regularity hypothesis and its original retained sigma algebra. -/
theorem exists_stageWitness_sorted_heightOrigin_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (β ω).IsSorted ∧ ∀ y ∉ (β ω).jumps,
          StageHeight κ b jumps spec (fun j => E j ω) k ((β ω).fn y) := by
  obtain ⟨β, Y, hW, hvalues⟩ := exists_stageWitness_sorted_heightOrigin hκ hb hh
    (StagedReg.isStagedHistory_regHist hb hE hR) StagedReg.isRegularDriver_regHist k
  obtain ⟨β₀, hW₀, heq⟩ := exists_stageWitness_of_regHist hb hE hR hW
  refine ⟨β₀, Y, hW₀, ?_⟩
  filter_upwards [hvalues, heq, StagedReg.ae_run_regHist hR] with ω hω hword hrun hlaunch
  rw [hword]
  have hlaunch' : (ExplState.run κ b jumps spec
      (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hrun (k + 1)]
    exact hlaunch
  refine ⟨(hω hlaunch').1, fun y hy => ?_⟩
  rcases (hω hlaunch').2 y hy with hOrig | ⟨j, hj, hjlaunch, hheight⟩
  · exact Or.inl hOrig
  · rw [hrun (j + 1)] at hjlaunch
    exact Or.inr ⟨j, hj, hjlaunch, hheight⟩

end InteractingSLE.Theorem14.SB.S3
