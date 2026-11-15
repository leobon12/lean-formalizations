/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedPhysical
import InteractingSLE.Spec.Supplement.SBS3MarkedWitness
import InteractingSLE.Spec.Supplement.WalkUnionLawMain

/-!
# S3: actual conditional words have physical side provenance

At every launched stage, choose one sorted word with its actual conditional
GFF law and its physical interior-side invariant. Arbitrary initial boundary
values are allowed. Original real data are excluded by the physical landing,
not by deleting a numerical branch of the word genealogy.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- A word's values at physical interior landings come from actually
launched earlier sides of the same run. -/
def HasInteriorStageSides (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (word : BoundaryWord) : Prop :=
  ∀ y ∉ word.jumps,
    LuM.bdVal (ExplState.run κ b jumps spec D k).2.2.2.2.1 (y : ℂ) ∈ H →
      StageSide κ b jumps spec D k (word.fn y)

/-- A sorted conditional-law witness with physical side provenance, for a
family regular at every sample and with R51's regular launched pieces. -/
theorem exists_stageWitness_interiorStageSides {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (β ω).IsSorted ∧ HasInteriorStageSides κ b jumps spec (fun j => E j ω) k (β ω) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨c₀, hc₀, hc₀J, hcb⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
      have hc : c₀.IsSorted := fun i j hij hj => hc₀.monotoneOn (lt_of_le_of_lt hij hj) hj hij
      refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀,
        fun ω => Exist.flowField spec.1 0 (h ω), GW1W.isStageWitness_zero hh hc₀J hcb,
        Eventually.of_forall fun ω _ => ⟨BoundaryWord.isSorted_shiftW hc _, ?_⟩⟩
      intro y _ hyH
      change LuM.bdVal (Chart.id.recenter spec.1) (y : ℂ) ∈ H at hyH
      rw [bdVal_init_real] at hyH
      simp [QuantumZipper.H] at hyH
    · have Hprev : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
          ℓ < k → IsStageWitness κ b jumps P h spec E ℓ β Y ∧
            ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
              (β ω).IsSorted ∧ HasInteriorStageSides κ b jumps spec (fun j => E j ω) ℓ (β ω) := by
        intro ℓ
        by_cases hℓ : ℓ < k
        · obtain ⟨β, Y, hW, hSide⟩ := ih ℓ hℓ
          exact ⟨β, Y, fun _ => ⟨hW, hSide⟩⟩
        · exact ⟨fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
      choose β Y hprev using Hprev
      obtain ⟨βk, Yk, hWk, hexpl⟩ := GW1W.isStageWitness_succ_expl
        (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh hk
        (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j)
        β Y (fun ℓ hℓ => (hprev ℓ hℓ).1)
      have hPrior : ∀ ℓ, ∀ᵐ ω ∂P, ℓ < k →
          (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          (β ℓ ω).IsSorted ∧ HasInteriorStageSides κ b jumps spec (fun j => E j ω) ℓ (β ℓ ω) := by
        intro ℓ
        by_cases hℓ : ℓ < k
        · exact (hprev ℓ hℓ).2.mono fun _ hω _ => hω
        · exact Eventually.of_forall fun _ h' => absurd h' hℓ
      have hGood : ∀ ℓ, ∀ᵐ ω ∂P, ℓ < k →
          (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ →
          LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω))) := by
        intro ℓ
        by_cases hℓ : ℓ < k
        · have hW := (hprev ℓ hℓ).1
          have hp := post_stage (spec := spec) (E := E) (ℓ := ℓ) (β := β ℓ) (Y := Y ℓ)
            (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
            (fun j _ => hE.1 j) (fun j _ => hreg j) (hE.2.2.2 ℓ)
            hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
          exact hp.1.mono fun _ hω _ => hω
        · exact Eventually.of_forall fun _ h' => absurd h' hℓ
      refine ⟨βk, Yk, hWk, ?_⟩
      filter_upwards [ae_all_iff.2 hPrior, ae_all_iff.2 hGood,
        GW1W.regLaunches_of_stagedPiecesRegular hR] with ω hp hg hr hlk
      obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
      obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, -⟩ :=
        exists_last_launch spec (fun j => E j ω) hk hcθ
      have hlℓ : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
        rw [hl']; exact Option.some_ne_none _
      have he := hexpl ℓ ω hℓk hlk hlℓ hn
      rw [pastMap_last_of_launch hlℓ] at he
      refine ⟨?_, ?_⟩
      · rw [he]
        exact BoundaryWord.isSorted_shiftW (isSorted_stopWord κ _) _
      · exact interior_stageSide_of_last_launch hκ hr hℓk hlk hlℓ hn (hreg ℓ ω)
          (hg ℓ hℓk hlℓ (last_launch_props hℓk hlk hlℓ hn).1) (hp ℓ hℓk hlℓ).2 he

/-- Physical provenance for an actual stage word under exactly R51, with
its conditional law measurable for the original retained past. -/
theorem exists_stageWitness_interiorStageSides_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (β ω).IsSorted ∧ HasInteriorStageSides κ b jumps spec (fun j => E j ω) k (β ω) := by
  obtain ⟨βr, Y, hW, hSide⟩ := exists_stageWitness_interiorStageSides hκ hb hh
    (StagedReg.isStagedHistory_regHist hb hE hR) (WalkLaw.stagedPiecesRegular_regHist hR)
    StagedReg.isRegularDriver_regHist k
  obtain ⟨β, hW₀, heq⟩ := exists_stageWitness_of_regHist hb hE hR hW
  refine ⟨β, Y, hW₀, ?_⟩
  filter_upwards [hSide, heq, StagedReg.ae_run_regHist hR] with ω hs hw hr hlaunch
  have hlaunch' : (ExplState.run κ b jumps spec
      (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hr (k + 1)]; exact hlaunch
  rw [hw]
  refine ⟨(hs hlaunch').1, fun y hy hyH => ?_⟩
  have hyH' : LuM.bdVal (ExplState.run κ b jumps spec
      (fun j => StagedReg.regHist spec E j ω) k).2.2.2.2.1 (y : ℂ) ∈ H := by
    rw [hr k]; exact hyH
  obtain ⟨j, hj, hjL, hjH⟩ := (hs hlaunch').2 y hy hyH'
  rw [hr (j + 1)] at hjL
  exact ⟨j, hj, hjL, hjH⟩

end InteractingSLE.Theorem14.SB.S3
