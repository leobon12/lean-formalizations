/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QtWord
import InteractingSLE.Spec.Supplement.SB2KcStage

/-!
# Stage witnesses that are sorted, bounded and of countably many profiles

Worker PROVE-SB2-F3LAW (round 6, D80). CANON's `Cz.SB2LowerStageLawInStatement` asks the induction's word to have a
countable set of word types over all its shifts; the induction carries countable sets of word profiles
(`Lv.wordProfile`), so its base word needs them. The landed witnesses give either sortedness and a uniform bound
(`Qt.exists_stageWitness_sorted_bounded`, used by the base law) or countable profiles
(`Lv.exists_stageWitness_countable_profiles`). One strong induction gives both (same recursion
`GW1W.isStageWitness_succ_expl`):

* `exists_stageWitness_bounded_profiles`: almost surely on the launch, sorted, bounded and profile in `S`;
* **`exists_stageWitness_sorted_bounded_profiles`**: sorted and bounded at every sample (`Qt.normW`), profiles in a
  countable set at the launch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fs

open Restart Exist Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A stage witness, almost surely on the launch sorted, bounded and of profile in a countable set.** -/
theorem exists_stageWitness_bounded_profiles (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ) (S : Set Lv.WordProfile),
      IsStageWitness κ b jumps P h spec E k β Y ∧ 0 ≤ M ∧ S.Countable ∧
        ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
          (β ω).IsSorted ∧ (∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M) ∧ Lv.wordProfile (β ω) ∈ S := by
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  obtain ⟨c₀, hc₀, hc₀J, hcb⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hc : c₀.IsSorted := fun i j hij hj => hc₀.monotoneOn (lt_of_le_of_lt hij hj) hj hij
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => Exist.flowField spec.1 0 (h ω),
        ∑ i ∈ Finset.range (c₀.1 + 1), |c₀.2.2 i|, {Lv.wordProfile c₀}, GW1W.isStageWitness_zero hh hc₀J hcb,
        Finset.sum_nonneg fun i _ => abs_nonneg _, countable_singleton _,
        Eventually.of_forall fun _ _ => ⟨BoundaryWord.isSorted_shiftW hc _, ?_, rfl⟩⟩
      exact Lv.abs_shiftW_fn_le (fun x _ => Lv.abs_fn_le_sum c₀ x) spec.1
    have Hprev : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ)
        (S : Set Lv.WordProfile), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ β Y ∧ 0 ≤ M ∧ S.Countable ∧
          ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
            (β ω).IsSorted ∧ (∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M) ∧ Lv.wordProfile (β ω) ∈ S := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, M, S, hW, hM0, hS, hg⟩ := ih ℓ hℓ
        exact ⟨β, Y, M, S, fun _ => ⟨hW, hM0, hS, hg⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, 0, ∅, fun h' => absurd h' hℓ⟩
    choose β Y M S hprev using Hprev
    obtain ⟨βk, Yk, hWk, hexpl⟩ := GW1W.isStageWitness_succ_expl
      (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh hk
      (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j)
      β Y (fun ℓ hℓ => (hprev ℓ hℓ).1)
    set Mk : ℝ := ∑ ℓ ∈ Finset.range k, (M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|)) with hMk
    have hterm : ∀ ℓ ∈ Finset.range k, 0 ≤ M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|) :=
      fun ℓ hℓ => add_nonneg (hprev ℓ (Finset.mem_range.1 hℓ)).2.1 (add_nonneg hl.le (abs_nonneg _))
    have hle : ∀ ℓ < k, max (M ℓ) (sleLambda κ + |instrAngle spec ℓ * chiC κ|) ≤ Mk := by
      intro ℓ hℓ
      have hM0 := (hprev ℓ hℓ).2.1
      refine (max_le_add_of_nonneg hM0 (add_nonneg hl.le (abs_nonneg _))).trans ?_
      exact Finset.single_le_sum (f := fun ℓ => M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|))
        hterm (Finset.mem_range.2 hℓ)
    let Sk : Set Lv.WordProfile := ⋃ ℓ : Fin k, Lv.stoppedProfiles κ (instrAngle spec ℓ) (S ℓ)
    have hSk : Sk.Countable := countable_iUnion fun ℓ =>
      Lv.countable_stoppedProfiles κ (instrAngle spec ℓ) (hprev ℓ ℓ.2).2.2.1
    refine ⟨βk, Yk, Mk, Sk, hWk, Finset.sum_nonneg hterm, hSk, ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          (β ℓ ω).IsSorted ∧ (∀ y ∉ (β ℓ ω).jumps, |(β ℓ ω).fn y| ≤ M ℓ) ∧ Lv.wordProfile (β ℓ ω) ∈ S ℓ := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · exact (hprev ℓ hℓ).2.2.2.mono fun _ hω _ => hω
      · exact Eventually.of_forall fun _ h' => absurd h' hℓ
    filter_upwards [hall] with ω hω hlk
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
    have hlℓ : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hl']
      exact Option.some_ne_none _
    obtain ⟨-, hbd, hp⟩ := hω ℓ hℓk hlℓ
    rw [hexpl ℓ ω hℓk hlk hlℓ hn]
    refine ⟨BoundaryWord.isSorted_shiftW (isSorted_stopWord κ _) _, fun y hy => ?_,
      mem_iUnion.2 ⟨⟨ℓ, hℓk⟩, Lv.wordProfile_shift_stop_mem κ (instrAngle spec ℓ) _ hp _⟩⟩
    exact (Lv.abs_shiftW_fn_le (fun x hx => Lv.abs_stopWord_fn_le hκ hbd _ _ hx) _ y hy).trans (hle ℓ hℓk)

/-- **A stage witness sorted and bounded at every sample, with profiles in a countable set at the launch.** -/
theorem exists_stageWitness_sorted_bounded_profiles (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ) (S : Set Lv.WordProfile),
      IsStageWitness κ b jumps P h spec E k β Y ∧ 0 ≤ M ∧ (∀ ω, (β ω).IsSorted) ∧
        (∀ ω, ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M) ∧ S.Countable ∧
        ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
          Lv.wordProfile (β ω) ∈ S := by
  obtain ⟨β, Y, M, S, hW, hM, hS, hgood⟩ := exists_stageWitness_bounded_profiles hκ hb hh hE hreg k
  refine ⟨fun ω => Qt.normW M (β ω), Y, M, (fun p : Lv.WordProfile => (p.1, fun i => max (-M) (min M (p.2 i)))) '' S,
    ⟨(Qt.measurable_normW M).comp hW.1, hW.2.1, hW.2.2.1, ?_⟩, hM, fun ω => Qt.isSorted_normW M (β ω),
    fun ω y _ => Qt.abs_fn_normW_le hM (β ω) y, hS.image _, ?_⟩
  · filter_upwards [hW.2.2.2, hgood] with ω₀ hg hgd hl
    obtain ⟨hs, hbd, -⟩ := hgd hl
    exact Qt.isGFFWithBoundaryData_normW hs hbd (hg hl)
  · filter_upwards [hgood] with ω hg hl
    obtain ⟨hs, -, hp⟩ := hg hl
    show Lv.wordProfile (Qt.normW M (β ω)) ∈ _
    rw [Qt.normW_of_isSorted hs]
    exact ⟨_, hp, rfl⟩

end InteractingSLE.Theorem14.SB.Fs
