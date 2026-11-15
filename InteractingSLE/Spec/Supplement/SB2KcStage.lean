/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KcTypes
import InteractingSLE.Spec.Supplement.GW1ActiveLaw

/-!
# Countable profiles of the actual finite staged conditional words

The explicit stage-witness construction gives the countable profile cover
needed for SB2's force-word partition. This uses the stopped-word formula at the
last launch; no active-side classification or counterflow hypothesis is needed.
The cover is almost sure on the launch event, so arbitrary null modifications
of a staged family cause no all-sample countability requirement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A finite staged history has a conditional-word witness with countably many
profiles at its launches. Its coordinates remain measurable for the history's
own past, as required by K2. -/
theorem exists_stageWitness_countable_profiles (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens)
      (S : Set WordProfile),
      IsStageWitness κ b jumps P h spec E k β Y ∧ S.Countable ∧
        ∀ᵐ ω ∂P,
          (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
            wordProfile (β ω) ∈ S := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀,
        fun ω => Exist.flowField spec.1 0 (h ω), {wordProfile c₀},
        GW1W.isStageWitness_zero hh hc₀J hc₀, countable_singleton _, ?_⟩
      exact Eventually.of_forall fun _ _ => rfl
    have Hprev : ∀ ℓ, ∃ (β : Ω → BoundaryWord)
        (Y : Ω → DistOn upperHalfPlaneOpens) (S : Set WordProfile), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ β Y ∧ S.Countable ∧
          ∀ᵐ ω ∂P,
            (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
              wordProfile (β ω) ∈ S := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, S, hW, hS, hprof⟩ := ih ℓ hℓ
        exact ⟨β, Y, S, fun _ => ⟨hW, hS, hprof⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, ∅, fun h' => absurd h' hℓ⟩
    choose β Y S hprev using Hprev
    obtain ⟨βk, Yk, hWk, hexpl⟩ := GW1W.isStageWitness_succ_expl
      (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh hk
      (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j)
      β Y (fun ℓ hℓ => (hprev ℓ hℓ).1)
    let Sk : Set WordProfile :=
      ⋃ ℓ : Fin k, stoppedProfiles κ (instrAngle spec ℓ) (S ℓ)
    have hSk : Sk.Countable := countable_iUnion fun ℓ =>
      countable_stoppedProfiles κ (instrAngle spec ℓ) (hprev ℓ ℓ.2).2.1
    refine ⟨βk, Yk, Sk, hWk, hSk, ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          wordProfile (β ℓ ω) ∈ S ℓ := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · exact (hprev ℓ hℓ).2.2.mono fun _ hω _ => hω
      · exact Eventually.of_forall fun _ h' => absurd h' hℓ
    filter_upwards [hall] with ω hω hlk
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, -⟩ :=
      exists_last_launch spec (fun j => E j ω) hk hcθ
    have hl : (ExplState.run κ b jumps spec (fun j => E j ω)
        (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hl']
      exact Option.some_ne_none _
    rw [hexpl ℓ ω hℓk hlk hl hn]
    exact mem_iUnion.2 ⟨⟨ℓ, hℓk⟩,
      wordProfile_shift_stop_mem κ (instrAngle spec ℓ) _ (hω ℓ hℓk hl) _⟩

end InteractingSLE.Theorem14.SB.Lv
