/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMarkSeedRestart

/-! # Actual later walk launches have admissible active seeds and nonzero lifetime -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkMarkSeed

open Exist.Staged Exist.StagedLaw Restart WalkLaterSeed WalkCapBlock

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The actual stage witnesses can be chosen with admissible seeds at every
later launch. The word is identified through the explicit last-launch
formula, including all retained past information. -/
theorem laterStageSeedData (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) : LaterStageSeedData κ b jumps θ right P h E := by
  classical
  let spec := boundaryWalkSpec b jumps θ right
  have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E ℓ β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        GW2aConn.GInv b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) := by
    intro ℓ
    obtain ⟨β, Y, βt, Yt, hW, -, hI⟩ := GW2aConn.exists_inv hκ hb hh rfl rfl hE hreg ℓ
    exact ⟨β, Y, hW, hI.mono fun _ hω hl => (hω.1 hl).1⟩
  choose β Y hW hI using H
  intro k hk0
  obtain ⟨βk, Yk, hWk, hβk⟩ := GW1W.isStageWitness_succ_expl (GW1W.isStopLaw_stopWord hκ)
    runMeasStatement hκ hb hh hk0 (fun j _ => hE.1 j) (fun j _ => hreg j)
    (fun j _ => hE.2.2.2 j) β Y (fun ℓ _ => hW ℓ)
  refine ⟨βk, Yk, hWk, ?_⟩
  filter_upwards [ae_all_iff.2 hI, WalkRecordSeed.ae_all_stageGood hκ hb hh hE hreg] with ω hi hg hk
  obtain ⟨⟨c, α⟩, hc⟩ := Option.ne_none_iff_exists'.1 hk
  obtain ⟨ℓ, hℓk, ⟨c', α', hl'⟩, hstop, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk0 hc
  have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [hl']; exact Option.some_ne_none _
  have he := hβk ℓ ω hℓk hk hl hn
  rw [pastMap_last_of_launch hl, GW1W.instrAngle_walk hl,
    GW1WalkExit.instrTime_walk_of_launch hl] at he
  have hfin : (E ℓ ω).2 ≠ ⊤ := by
    have ht : instrTime spec ℓ = ⊤ := GW1WalkExit.instrTime_walk_of_launch hl
    simpa only [ht, min_top_left] using hstop
  have hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω))) := by
    simpa only [GW1WalkExit.instrTime_walk_of_launch hl] using (hg ℓ hl).1 hstop
  rw [he]
  exact admissible_next_word hκ hb (fun j => E j ω) hℓk hk hl hn (hi ℓ hl) (hreg ℓ ω) hfin hgood

/-- Nonzero lifetime at every actual later launch, for arbitrary original
boundary data. No side-height bound or trace-existence theorem is needed. -/
theorem ae_noZeroLaterLaunchData (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, NoZeroLaterLaunchData κ b jumps θ right (fun j => E j ω) :=
  ae_noZeroLaterLaunchData_of_stageSeeds hκ hb hh hE hreg (laterStageSeedData hκ hb hh hE hreg)

/-- All original seed assertions for every boundary walk follow from its
actual staged law. No open exit, freshness, or seed hypothesis remains. -/
theorem ae_walkSeedData (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, WalkSeedData κ b jumps θ right (fun j => E j ω) :=
  WalkFreshRecord.ae_walkSeedData_of_noZero hκ hb hh hE hreg
    (ae_noZeroLaterLaunchData hκ hb hh hE hreg)

end InteractingSLE.Theorem14.WalkMarkSeed
