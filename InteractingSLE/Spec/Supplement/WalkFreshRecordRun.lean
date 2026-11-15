/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFreshRecordBounds

/-! # Record growth and point bounds along the actual staged walk -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkFreshRecord

open Exist.Staged Exist.StagedLaw

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

def LaunchRecordData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  ∀ k, (R (k + 1)).2.2.2.1 k ≠ none → RecordsGrow (R k) (R (k + 1))

theorem run_step_recordFacts (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hG : LaunchRecordData κ b jumps θ right D) (k : ℕ) :
    let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
    RecordsGrow (R k) (R (k + 1)) ∧ (RecordBounds (R k) → RecordBounds (R (k + 1))) := by
  let w := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps w D
  change RecordsGrow (R k) (R (k + 1)) ∧ (RecordBounds (R k) → RecordBounds (R (k + 1)))
  cases hi : w.2.2[k]? with
  | none =>
    have he : R (k + 1) = R k := by dsimp only [R]; rw [run_succ, hi]
    rw [he]
    exact ⟨RecordsGrow.refl _, id⟩
  | some ins =>
    rcases ins with ⟨α, t⟩ | r | ⟨x, r⟩
    · have hf : R (k + 1) = ExplState.flowStep κ b false (R k) k (D k) α t := by
        dsimp only [R]; rw [run_succ, hi]; rfl
      by_cases hl : (R (k + 1)).2.2.2.1 k = none
      · have he : R (k + 1) = R k := hf.trans (GW1W.flowStep_eq_self_of_noLaunch _ k _ α t
          (by rw [← hf]; exact hl))
        rw [he]
        exact ⟨RecordsGrow.refl _, id⟩
      · have hg := hG k hl
        change RecordsGrow (R k) (R (k + 1)) at hg
        have he := GW1W.launch_walk hl
        change R (k + 1) = _ at he
        rw [he] at hg ⊢
        exact ⟨hg, fun hbnd => recordBounds_launch hbnd k (D k) θ hg⟩
    · have he : R (k + 1) = ExplState.contStep κ b jumps (R k) none r := by
        dsimp only [R]; rw [run_succ, hi]; rfl
      rw [he]
      exact ⟨recordsGrow_contStep _ _ _, fun hbnd => recordBounds_contStep hbnd _ _⟩
    · have he : R (k + 1) = ExplState.contStep κ b jumps (R k) (some x) r := by
        dsimp only [R]; rw [run_succ, hi]; rfl
      rw [he]
      exact ⟨recordsGrow_contStep _ _ _, fun hbnd => recordBounds_contStep hbnd _ _⟩

theorem recordsGrow_run (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hG : LaunchRecordData κ b jumps θ right D) {m n : ℕ} (hmn : m ≤ n) :
    RecordsGrow (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D m)
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  have hL : Antitone (fun k => stRecL (R k)) :=
    antitone_nat_of_succ_le fun k => (run_step_recordFacts D hG k).1.1
  have hR : Monotone (fun k => stRecR (R k)) :=
    monotone_nat_of_le_succ fun k => (run_step_recordFacts D hG k).1.2
  exact ⟨hL hmn, hR hmn⟩

theorem recordBounds_run (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hG : LaunchRecordData κ b jumps θ right D) (n : ℕ) :
    RecordBounds (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih => exact (run_step_recordFacts D hG n).2 ih

/-- The actual staged law supplies the two-ray invariant and the good
records at every launch, hence both records expand almost surely. -/
theorem ae_launchRecordData (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, LaunchRecordData κ b jumps θ right (fun j => E j ω) := by
  change ∀ᵐ ω ∂P, ∀ k,
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
    RecordsGrow (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) k)
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) (k + 1))
  refine ae_all_iff.2 fun k => ?_
  obtain ⟨β, Y, βt, Yt, -, -, hI⟩ := GW2aConn.exists_inv hκ hb hh rfl rfl hE hreg k
  filter_upwards [hI, WalkRecordSeed.ae_all_stageGood hκ hb hh hE hreg] with ω hi hg hk
  have hgood := hg k hk
  rw [GW1WalkExit.instrTime_walk_of_launch hk] at hgood
  simp only [min_top_left] at hgood
  rw [GW1W.launch_walk hk]
  exact recordsGrow_launch (hi.1 hk).1 k (E k ω) (hreg k ω) hgood.1

end InteractingSLE.Theorem14.WalkFreshRecord
