/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedMeanReg
import InteractingSLE.Spec.Supplement.SBS3TerminalCanonical
import InteractingSLE.Spec.Supplement.SBS3MarkedSchedule

/-!
# S3: all schedule prefixes with their actual mean and side alphabet
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

/-- Every schedule prefix has finite ordinary times, even beyond the end
of the program; the latter indices have no ordinary instruction. -/
theorem hasFiniteOrdinaryTimes_schedule (x₀ : ℝ) (gw2 : Bool) (τ₀ : ℝ≥0)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) :
    HasFiniteOrdinaryTimes (x₀, gw2, scheduleProgram τ₀ l) k := by
  intro j _ θ t he
  by_cases hj : j < (scheduleProgram τ₀ l).length
  · have hs := GW2Schedule.isFlowProg_scheduleProgram τ₀ l j hj
    change (scheduleProgram τ₀ l)[j]? = some (Sum.inl (θ, t)) at he
    rw [hs] at he
    have ht := (Prod.mk.inj (Sum.inl.inj (Option.some.inj he))).2
    rw [← ht]
    exact GW2Schedule.schedDelta_ne_top τ₀ l j
  · change (scheduleProgram τ₀ l)[j]? = some (Sum.inl (θ, t)) at he
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hj)] at he
    cases he

/-- One full retained-word witness for every original R51 schedule prefix,
with all physically interior values in the schedule's side alphabet after
every real recentering. No following launch or prefix-length bound occurs. -/
theorem exists_scheduleRetainedWord_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {x₀ : ℝ} {gw2 : Bool} {τ₀ : ℝ≥0}
    {l : List (ℝ × ℝ≥0)} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E)
    (hR : StagedPiecesRegular κ b jumps P (x₀, gw2, scheduleProgram τ₀ l) E) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      RetainedWordWitness κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E k β Y ∧
      ∀ᵐ ω ∂P, ∀ a y : ℝ, y ∉ (BoundaryWord.shiftW a (β ω)).jumps →
        LuM.bdVal ((ExplState.run κ b jumps (x₀, gw2, scheduleProgram τ₀ l)
          (fun j => E j ω) k).2.2.2.2.1.recenter a) (y : ℂ) ∈ H →
        Lh.SideH κ l ((BoundaryWord.shiftW a (β ω)).fn y) := by
  obtain ⟨β, Y, hW⟩ := exists_retainedWordWitness_reg hκ hb hh hE hR k
    (hasFiniteOrdinaryTimes_schedule x₀ gw2 τ₀ l k)
  refine ⟨β, Y, hW, ?_⟩
  filter_upwards [hW.sides, GW1W.regLaunches_of_stagedPiecesRegular hR] with ω hs hr a y hy hyH
  rw [bdVal_recenter_real (GW1WalkFinish.hasBdryLimits_chart_run _ _ hr k)] at hyH
  have hyJ : y + a ∉ (β ω).jumps := by
    intro h
    apply hy
    rw [BoundaryWord.jumps_shiftW]
    exact Finset.mem_image.2 ⟨y + a, h, by ring⟩
  rw [BoundaryWord.fn_shiftW]
  exact (hs (y + a) hyJ hyH).sideH

/-- Every original schedule prefix has its actual explored-set mean and
full physical word witness. All real recenterings of every harmonic mean
representative obey the same shifted-word formula on one conull event. -/
theorem exists_scheduleRetainedMean_reg
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {x₀ : ℝ} {gw2 : Bool} {τ₀ : ℝ≥0}
    {l : List (ℝ × ℝ≥0)} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E)
    (hR : StagedPiecesRegular κ b jumps P (x₀, gw2, scheduleProgram τ₀ l) E)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (k : ℕ) :
    ∃ (A : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens)
        (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps (x₀, gw2, scheduleProgram τ₀ l) E k ω) ∧
      IsLocalSetMean A (WholeField.centredField h u₀) P g ∧
      RetainedWordWitness κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E k β Y ∧
      ∀ᵐ ω ∂P, ∀ (v : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
          g ω φ = ∫ z, v z * φ z) → ∀ a : ℝ,
        EqOn (fun z => v z + u₀ z + chiC κ *
            ((ExplState.run κ b jumps (x₀, gw2, scheduleProgram τ₀ l)
              (fun j => E j ω) k).2.2.2.2.1.recenter a).2.2 z)
          (fun z => (BoundaryWord.shiftW a (β ω)).mean
            (((ExplState.run κ b jumps (x₀, gw2, scheduleProgram τ₀ l)
              (fun j => E j ω) k).2.2.2.2.1.recenter a).1 z))
          ((ExplState.run κ b jumps (x₀, gw2, scheduleProgram τ₀ l)
            (fun j => E j ω) k).2.2.2.2.1.recenter a).dom := by
  obtain ⟨A, g, β, Y, hAm, hAc, hAeq, hg, hW, hm⟩ :=
    exists_retainedMean_reg h12p h13 hκ hκ4 hb hh hE hR hu₀ k
      (hasFiniteOrdinaryTimes_schedule x₀ gw2 τ₀ l k)
  refine ⟨A, g, β, Y, hAm, hAc, hAeq, hg, hW, ?_⟩
  filter_upwards [hm] with ω hω v hv hrep a
  exact eqOn_corrected_mean_recenter (hω v hv hrep) a

end InteractingSLE.Theorem14.SB.S3
