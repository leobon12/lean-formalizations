/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfLocal

/-!
# Locality of a capped program whose last instruction does not launch

Packet PROVE-T14-WALKSIDE2, continuation. The last launch decision is independent
of its own time. If that instruction almost surely does not launch, the capped
program inherits the original staged law. Its earlier pieces have marked locality
by `WalkLeaf.launchLocal_of_thm12_thm13`; gluing gives locality at every stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkSideResume

open LocalSets Exist.Staged Exist.StagedLaw WalkSide

section Cap

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {w : ExplSpec}
  {ℓ : ℕ} {θ : ℝ} {τ : ℝ≥0∞}

/-- The last launch decision of a capped program is independent of its own time. -/
theorem launches_capSpec_time_indep (hℓ : ℓ ≤ w.2.2.length)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (s t : ℝ≥0∞) :
    (ExplState.run κ b jumps (capSpec w ℓ θ s) D (ℓ + 1)).2.2.2.1 =
      (ExplState.run κ b jumps (capSpec w ℓ θ t) D (ℓ + 1)).2.2.2.1 := by
  rw [run_capSpec_succ hℓ D, run_capSpec_succ hℓ D]
  exact launches_flowStep_time_indep _ _ _ _ _ _ _

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A capped program inherits the staged history when its extra instruction never
launches almost surely. The earlier coupling clauses are unchanged. -/
theorem isStagedHistory_capSpec_of_noLaunch
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : IsStagedHistory κ b jumps P h w E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hℓ : ℓ ≤ w.2.2.length)
    (hN : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (capSpec w ℓ θ τ) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = none) :
    IsStagedHistory κ b jumps P h (capSpec w ℓ θ τ) E := by
  refine ⟨hE.1, fun k => ?_, hE.2.2.1, fun k => ?_⟩
  · rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb (capSpec w ℓ θ τ)
      (k := k) (fun j _ => hE.1 j) (fun j _ => hreg j) k le_rfl).comap_le
  · rcases lt_trichotomy k ℓ with hk | rfl | hk
    · filter_upwards [hE.2.2.2 k] with ω hω c θ' hl
      rw [run_capSpec_of_le hℓ _ (Nat.succ_le_of_lt hk)] at hl
      rw [pastSigma_capSpec_of_le hℓ E hk.le]
      exact hω c θ' hl
    · filter_upwards [hN] with ω hω c θ' hl
      rw [hω] at hl
      cases hl
    · refine Eventually.of_forall fun ω c θ' hl => ?_
      rw [run_capSpec_of_ge hℓ _ (by omega : ℓ + 1 ≤ k + 1),
        launches_run_of_le (capSpec w ℓ θ τ) _ (Nat.succ_le_of_lt hk)] at hl
      cases hl

/-- Marked locality of a capped program with no last launch. Every original flow
instruction has the same angle and runs through its lifetime. The conclusion holds
at any stage, including stages after the actual end of the capped program. -/
theorem markedLocal_capSpec_of_noLaunch
    (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h w E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hword : ∀ (k : ℕ) (θ' : ℝ) (t : ℝ≥0∞),
      w.2.2[k]? = some (Sum.inl (θ', t)) → θ' = θ ∧ t = ⊤)
    (hℓ : ℓ ≤ w.2.2.length) (u₀ : ℂ → ℝ)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hN : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (capSpec w ℓ θ τ) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = none)
    (n : ℕ) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (pastSigma κ b jumps (capSpec w ℓ θ τ) E n) P]
        {ω | Disjoint (WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E n ω) U}) ∧
    (∀ᵐ ω ∂P, IsOpen (H \ WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E n ω)) ∧
    WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps (capSpec w ℓ θ τ) E n)
      (WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E n) (WholeField.centredField h u₀) P := by
  let cs := capSpec w ℓ θ τ
  have hEc : IsStagedHistory κ b jumps P h cs E :=
    isStagedHistory_capSpec_of_noLaunch hb hE hreg hℓ hN
  have hRc : StagedPiecesRegular κ b jumps P cs E :=
    stagedPiecesRegular_of_regular h13 hκ hb hEc hreg
  have hdet := fun k => WalkLaw.pastDetRegStatement_of_thm12_thm13 h12p h13
    κ hκ hκ4 b jumps hb P h hh cs E hEc hRc k
  refine WalkInf.markedLocalAE_of_kernel hb hh hu₀ hEc hRc hreg hdet (fun k => ?_) n
  refine WalkInf.kernelLocal_of_launchLocal hh.1 u₀ hEc hreg k ?_
  rcases lt_trichotomy k ℓ with hk | rfl | hk
  · refine WalkLeaf.launchLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hEc hRc
      hreg u₀ k (θ := θ) fun θ' t ht => ?_
    rw [capSpec_getElem?_of_lt hk hℓ] at ht
    exact hword k θ' t ht
  · filter_upwards [hN] with ω hω hl
    exact (hl hω).elim
  · refine Eventually.of_forall fun ω hl => False.elim (hl ?_)
    rw [run_capSpec_of_ge hℓ _ (by omega : ℓ + 1 ≤ k + 1),
      launches_run_of_le (capSpec w ℓ θ τ) _ (Nat.succ_le_of_lt hk)]

end Cap

end InteractingSLE.Theorem14.WalkSideResume
