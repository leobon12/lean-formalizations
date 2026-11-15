/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwRecRun
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# SB2(2): whole launched pieces are regular (item 4a)

Packet PROVE-SB2-LIFTSET (round 17). `StagedPiecesRegular` gives each launched piece's trace up to its own stop
`min t ζ`. The record bound needs the trace beyond an interior stop: Theorem 1.3 gives it for the whole lifetime `ζ`
(`GW1P.ae_pieceRegular_of_isFlowLineDriver` at `t = ⊤`):

* `ae_condExpKernel_pieceRegular_full`: under the conditional law at a launch;
* **`ae_pieceRegular_full_of_regular`**: `P`-almost surely, for a staged history with everywhere regular drivers
  (the proof of `Exist.StagedLaw.ae_pieceRegular_of_regular` with `t = ⊤`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1P Sec7.RandRestart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A whole launched piece is regular under its conditional law** (Theorem 1.3 at `t = ⊤`). -/
theorem ae_condExpKernel_pieceRegular_full (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    (hS : IsStagedHistory κ b jumps P h spec E) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), PieceRegular (E k ω).1 (E k ω).2 := by
  have hrec := Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 k) (hS.2.2.1 k)
  filter_upwards [hS.2.2.2 k, hrec] with ω₀ hω₀ hrecω₀ c θ hl
  obtain ⟨b', jumps', h', -, -, hfl⟩ := hω₀ c θ hl
  filter_upwards [ae_pieceRegular_of_isFlowLineDriver h13 hκ hfl hrecω₀ ⊤] with ω hω
  rwa [min_eq_right le_top] at hω

/-- **Every whole launched piece of a staged history with everywhere regular drivers is `P`-a.s. regular.** -/
theorem ae_pieceRegular_full_of_regular (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω)) (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (E k ω).1 (E k ω).2 := by
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hL : MeasurableSet L := (runMeasStatement κ b jumps hb spec E hS.1 hreg k).1
  set G : Set Ω := Lᶜ ∪ {ω | RegCond ⊤ (E k ω)} with hGdef
  have hG : MeasurableSet G := hL.compl.union (measurableSet_regCond (hS.1 k) (hreg k) ⊤)
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ G := by
    filter_upwards [ae_ae_run_eq (P := P) runMeasStatement hb spec (k := k) (fun j _ => hS.1 j)
      (fun j _ => hreg j), ae_condExpKernel_pieceRegular_full h13 hκ hS k] with ω₀ hrun hpr
    rcases hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k with _ | ⟨c, θ⟩
    · filter_upwards [hrun] with ω hω
      refine Or.inl fun hωL => hωL ?_
      show (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none
      rw [congrFun (launches_run_succ_of_run_eq spec hω) k, hl]
    · filter_upwards [hpr c θ hl] with ω hω
      refine Or.inr ((pieceRegular_iff_regCond (hreg k ω) ⊤).1 ?_)
      rwa [min_eq_right le_top]
  filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel (hS.2.1 k) hG hker] with ω hω c θ hl
  rcases hω with hω | hω
  · refine absurd ?_ hω
    show (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none
    rw [hl]
    exact Option.some_ne_none _
  · have := (pieceRegular_iff_regCond (hreg k ω) ⊤).2 hω
    rwa [min_eq_right le_top] at this

end InteractingSLE.Theorem14.SB.Lk
