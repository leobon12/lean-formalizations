/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2McPart
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier
import InteractingSLE.Spec.Supplement.SB2HEntry

/-!
# `FillCorr` from the two runs, with `OnSegFill` discharged

Packet PROVE-T14-SB2LIFT (round 17). This file assembles `fillCorr_of_liftImage` (round 16) with `onSegFill_prefix_succ`
and `onSegFill_partPrefix` (this round):

* **`isWalkSeg_prefix`**: before the walk is done and within its program, a prefix is compact
  (`Lx.isCompact_prefixPhysSet_run`), lies in the range of a parametrization of the whole walk (prefix monotonicity),
  and contains the root. What remains of `IsWalkSeg` is preconnectedness and the visit to `R`;
* `isPreconnected_tipSet`: the tip set of a regular piece is preconnected (a step of the preconnectedness invariant);
* **`fillCorr_of_runs`**: `FillCorr` at a pair of corresponding launches. It takes:
  - the run facts of both walks (regular launches, record invariants up to the launch, no left moves, finite lifetimes,
    not done);
  - the record correspondence;
  - the curve facts (`LiftCurveData`);
  - `IsWalkSeg` for the actual prefixes after the launch and at the times of the piece;
  - the relative prefixes equal to the lift images of the actual ones at matching times.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A prefix of a walk is a walk segment once it is preconnected and contains `β₀ t_L`.** -/
theorem isWalkSeg_prefix {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} {n : ℕ}
    (hn : n ≤ (boundaryWalkSpec b jumps θ true).2.2.length)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) (hβ0 : β₀ 0 = 0)
    (hconn : IsPreconnected (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hL : β₀ tL ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) :
    IsWalkSeg β₀ tL (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) := by
  refine ⟨Lx.isCompact_prefixPhysSet_run _ D hP n hst, hconn, ?_, ?_, hL⟩
  · rw [hβr, ← SB.prefixPhysSet_length]
    exact WalkIntRunChron.prefixPhysSet_mono _ D hn
  · rw [hβ0]
    unfold SB.prefixPhysSet
    exact Or.inl (Or.inl (by simp [boundaryWalkSpec]))

/-- **The tip set of a regular piece read in a chart with a proper boundary extension is preconnected** (the boundary
image of the trace on an interval of times). -/
theorem isPreconnected_tipSet {c : Chart} (hc : GW1P.HasProperBdryExt c) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (h : GW1P.PieceRegular W S) :
    IsPreconnected (c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S) := by
  obtain ⟨f, C, hf, -⟩ := hc
  obtain ⟨hW0, hWc, α, hα, -⟩ := h
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun s (hs : (s : ℝ≥0∞) < S) => (le_of_lt hs : (s : ℝ≥0∞) ≤ S))
      hW0 ht
  rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)]
  have hI : IsPreconnected {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} :=
    Set.OrdConnected.isPreconnected ⟨fun _ _ _ hy _ hz => le_trans (ENNReal.coe_le_coe.2 hz.2) hy⟩
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  refine (hI.image α hα.2.1).image f (hfc.mono ?_)
  rintro _ ⟨t, ht, rfl⟩
  exact hαH t ht

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} {ι : ℝ → ℝ}

/-- **`FillCorr` at a pair of corresponding launches from the two runs.** -/
theorem fillCorr_of_runs {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hβ : Supp9B.IsProperCurve β₀) (hD : LiftCurveData β₀ γ tL R ι)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, NoLeftMove κ b₁ J₁ θ D₁ k)
    (hst₁ : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ≠ stDone)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, NoLeftMove κ b₂ J₂ θ D₂ k)
    (hst₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ≠ stDone)
    (hseg : IsWalkSeg β₀ tL (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hP₂eq : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hsegp : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → IsWalkSeg β₀ tL (partPrefix κ b₁ J₁ θ D₁ n₁ r))
    (hmatch₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r))
    (hmatch₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r)) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι := by
  have hon : ∀ (r r' : ℝ), 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) →
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r) →
      OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
        (partPrefix κ b₁ J₁ θ D₁ n₁ r) := fun r r' hr0 hr hr0' hr' heq =>
    onSegFill_partPrefix hι.mono hRa hrecc hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hr0 hr.le
      hr0' hr'.le heq
  refine fillCorr_of_liftImage hι hβ hD hRa hseg hP₂eq
    (onSegFill_prefix_succ hι.mono hRa hrecc hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hP₂eq)
    (fun r hr0 hr => ?_) (fun r' hr0' hr' => ?_)
  · obtain ⟨r', hr0', hr', heq⟩ := hmatch₁ r hr0 hr
    exact ⟨hsegp r hr0 hr, hon r r' hr0 hr hr0' hr' heq, r', hr0', hr', heq⟩
  · obtain ⟨r, hr0, hr, heq⟩ := hmatch₂ r' hr0' hr'
    exact ⟨r, hr0, hr, hsegp r hr0 hr, hon r r' hr0 hr hr0' hr' heq, heq⟩

end InteractingSLE.Theorem14.SB.Lk
