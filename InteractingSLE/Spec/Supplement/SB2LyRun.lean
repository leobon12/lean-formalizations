/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LyStat

/-!
# The lockstep correspondence of the two walks from the named inputs

Packet PROVE-T14-SB2LIFT (round 13). **`stCorr_run_of_inputs`** assembles the lockstep induction
`stCorr_run_of_steps` (round 10) with:

* the record invariants of both runs (`recInv_ptRec_run`, round 12);
* the status invariant of the actual run (`status_run`, `stepOK_of_status`);
* the launch observables at every pair of corresponding launches (`launch_obs_of_fill`). At a mark with an
  admissible seed the actual walk launches (`flowStep_of_launchReady`). The relative walk is at the corresponding
  mark with an admissible seed too (`launchReady_corr`), so it launches as well.

What remains as input is:

* the starting stage (`h₀`, with the actual status a mark beyond `p`, done, or dead, and `p ≤ recR`). This is
  PROVE-SB2-LIFTSET's starting stage;
* the GW1-type inputs of both walks: finite launched lifetimes, `NoLeftMove`, `NoLeftHit`, and no zero lifetime
  after the start;
* at each pair of corresponding launches, (L1) (lifetimes infinite together and zero together) and `FillCorr`. These
  come from the lifted pieces (L4, LIFTSET) and the fill geometry.

The conclusion is the correspondence `StCorr` of the actual and the relative walk at every stage up to `N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}

/-- A flow step at a mark with an admissible seed launches. -/
theorem launched_of_admissible {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hk : k < (boundaryWalkSpec b J θ true).2.2.length) (hev : k % 2 = 0)
    (hst : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = GW1W.stArcM true)
    (hadm : ExplState.IsAdmissibleSeed κ (leftLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k)))
      (rightLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))) θ) :
    (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k =
      some (stChart (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k), θ) := by
  rw [GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := J) (θ := θ) (right := true) (D := D) hk hev,
    GW1WalkExit.flowStep_of_launchReady (Or.inr ⟨hst, hadm⟩) k (D k), launches_launch, Function.update_self]

/-- **The lockstep correspondence of the actual and the relative walk from the named inputs.** -/
theorem stCorr_run_of_inputs {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {R p : ℝ} {ι : ℝ → ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R)) (hRp : R ≤ p)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hfin₁ : ∀ j, (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none →
      (D₁ j).2 ≠ ⊤)
    (hfin₂ : ∀ j, (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      (D₂ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hlm₂ : ∀ j, NoLeftMove κ b₂ J₂ θ D₂ j) (hlh₂ : ∀ j, NoLeftHit κ b₂ J₂ θ D₂ j)
    (o i₀ N : ℕ) (hpar : o % 2 = 0) (hi₀ : i₀ % 2 = 0)
    (hlen : ∀ i, i₀ ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hNlen : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (h₀ : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i₀))
    (hnz₁ : ∀ k, i₀ + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0)
    (hp₀ : p ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o)))
    (hs₀ : FlowSt p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o)))
    (hL1 : ∀ i, i₀ ≤ i → i < N →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      ((D₂ i).2 = ⊤ ↔ (D₁ (i + o)).2 = ⊤) ∧ ((D₂ i).2 = 0 ↔ (D₁ (i + o)).2 = 0))
    (hF : ∀ i, i₀ ≤ i → i < N →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      (D₁ (i + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (i + o) b₂ J₂ D₂ i ι) :
    ∀ i, i₀ ≤ i → i ≤ N → StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) := by
  refine stCorr_run_of_steps hι hRp o i₀ N hpar hlen h₀ fun i hi hiN hc => ?_
  have hk₀ : (i₀ + o) % 2 = 0 := by omega
  obtain ⟨hp, hfl, hco⟩ := status_run hP₁ hfin₁ hlm₁ hlh₁ (i₀ + o) (N + o) hNlen hk₀ hnz₁ hp₀ hs₀ (i + o)
    (by omega) (by omega)
  obtain ⟨hok₁, hpt₁⟩ := recInv_ptRec_run hP₁ hfin₁ hlm₁ hlh₁ (i + o)
  obtain ⟨hok₂, -⟩ := recInv_ptRec_run hP₂ hfin₂ hlm₂ hlh₂ i
  obtain ⟨hk₁, hk₂⟩ := hlen i hi hiN
  refine stepOK_of_status hRp _ hpt₁ hp ⟨fun hf => hfl ?_, fun hf => hco ?_⟩ fun hf hst hR hpp hadm => ?_
  · have : i % 2 = 0 := by simpa using hf
    omega
  · have : ¬ i % 2 = 0 := by simpa using hf
    omega
  · have hev : i % 2 = 0 := by simpa using hf
    have hev₁ : (i + o) % 2 = 0 := by omega
    have hl₁ := launched_of_admissible hk₁ hev₁ hst hadm
    -- the relative walk is at the corresponding mark with an admissible seed
    obtain ⟨hpt, hstat, -, hrecc⟩ := hc
    have hst₂ := hstat.trans hst
    have hpt' : stPt (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) =
        ι (stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))) := by
      rw [hpt, max_eq_left hpp]
    obtain ⟨-, hseed⟩ := launchReady_corr (κ := κ) (θ := θ) hι hst hst₂ hpt' hR
    have hl₂ := launched_of_admissible hk₂ hev hst₂ (hseed.2 hadm)
    have hlne₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none := by
      rw [hl₁]; simp
    have hlne₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none := by
      rw [hl₂]; simp
    exact launch_obs_of_fill hι hcont hP₁ hP₂ hl₁ hl₂ hok₁ hok₂ hRp hp hrecc (hL1 i hi hiN hlne₁ hlne₂)
      (hF i hi hiN hlne₁ hlne₂) (hlh₁ (i + o)) (hlh₂ i)

end InteractingSLE.Theorem14.SB.Lk
