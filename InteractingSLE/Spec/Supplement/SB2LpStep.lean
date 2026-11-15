/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LuRange
import InteractingSLE.Spec.Supplement.SB2LyRun

/-!
# SB2(2)'s lockstep run with history from the named inputs

Packet PROVE-SB2-LIFTSET (round 2). PROVE-T14-SB2LIFT's `stCorr_run_of_inputs` derives the state correspondence of the
actual and the relative walk from named inputs (regular launches, finite launched lifetimes, `NoLeftMove`,
`NoLeftHit`, no zero lifetime after the start, and at every pair of launches (L1) and `FillCorr`). The range identity
of `SB2LuRange` needs the step data `StepOK` themselves (with the piece datum `StepPiece`). This file supplies them:

* **`stepOK_of_local`**: `StepOK` at one pair of stages from the run facts there (the body of `stCorr_run_of_inputs`);
* **bounded run invariants**: `recInv_ptRec_run_le`, `stRecR_run_le_succ'`, `contSt_of_flowSt'`, **`status_run_le`**.
  SB2LIFT's `recInv_ptRec_run`/`status_run` ask for finite lifetimes at **every** launch, which fails whenever the walk
  ends with an infinite piece (the last ordinary piece of a boundary walk can reach `∞`). Here finite lifetimes are
  needed only before the last stage used; a launch with infinite lifetime finishes the walk (`run_succ_of_launch_top`);
* **`stepData_of_inputs`**: `StepOK ∧ StepPiece` at every stage of the lockstep run from the named inputs (bounded),
  and `stepData_of_done` once the actual walk is done.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R p : ℝ} {ι : ℝ → ℝ}

/-- **The step data at one pair of stages from the run facts** (the body of `stCorr_run_of_inputs`, localized):
the record invariants of both runs, the actual point at its record, the status of the actual run, and at a pair of
launches (L1) and the fill correspondence. -/
theorem stepOK_of_local (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R)) (hRp : R ≤ p)
    {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) {k₁ k₂ : ℕ}
    (hk₁ : k₁ < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hk₂ : k₂ < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hpar : k₁ % 2 = k₂ % 2)
    (hc : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂))
    (hok₁ : RecInv κ b₁ J₁ θ D₁ k₁) (hpt₁ : PtRec (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁))
    (hok₂ : RecInv κ b₂ J₂ θ D₂ k₂)
    (hp : p ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁))
    (hst : (k₂ % 2 = 0 → FlowSt p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)) ∧
      (k₂ % 2 = 1 → ContSt p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)))
    (hL1 : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k₁ + 1)).2.2.2.1 k₁ ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k₂ + 1)).2.2.2.1 k₂ ≠ none →
      ((D₂ k₂).2 = ⊤ ↔ (D₁ k₁).2 = ⊤) ∧ ((D₂ k₂).2 = 0 ↔ (D₁ k₁).2 = 0))
    (hF : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k₁ + 1)).2.2.2.1 k₁ ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k₂ + 1)).2.2.2.1 k₂ ≠ none →
      (D₁ k₁).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ k₁ b₂ J₂ D₂ k₂ ι)
    (hlh₁ : NoLeftHit κ b₁ J₁ θ D₁ k₁) (hlh₂ : NoLeftHit κ b₂ J₂ θ D₂ k₂) :
    StepOK κ θ b₁ J₁ R ι p (k₂ % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂) (D₁ k₁) (D₂ k₂) := by
  refine stepOK_of_status hRp _ hpt₁ hp ⟨fun hf => hst.1 ?_, fun hf => hst.2 ?_⟩ fun hf hst' hR hpp hadm => ?_
  · simpa using hf
  · have : ¬ k₂ % 2 = 0 := by simpa using hf
    omega
  · have hev : k₂ % 2 = 0 := by simpa using hf
    have hev₁ : k₁ % 2 = 0 := by omega
    have hl₁ := launched_of_admissible hk₁ hev₁ hst' hadm
    obtain ⟨hpt, hstat, -, hrecc⟩ := hc
    have hst₂ := hstat.trans hst'
    have hpt' : stPt (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂) =
        ι (stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)) := by
      rw [hpt, max_eq_left hpp]
    obtain ⟨-, hseed⟩ := launchReady_corr (κ := κ) (θ := θ) hι hst' hst₂ hpt' hR
    have hl₂ := launched_of_admissible hk₂ hev hst₂ (hseed.2 hadm)
    have hlne₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k₁ + 1)).2.2.2.1 k₁ ≠ none := by
      rw [hl₁]; simp
    have hlne₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k₂ + 1)).2.2.2.1 k₂ ≠ none := by
      rw [hl₂]; simp
    exact launch_obs_of_fill hι hcont hP₁ hP₂ hl₁ hl₂ hok₁ hok₂ hRp hp hrecc (hL1 hlne₁ hlne₂)
      (hF hlne₁ hlne₂) hlh₁ hlh₂


/-! ### The run invariants with finite lifetimes only before the last stage used -/

section Bounded

variable {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The record invariant and the current point at the record up to stage `N`**, with finite launched lifetimes only
before `N` (`recInv_ptRec_run` asks them at every launch, which fails when the walk ends with an infinite piece). -/
theorem recInv_ptRec_run_le {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    {N : ℕ} (hfin : ∀ j, j < N → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠
      none → (D j).2 ≠ ⊤)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j) :
    ∀ n, n ≤ N → RecInv κ b jumps θ D n ∧ PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)
  | 0, _ => by
    refine ⟨recInv_zero D, Or.inr (Or.inr ?_)⟩
    simp [ExplState.run, ExplState.init, boundaryWalkSpec]
  | n + 1, hn => by
    obtain ⟨hrec, hpt⟩ := recInv_ptRec_run_le hP hfin hlm hlh n (by omega)
    rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · exact ⟨recInv_noLaunch hP hl (walkMovesRight_of_ptRec D hpt (hlm n)) hrec, ptRec_noLaunch D hl hpt (hlm n)⟩
    · have hf := hfin n (by omega) (by rw [hl]; simp)
      exact ⟨recInv_launch hP hl hf hrec, ptRec_launch hP hl hf hpt hrec (hlh n)⟩

/-- A launch with an infinite lifetime finishes the walk and keeps the right record. -/
theorem run_succ_of_launch_top {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k = some (c, θ'))
    (htop : (D k).2 = ⊤) :
    stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) = stDone ∧
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) =
        stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) := by
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
  have e := launch_eq_of_top (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) k (D k) θ' ⊤
    (by rw [htop, min_self])
  rw [he]
  exact ⟨e.2.2.2.2.1, e.2.2.1⟩

/-- **The right record never decreases** (`stRecR_run_le_succ` with an infinite lifetime allowed). -/
theorem stRecR_run_le_succ' {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    {k : ℕ} (hok : RecInv κ b jumps θ D k) :
    stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) ≤
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) := by
  rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k with _ | ⟨c, θ'⟩
  · exact stRecR_run_le_succ hP (fun h => absurd hl h) hok
  · by_cases htop : (D k).2 = ⊤
    · exact (run_succ_of_launch_top hl htop).2.ge
    · exact stRecR_run_le_succ hP (fun _ => htop) hok

/-- **A flow step from `FlowSt` gives `ContSt`** (`contSt_of_flowSt` with an infinite lifetime allowed). -/
theorem contSt_of_flowSt' {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {p : ℝ} {k : ℕ}
    (hk : k < (boundaryWalkSpec b jumps θ true).2.2.length) (hev : k % 2 = 0)
    (hnz : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none →
      (D k).2 ≠ 0) (hlh : NoLeftHit κ b jumps θ D k)
    (hs : FlowSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) :
    ContSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) := by
  rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k with _ | ⟨c, θ'⟩
  · exact contSt_of_flowSt hk hev (fun h => absurd hl h) hnz hlh hs
  · by_cases htop : (D k).2 = ⊤
    · exact Or.inr (Or.inr (Or.inl (run_succ_of_launch_top hl htop).1))
    · exact contSt_of_flowSt hk hev (fun _ => htop) hnz hlh hs

/-- **The status invariant up to `N`** (`status_run` with finite launched lifetimes only before `N − 1`). -/
theorem status_run_le {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    {p : ℝ} (k₀ N : ℕ)
    (hfin : ∀ j, j + 1 < N → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠
      none → (D j).2 ≠ ⊤)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hN : N ≤ (boundaryWalkSpec b jumps θ true).2.2.length) (hk₀ : k₀ % 2 = 0)
    (hnz : ∀ k, k₀ ≤ k → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none →
      (D k).2 ≠ 0)
    (hp₀ : p ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k₀))
    (hs₀ : FlowSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k₀)) :
    ∀ k, k₀ ≤ k → k ≤ N → p ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) ∧
      (k % 2 = 0 → FlowSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) ∧
      (k % 2 = 1 → ContSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨hp₀, fun _ => hs₀, fun h => absurd h (by omega)⟩
  | succ k hk ih =>
    intro hkN
    have hkN' : k < N := hkN
    obtain ⟨hp, hfl, hco⟩ := ih hkN'.le
    have hlen : k < (boundaryWalkSpec b jumps θ true).2.2.length := lt_of_lt_of_le hkN' hN
    obtain ⟨hinv, hpt⟩ := recInv_ptRec_run_le hP (N := k) (fun j hj => hfin j (by omega)) hlm hlh k le_rfl
    have hp' := hp.trans (stRecR_run_le_succ' hP hinv)
    refine ⟨hp', fun hev => ?_, fun hodd => ?_⟩
    · have hodd' : k % 2 = 1 := by omega
      exact flowSt_of_contSt hlen hodd' hpt hp (hco hodd')
    · have hev' : k % 2 = 0 := by omega
      exact contSt_of_flowSt' hlen hev' (hnz k hk) (hlh k) (hfl hev')

end Bounded


/-! ### The step data along the lockstep run -/

/-- **The step data along the run from the named inputs** (`stCorr_run_of_inputs`'s inputs with finite launched
lifetimes only before the last stage used, plus the piece datum `StepPiece` at every launch): at every stage where the
states correspond, `StepOK` and `StepPiece` hold. -/
theorem stepData_of_inputs (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R)) (hRp : R ≤ p)
    {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {L : Pc → Pc → Prop}
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) (o i₀ N : ℕ)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hfin₂ : ∀ j, j + 1 < N →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hlm₂ : ∀ j, NoLeftMove κ b₂ J₂ θ D₂ j) (hlh₂ : ∀ j, NoLeftHit κ b₂ J₂ θ D₂ j)
    (hpar : o % 2 = 0) (hi₀ : i₀ % 2 = 0)
    (hlen : ∀ i, i₀ ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hNlen : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
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
      (D₁ (i + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (i + o) b₂ J₂ D₂ i ι)
    (hpc : ∀ i, i₀ ≤ i → i < N →
      StepPiece κ θ b₁ L (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i)) :
    ∀ i, i₀ ≤ i → i < N →
      StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι p (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ L (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) := by
  intro i hi hiN hc
  refine ⟨?_, hpc i hi hiN⟩
  have hk₀ : (i₀ + o) % 2 = 0 := by omega
  obtain ⟨hp, hfl, hco⟩ := status_run_le hP₁ (i₀ + o) (N + o) hfin₁ hlm₁ hlh₁ hNlen hk₀ hnz₁ hp₀ hs₀ (i + o)
    (by omega) (by omega)
  obtain ⟨hok₁, hpt₁⟩ := recInv_ptRec_run_le hP₁ (N := i + o) (fun j hj => hfin₁ j (by omega)) hlm₁ hlh₁
    (i + o) le_rfl
  obtain ⟨hok₂, -⟩ := recInv_ptRec_run_le hP₂ (N := i) (fun j hj => hfin₂ j (by omega)) hlm₂ hlh₂ i le_rfl
  obtain ⟨hk₁, hk₂⟩ := hlen i hi hiN
  refine stepOK_of_local hι hcont hRp hP₁ hP₂ hk₁ hk₂ (by omega) hc hok₁ hpt₁ hok₂ hp
    ⟨fun h => hfl (by omega), fun h => hco (by omega)⟩ (hL1 i hi hiN) (hF i hi hiN) (hlh₁ (i + o)) (hlh₂ i)

/-- **The step data at a finished actual state** (nothing happens; no launch). -/
theorem stepData_of_done {L : Pc → Pc → Prop} {s₁ s₂ : ExplState} {D₁ D₂ : (ℝ≥0 → ℝ) × ℝ≥0∞} (flow : Bool)
    (hd : stStatus s₁ = stDone) :
    StepOK κ θ b₁ J₁ R ι p flow s₁ s₂ D₁ D₂ ∧ StepPiece κ θ b₁ L flow s₁ s₂ D₁ D₂ := by
  refine ⟨?_, fun _ hst => absurd (hd.symm.trans hst) (by intro e; cases e)⟩
  cases flow
  · simp only [StepOK, Bool.false_eq_true, ↓reduceIte]
    exact Or.inl hd
  · simp only [StepOK, ↓reduceIte]
    exact Or.inl hd

end InteractingSLE.Theorem14.SB.Lk
