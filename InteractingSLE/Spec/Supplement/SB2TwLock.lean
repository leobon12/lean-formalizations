/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MeRel

/-!
# The lockstep with the relative walk's no-left-move derived

Packet PROVE-T14-SB2LIFT (round 20; `RunInputs.lm₂`, handoff §R19.2 2). PROVE-SB2-LIFTSET's `stepData_of_inputs` takes
`NoLeftMove` of the relative walk at every step as an input. It is used only through the relative record invariant at
the current stage, which needs `NoLeftMove` before that stage. Along the lockstep, `noLeftMove_rel_of_stCorr`
(round 19) gives it from the correspondence at that earlier stage. So a strong induction removes the input:

* `recInv_ptRec_run_le'`: LIFTSET's bounded `recInv_ptRec_run_le` with no left moves and no left hits only before `N`;
* `flowStep_of_arcM_not_adm`, `admissible_of_launched_arcM`, **`launched_of_corr_rel`**: along the correspondence
  a relative launch is matched by an actual launch (the seeds correspond, `launchReady_corr`);
* **`fin_rel_of_corr`**: hence the relative lifetimes along the lockstep are finite ((L1)'s infinite half);
* **`stCorr_run_strong`**: from LIFTSET's inputs with `NoLeftMove` and finite lifetimes of the relative walk only
  before the start (`hlm₂₀`, `hfin₂₀`), and the actual walk allowed at every stage after the start
  (`sb2LowerAllowed`, a.s.), the states
  correspond at every stage up to `N`. Moreover the step data `StepOK` hold, and the relative walk does not move left,
  at every stage before `N`;
* **`noLeftMove_rel_all`**: if moreover the actual walk is done at `N + o`, the relative walk does not move left at
  any step (`RunInputs.lm₂`);
* **`fin_rel_all`**: the relative lifetimes are finite before `N` (`RunInputs.fin₂`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkExit GW1WalkFinish
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ}

section Bounded

variable {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The record invariant up to `N` with no left moves and no left hits only before `N`.** -/
theorem recInv_ptRec_run_le' {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {N : ℕ}
    (hfin : ∀ j, j < N → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠
      none → (D j).2 ≠ ⊤)
    (hlm : ∀ j, j < N → NoLeftMove κ b jumps θ D j) (hlh : ∀ j, j < N → NoLeftHit κ b jumps θ D j) :
    ∀ n, n ≤ N → RecInv κ b jumps θ D n ∧ PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)
  | 0, _ => by
    refine ⟨recInv_zero D, Or.inr (Or.inr ?_)⟩
    simp [ExplState.run, ExplState.init, boundaryWalkSpec]
  | n + 1, hn => by
    obtain ⟨hrec, hpt⟩ := recInv_ptRec_run_le' hP hfin hlm hlh n (by omega)
    rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · exact ⟨recInv_noLaunch hP hl (walkMovesRight_of_ptRec D hpt (hlm n (by omega))) hrec,
        ptRec_noLaunch D hl hpt (hlm n (by omega))⟩
    · have hf := hfin n (by omega) (by rw [hl]; simp)
      exact ⟨recInv_launch hP hl hf hrec, ptRec_launch hP hl hf hpt hrec (hlh n (by omega))⟩

end Bounded

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R p : ℝ} {ι : ℝ → ℝ}

/-- At a mark, a flow step without an admissible seed keeps the state. -/
theorem flowStep_of_arcM_not_adm {b : ℝ → ℝ} {s : ExplState} {θ' : ℝ} (hst : stStatus s = GW1W.stArcM true)
    (hadm : ¬ ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ') (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) : ExplState.flowStep κ b false s k D θ' t = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at hst
  subst hst
  simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h
  · exact absurd h hadm
  · rfl

/-- **A launch at a mark has an admissible seed.** -/
theorem admissible_of_launched_arcM {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hk : k < (boundaryWalkSpec b J θ true).2.2.length) (hev : k % 2 = 0)
    (hst : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = GW1W.stArcM true)
    (hl : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k ≠ none) :
    ExplState.IsAdmissibleSeed κ (leftLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k)))
      (rightLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))) θ := by
  by_contra hadm
  apply hl
  rw [GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := J) (θ := θ) (right := true) (D := D) hk hev,
    flowStep_of_arcM_not_adm hst hadm]
  exact launches_run_of_le _ D le_rfl

/-- **A relative launch at a corresponding flow stage is matched by an actual launch.** -/
theorem launched_of_corr_rel {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k₁ k₂ : ℕ} (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hRp : R ≤ p)
    (hc : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂))
    (hk₁ : k₁ < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hk₂ : k₂ < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hev₁ : k₁ % 2 = 0) (hev₂ : k₂ % 2 = 0)
    (hfl : FlowSt p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁))
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k₂ + 1)).2.2.2.1 k₂ ≠ none) :
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k₁ + 1)).2.2.2.1 k₁ ≠ none := by
  obtain ⟨hpt, hstat, -, -⟩ := hc
  rcases hfl with ⟨hst₁, hpp⟩ | hd | hd
  · have hst₂ := hstat.trans hst₁
    have hpt' : stPt (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂) =
        ι (stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)) := by
      rw [hpt, max_eq_left hpp.le]
    obtain ⟨-, hseed⟩ := launchReady_corr (κ := κ) (θ := θ) hι hst₁ hst₂ hpt' (lt_of_le_of_lt hRp hpp)
    have hl₁ := launched_of_admissible hk₁ hev₁ hst₁ (hseed.1 (admissible_of_launched_arcM hk₂ hev₂ hst₂ hl₂))
    rw [hl₁]
    simp
  · exfalso
    apply hl₂
    rw [GW1WalkFinish.done_run_succ _ D₂ (hstat.trans hd)]
    exact launches_run_of_le _ D₂ le_rfl
  · exfalso
    apply hl₂
    rw [GW1W.run_succ_walk_flow (κ := κ) (b := b₂) (jumps := J₂) (θ := θ) (right := true) (D := D₂) hk₂ hev₂,
      flowStep_of_dead (hstat.trans hd)]
    exact launches_run_of_le _ D₂ le_rfl

/-- **The relative lifetimes along the lockstep are finite** (an actual launch matches each relative one, (L1)'s
infinite half and the actual finite lifetimes). -/
theorem fin_rel_of_corr (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hRp : R ≤ p) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (o i₀ N : ℕ)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
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
    {j : ℕ} (hj₀ : i₀ ≤ j) (hjN : j + 1 < N)
    (hcj : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j))
    (hl : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none) :
    (D₂ j).2 ≠ ⊤ := by
  have hk₀ : (i₀ + o) % 2 = 0 := by omega
  obtain ⟨hev₂, hk₂⟩ := GW1W.even_of_launches_walk hl
  have hev₁ : (j + o) % 2 = 0 := by omega
  obtain ⟨-, hflj, -⟩ := status_run_le hP₁ (i₀ + o) (N + o) hfin₁ hlm₁ hlh₁ hNlen hk₀ hnz₁ hp₀ hs₀ (j + o)
    (by omega) (by omega)
  have hl₁ := launched_of_corr_rel hι hRp hcj (hlen j hj₀ (by omega)).1 hk₂ hev₁ hev₂ (hflj hev₁) hl
  intro htop
  exact hfin₁ (j + o) (by omega) hl₁ ((hL1 j hj₀ (by omega) hl₁ hl).1.1 htop)

/-- **The lockstep by strong induction, with the relative walk's no-left-move derived along it.** -/
theorem stCorr_run_strong (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R)) (hRp : R ≤ p)
    {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) (o i₀ N : ℕ)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hfin₂₀ : ∀ j, j < i₀ →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hlm₂₀ : ∀ j, j < i₀ → NoLeftMove κ b₂ J₂ θ D₂ j) (hlh₂ : ∀ j, NoLeftHit κ b₂ J₂ θ D₂ j)
    (hallow : ∀ k, i₀ + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hpar : o % 2 = 0) (hi₀ : i₀ % 2 = 0)
    (hlen : ∀ i, i₀ ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hNlen : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hnz₁ : ∀ k, i₀ + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0)
    (hp₀ : p ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o)))
    (hs₀ : FlowSt p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o)))
    (h₀ : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i₀))
    (hL1 : ∀ i, i₀ ≤ i → i < N →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      ((D₂ i).2 = ⊤ ↔ (D₁ (i + o)).2 = ⊤) ∧ ((D₂ i).2 = 0 ↔ (D₁ (i + o)).2 = 0))
    (hF : ∀ i, i₀ ≤ i → i < N →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      (D₁ (i + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (i + o) b₂ J₂ D₂ i ι) :
    ∀ i, i₀ ≤ i → i ≤ N →
      (∀ j, i₀ ≤ j → j ≤ i → StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)) ∧
      (∀ j, i₀ ≤ j → j < i → StepOK κ θ b₁ J₁ R ι p (j % 2 = 0)
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j) (D₁ (j + o)) (D₂ j)) ∧
      ∀ j, j < i → NoLeftMove κ b₂ J₂ θ D₂ j := by
  have hk₀ : (i₀ + o) % 2 = 0 := by omega
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _
    refine ⟨fun j hj hji => ?_, fun j hj hji => absurd hji (by omega), hlm₂₀⟩
    rw [show j = i₀ by omega]
    exact h₀
  | succ i hi ih =>
    intro hiN
    have hiN' : i < N := hiN
    obtain ⟨hcs, hoks, hlms⟩ := ih hiN'.le
    have hc := hcs i hi le_rfl
    -- the actual walk's invariants at `i + o`
    obtain ⟨hp, hfl, hco⟩ := status_run_le hP₁ (i₀ + o) (N + o) hfin₁ hlm₁ hlh₁ hNlen hk₀ hnz₁ hp₀ hs₀ (i + o)
      (by omega) (by omega)
    obtain ⟨hok₁, hpt₁⟩ := recInv_ptRec_run_le hP₁ (N := i + o) (fun j hj => hfin₁ j (by omega)) hlm₁ hlh₁
      (i + o) le_rfl
    -- no left move of the relative walk at `i`
    have hthr : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o)) = stThr none →
        p ≤ stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o)) := fun h => by
      rcases hpt₁ with hd | hd | hpr
      · rw [h] at hd; exact absurd hd (by intro h'; cases h')
      · rw [h] at hd; exact absurd hd (by intro h'; cases h')
      · rw [hpr]; exact hp
    have hlmi := noLeftMove_rel_of_stCorr hι hRp hc (hallow (i + o) (by omega)) hthr
    have hlms' : ∀ j, j < i + 1 → NoLeftMove κ b₂ J₂ θ D₂ j := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hlms j hj
      · exact hlmi
    -- the relative lifetimes before `i` are finite
    have hfin₂ : ∀ j, j < i →
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤ :=
      fun j hj hl => by
        by_cases hj₀ : j < i₀
        · exact hfin₂₀ j hj₀ hl
        · exact fin_rel_of_corr hι hRp hP₁ o i₀ N hfin₁ hlm₁ hlh₁ hpar hi₀ hlen hNlen hnz₁ hp₀ hs₀ hL1
            (not_lt.1 hj₀) (by omega) (hcs j (not_lt.1 hj₀) hj.le) hl
    -- the relative record invariant at `i`
    obtain ⟨hok₂, -⟩ := recInv_ptRec_run_le' hP₂ (N := i) hfin₂
      (fun j hj => hlms j hj) (fun j _ => hlh₂ j) i le_rfl
    obtain ⟨hk₁, hk₂⟩ := hlen i hi hiN'
    have hokS := stepOK_of_local hι hcont hRp hP₁ hP₂ hk₁ hk₂ (by omega) hc hok₁ hpt₁ hok₂ hp
      ⟨fun _ => hfl (by omega), fun _ => hco (by omega)⟩ (hL1 i hi hiN') (hF i hi hiN') (hlh₁ (i + o)) (hlh₂ i)
    have hpar' : (i + o) % 2 = i % 2 := by omega
    have hnext := stCorr_step (κ := κ) (θ := θ) hι hRp hk₁ hk₂ hpar' hc hokS
    rw [show i + o + 1 = i + 1 + o by omega] at hnext
    refine ⟨fun j hj hji => ?_, fun j hj hji => ?_, hlms'⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hji) with h | h
      · exact hcs j hj (by omega)
      · rw [h]; exact hnext
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hji with h | rfl
      · exact hoks j hj h
      · exact hokS

/-- **The relative walk never moves left**: before the start by the start data, along the lockstep by
`stCorr_run_strong`, and after it because both walks are done (`RunInputs.lm₂`). -/
theorem noLeftMove_rel_all {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}
    (hlms : ∀ j, j < N → NoLeftMove κ b₂ J₂ θ D₂ j)
    (hcN : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N))
    (hdone : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone) :
    ∀ j, NoLeftMove κ b₂ J₂ θ D₂ j := by
  intro j
  by_cases hj : j < N
  · exact hlms j hj
  · have hd₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N) = stDone :=
      hcN.2.1.trans hdone
    have hdj := done_of_le hd₂ (not_lt.1 hj)
    refine noLeftMove_of_arcs_eq ?_
    rw [GW1WalkFinish.done_run_succ _ D₂ hdj]

/-- **The relative lifetimes are finite before `N`** (`RunInputs.fin₂`): before the start by the start data, along the
lockstep by `fin_rel_of_corr` and the correspondence of `stCorr_run_strong`. -/
theorem fin_rel_all (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hRp : R ≤ p) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (o i₀ N : ℕ)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hfin₂₀ : ∀ j, j < i₀ →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
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
    (hcs : ∀ j, i₀ ≤ j → j ≤ N → StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)) :
    ∀ j, j + 1 < N →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤ := by
  intro j hj hl
  by_cases hj₀ : j < i₀
  · exact hfin₂₀ j hj₀ hl
  · exact fin_rel_of_corr hι hRp hP₁ o i₀ N hfin₁ hlm₁ hlh₁ hpar hi₀ hlen hNlen hnz₁ hp₀ hs₀ hL1
      (not_lt.1 hj₀) hj (hcs j (not_lt.1 hj₀) (by omega)) hl

end InteractingSLE.Theorem14.SB.Lk
