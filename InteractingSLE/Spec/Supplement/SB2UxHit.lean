/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2UxProf
import InteractingSLE.Spec.Supplement.BW1PropTip

/-!
# The lockstep with the relative walk's no-left-hit derived

Packet PROVE-T14-SB2LIFT (round 21; `RunInputs.lh₂`, handoff §R20.2 1). In the lockstep, every relative launch is
matched by an actual launch (`launched_of_corr_rel`). After the start, every finite positive actual launch ends at a
right threshold, so it has a right hit (`hexit₁`: GW1's classified exits, almost surely). The fill correspondence makes
the relative launch hit on the right too (`lHit_launch_corr`, which does not use the relative `NoLeftHit`). So the
relative walk does not end at a left threshold. The profile invariant `InvR` of the relative run (`SB2UxProf`) then
excludes every left hit (`noLeftHit_of_invR`). Hence:

* `arcM_of_corr_launch`: a relative launch along the correspondence is at a mark;
* `invR_flow`: the invariant survives a flow step;
* **`stCorr_run_strong2`**: the lockstep by strong induction. The relative walk's inputs are:
  - regular drivers (true of `EL` by construction);
  - the invariant at the start;
  - `NoLeftMove`, `NoLeftHit` and finite lifetimes before the start.

  The actual walk's inputs are those of `stCorr_run_strong` and its right hits. The conclusions at every stage up to
  `N` are the correspondence, `StepOK`, and the relative `NoLeftMove` and `NoLeftHit` before it.
* **`noLeftHit_rel_all`**: if moreover the actual walk is done at `N + o`, the relative walk never has a left hit
  (`RunInputs.lh₂`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkExit GW1WalkFinish

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R p : ℝ} {ι : ℝ → ℝ}

/-- **A relative launch along the correspondence is at a mark.** -/
theorem arcM_of_corr_launch {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k₁ k₂ : ℕ}
    (hc : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂))
    (hk₂ : k₂ < (boundaryWalkSpec b₂ J₂ θ true).2.2.length) (hev₂ : k₂ % 2 = 0)
    (hfl : FlowSt p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁))
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k₂ + 1)).2.2.2.1 k₂ ≠ none) :
    stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂) = GW1W.stArcM true := by
  rcases hfl with ⟨hst₁, -⟩ | hd | hd
  · exact hc.2.1.trans hst₁
  · exfalso
    apply hl₂
    rw [GW1WalkFinish.done_run_succ _ D₂ (hc.2.1.trans hd)]
    exact launches_run_of_le _ D₂ le_rfl
  · exfalso
    apply hl₂
    rw [GW1W.run_succ_walk_flow (κ := κ) (b := b₂) (jumps := J₂) (θ := θ) (right := true) (D := D₂) hk₂ hev₂,
      flowStep_of_dead (hc.2.1.trans hd)]
    exact launches_run_of_le _ D₂ le_rfl

/-- **The invariant survives a flow step** (a launch only from a mark, with a regular driver and good records). -/
theorem invR_flow {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hk : k < (boundaryWalkSpec b J θ true).2.2.length) (hev : k % 2 = 0)
    (hI : InvR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k)) (hreg : IsRegularDriver (D k))
    (hgood : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k ≠ none → (D k).2 ≠ ⊤ →
      LocalExt.IsDrvGood (recHist (recOf ⊤ (D k))))
    (harc : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k ≠ none →
      stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = GW1W.stArcM true) :
    InvR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)) := by
  set s := ExplState.run κ b J (boundaryWalkSpec b J θ true) D k with hsdef
  have hstep := GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := J) (θ := θ) (right := true) (D := D) hk hev
  rcases flowStep_trichotomy (κ := κ) (b := b) false s k (D k) θ ⊤ with e | e | e
  · rw [hstep, e]
    exact hI
  · rw [hstep, e]
    exact invR_setDead hI
  · have hl : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k ≠ none := by
      rw [hstep, e]
      exact launched_launch s k (D k) θ ⊤
    rw [hstep, e]
    exact invR_launch hI (harc hl) k θ hreg (hgood hl)

/-- **The lockstep by strong induction, with the relative walk's no-left-move and no-left-hit derived along it.** -/
theorem stCorr_run_strong2 (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R)) (hRp : R ≤ p)
    {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (o i₀ N : ℕ)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hfin₂₀ : ∀ j, j < i₀ →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hlm₂₀ : ∀ j, j < i₀ → NoLeftMove κ b₂ J₂ θ D₂ j) (hlh₂₀ : ∀ j, j < i₀ → NoLeftHit κ b₂ J₂ θ D₂ j)
    (hinv₀ : InvR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i₀))
    (hallow : ∀ k, i₀ + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, i₀ + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ ⊤ →
      (D₁ k).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
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
      (∀ j, j < i → NoLeftMove κ b₂ J₂ θ D₂ j) ∧ (∀ j, j < i → NoLeftHit κ b₂ J₂ θ D₂ j) ∧
      InvR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) := by
  have hk₀ : (i₀ + o) % 2 = 0 := by omega
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _
    refine ⟨fun j hj hji => ?_, fun j hj hji => absurd hji (by omega), hlm₂₀, hlh₂₀, hinv₀⟩
    rw [show j = i₀ by omega]
    exact h₀
  | succ i hi ih =>
    intro hiN
    have hiN' : i < N := hiN
    obtain ⟨hcs, hoks, hlms, hlhs, hinv⟩ := ih hiN'.le
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
    obtain ⟨hok₂, -⟩ := recInv_ptRec_run_le' hP₂ (N := i) hfin₂ (fun j hj => hlms j hj) (fun j hj => hlhs j hj) i
      le_rfl
    obtain ⟨hk₁, hk₂⟩ := hlen i hi hiN'
    have hgood₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
        (D₂ i).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D₂ i))) := fun hl hT =>
      BW1Prop.isDrvGood_of_pieceRegular (hreg₂ i) (pieceRegular_of_launch hP₂ hl) hT
    -- no left hit of the relative walk at `i`
    have hlhi : NoLeftHit κ b₂ J₂ θ D₂ i := by
      intro hl₂
      obtain ⟨hev₂, -⟩ := GW1W.even_of_launches_walk hl₂
      have hev₁ : (i + o) % 2 = 0 := by omega
      have hfl₁ := hfl hev₁
      have hst₂ := arcM_of_corr_launch hc hk₂ hev₂ hfl₁ hl₂
      have hl₁ := launched_of_corr_rel hι hRp hc hk₁ hk₂ hev₁ hev₂ hfl₁ hl₂
      obtain ⟨⟨c₁, θ₁⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
      obtain ⟨⟨c₂, θ₂⟩, hl₂'⟩ := Option.ne_none_iff_exists'.1 hl₂
      obtain ⟨-, he₂, -⟩ := eq_launch_of_launches (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hl₂'
      rw [Lx.instrTime_boundaryWalk_of_launch hl₂'] at he₂
      have hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) =
          ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))) := by
        rw [hc.2.2.2, max_eq_left hp]
      have hhit : (D₂ i).2 ≠ ⊤ → (D₂ i).2 ≠ 0 → ∃ x : ℝ,
          stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) < x ∧
            lHit (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) ⊤ (D₂ i) x := by
        intro hT h0
        obtain ⟨hLT, hL0⟩ := hL1 i hi hiN' hl₁ hl₂
        have hT₁ : (D₁ (i + o)).2 ≠ ⊤ := fun h => hT (hLT.2 h)
        have h0₁ : (D₁ (i + o)).2 ≠ 0 := fun h => h0 (hL0.2 h)
        exact (lHit_launch_corr hι hP₁ hP₂ hl₁' hl₂' hT₁ hT hok₁ hok₂ (hRp.trans hp) hrecc
          (hF i hi hiN' hl₁ hl₂ hT₁)).2 (hexit₁ (i + o) (by omega) hl₁ hT₁ h0₁)
      have hthr₂ : stStatus (ExplState.launch (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) i
          (D₂ i) θ₂ ⊤) ≠ stThr (some false) := lStatus_ne_left i θ₂ hhit
      exact noLeftHit_of_invR hinv hst₂ i θ₂ (hreg₂ i) (hgood₂ hl₂) hthr₂
    have hlhs' : ∀ j, j < i + 1 → NoLeftHit κ b₂ J₂ θ D₂ j := fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hlhs j hj
      · exact hlhi
    -- the step
    have hokS := stepOK_of_local hι hcont hRp hP₁ hP₂ hk₁ hk₂ (by omega) hc hok₁ hpt₁ hok₂ hp
      ⟨fun _ => hfl (by omega), fun _ => hco (by omega)⟩ (hL1 i hi hiN') (hF i hi hiN') (hlh₁ (i + o)) hlhi
    have hpar' : (i + o) % 2 = i % 2 := by omega
    have hnext := stCorr_step (κ := κ) (θ := θ) hι hRp hk₁ hk₂ hpar' hc hokS
    rw [show i + o + 1 = i + 1 + o by omega] at hnext
    -- the relative invariant at `i + 1`
    have hinv' : InvR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)) := by
      rcases Nat.mod_two_eq_zero_or_one i with hev₂ | hodd₂
      · have hev₁ : (i + o) % 2 = 0 := by omega
        exact invR_flow hk₂ hev₂ hinv (hreg₂ i) hgood₂ fun hl₂ => arcM_of_corr_launch hc hk₂ hev₂ (hfl hev₁) hl₂
      · have hstep := GW1W.run_succ_walk_cont (κ := κ) (b := b₂) (jumps := J₂) (θ := θ) (right := true) (D := D₂)
          hk₂ hodd₂
        rw [hstep]
        exact invR_cont (allowedSt_corr hι hRp hc (hallow (i + o) (by omega)) hthr) hinv
    refine ⟨fun j hj hji => ?_, fun j hj hji => ?_, hlms', hlhs', hinv'⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hji) with h | h
      · exact hcs j hj (by omega)
      · rw [h]; exact hnext
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hji with h | rfl
      · exact hoks j hj h
      · exact hokS

/-- **The relative walk never has a left hit** (`RunInputs.lh₂`): before the start by the start data, along the
lockstep by `stCorr_run_strong2`, and after it because both walks are done. -/
theorem noLeftHit_rel_all {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}
    (hlhs : ∀ j, j < N → NoLeftHit κ b₂ J₂ θ D₂ j)
    (hcN : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N))
    (hdone : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone) :
    ∀ j, NoLeftHit κ b₂ J₂ θ D₂ j := by
  intro j
  by_cases hj : j < N
  · exact hlhs j hj
  · intro hl
    exfalso
    have hd₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N) = stDone :=
      hcN.2.1.trans hdone
    have hdj := done_of_le hd₂ (not_lt.1 hj)
    apply hl
    rw [GW1WalkFinish.done_run_succ _ D₂ hdj]
    exact launches_run_of_le _ D₂ le_rfl

end InteractingSLE.Theorem14.SB.Lk
