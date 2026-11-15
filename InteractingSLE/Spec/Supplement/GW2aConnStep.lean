/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aConnThr
import InteractingSLE.Spec.Supplement.GW1ActiveRun

/-!
# GW2a's connectors: the run invariant through every step (deterministic)

Packet PROVE-GW2A-CONN. The invariant `Inv` carried along the run of a boundary-continued program is `GInv` (the
classification of the word on both untouched original rays) together with `ConnFacts`, the readiness facts at the
statuses from which a connector can start:

* at the root and at a zero-lifetime threshold from the root, the current point is both records and both profiles
  tend to `0` there;
* at a right threshold, the current point is the right record, the right profile tends to `0`, the outward original
  height is low, and the word just left of `0` is the left side height `−λ − θχ` of the stopped piece (the mirror at
  a left threshold);
* on a partial right connector (status `onArc (true, false)`) the right readiness holds (the mirror on the left);
* at a zero-lifetime threshold that is not root-type, the original heights at the current point form an admissible
  seed, so the next continuation kills the history.

`inv_launch` proves the invariant after a launch with a good record, given the two threshold facts of the stage (from
`stopWord_facts_right/left`) and the origin of a zero-lifetime threshold; `inv_step_noLaunch` proves it after every
step that does not launch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap fwdMapInv fwdHull H)

namespace InteractingSLE

namespace Theorem14

namespace GW2aConn

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### The readiness facts -/

/-- The current point is the right record and the right profile tends to `0` there. -/
def RReady0 (s : ExplState) : Prop :=
  stPt s = stRecR s ∧ ∀ ε > 0, ∃ x, stRecR s < x ∧ rProf (stChart s) x < ε

/-- The current point is the left record and the reflected left profile tends to `0` there. -/
def LReady0 (s : ExplState) : Prop :=
  stPt s = stRecL s ∧ ∀ ε > 0, ∃ x, -stRecL s < x ∧ lProf (stChart s) x < ε

/-- **The readiness facts at the statuses from which a connector starts.** -/
def ConnFacts (κ : ℝ) (b : ℝ → ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  (stStatus s = .inl () → RReady0 s ∧ LReady0 s) ∧
  (stStatus s = stThr (some true) → RConn κ b s ∧
    ∃ ε > 0, ∀ z ∈ Ioo (-ε) (0 : ℝ), z ∉ β.jumps → β.fn z = -sleLambda κ - stAngle s * chiC κ) ∧
  (stStatus s = stThr (some false) → LConn κ b s ∧
    ∃ ε > 0, ∀ z ∈ Ioo (0 : ℝ) ε, z ∉ β.jumps → β.fn z = sleLambda κ - stAngle s * chiC κ) ∧
  (stStatus s = .inr (.inr (.inr (.inl (true, false)))) → RConn κ b s) ∧
  (stStatus s = .inr (.inr (.inr (.inl (false, false)))) → LConn κ b s) ∧
  (stStatus s = stThr none → (RReady0 s ∧ LReady0 s) ∨
    ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) (stAngle s))

/-- **The run invariant.** -/
def Inv (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  GInv b jumps β s ∧ ConnFacts κ b β s

theorem shiftW_zero (c : BoundaryWord) : BoundaryWord.shiftW 0 c = c := by
  obtain ⟨n, p, v⟩ := c
  simp [BoundaryWord.shiftW]

theorem shiftW_shiftW (a a' : ℝ) (c : BoundaryWord) :
    BoundaryWord.shiftW a' (BoundaryWord.shiftW a c) = BoundaryWord.shiftW (a + a') c := by
  obtain ⟨n, p, v⟩ := c
  simp only [BoundaryWord.shiftW, Prod.mk.injEq, true_and, and_true]
  funext i
  ring

theorem rConn_of_ready {s : ExplState} (h0 : RReady0 s)
    (hlow : rightLim b (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ) : RConn κ b s :=
  ⟨h0.1, h0.2, hlow⟩

theorem lConn_of_ready {s : ExplState} (h0 : LReady0 s)
    (hhigh : sleLambda κ ≤ leftLim b (stPt s) + stAngle s * chiC κ) : LConn κ b s :=
  ⟨h0.1, h0.2, hhigh⟩

/-! ### The outcome of a launch with a finite stop -/

section Outcome

variable {s : ExplState} {k : ℕ} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞}

theorem launch_thr_true_gen (hfin : min t D.2 ≠ ⊤)
    (h : stStatus (ExplState.launch s k D θ t) = stThr (some true)) :
    ¬ t < D.2 ∧ D.2 ≠ 0 ∧ (∃ x, stRecR s < x ∧ lHit (stChart s) t D x) ∧
      stPt (ExplState.launch s k D θ t) = stRecR (ExplState.launch s k D θ t) ∧
      stAngle (ExplState.launch s k D θ t) = θ := by
  obtain ⟨-, hang, hrec, -, hst, hpt⟩ := launch_eq_of_ne_top s k D θ t hfin
  rw [hst] at h
  unfold lStatus at h
  by_cases ht : t < D.2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)] at h
    exact absurd h (by simp [stTip, stThr])
  rw [ite_eq_right_of_eq_false _ _ (eq_false ht)] at h
  by_cases h0 : D.2 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)] at h
    exfalso
    revert h
    split <;> simp [stThr, stDead]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at h
  by_cases hx : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t D x
  · refine ⟨ht, h0, hx, ?_, hang⟩
    rw [hpt, hrec]
    unfold lPt
    rw [ite_eq_right_of_eq_false _ _ (eq_false ht), ite_eq_right_of_eq_false _ _ (eq_false h0),
      ite_eq_left_of_eq_true _ _ (eq_true hx)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)] at h
    exfalso
    split_ifs at h <;> simp [stThr, stDead] at h

theorem launch_thr_false_gen (hfin : min t D.2 ≠ ⊤)
    (h : stStatus (ExplState.launch s k D θ t) = stThr (some false)) :
    ¬ t < D.2 ∧ D.2 ≠ 0 ∧ (∃ x, x < stRecL s ∧ lHit (stChart s) t D x) ∧
      stPt (ExplState.launch s k D θ t) = stRecL (ExplState.launch s k D θ t) ∧
      stAngle (ExplState.launch s k D θ t) = θ := by
  obtain ⟨-, hang, -, hrecL, hst, hpt⟩ := launch_eq_of_ne_top s k D θ t hfin
  rw [hst] at h
  unfold lStatus at h
  by_cases ht : t < D.2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)] at h
    exact absurd h (by simp [stTip, stThr])
  rw [ite_eq_right_of_eq_false _ _ (eq_false ht)] at h
  by_cases h0 : D.2 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)] at h
    exfalso
    revert h
    split <;> simp [stThr, stDead]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at h
  by_cases hx : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t D x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hx)] at h
    exact absurd h (by simp [stThr])
  rw [ite_eq_right_of_eq_false _ _ (eq_false hx)] at h
  by_cases hy : ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t D x
  · refine ⟨ht, h0, hy, ?_, hang⟩
    rw [hpt, hrecL]
    unfold lPt
    rw [ite_eq_right_of_eq_false _ _ (eq_false ht), ite_eq_right_of_eq_false _ _ (eq_false h0),
      ite_eq_right_of_eq_false _ _ (eq_false hx), ite_eq_left_of_eq_true _ _ (eq_true hy)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hy)] at h
    exact absurd h (by simp [stThr, stDead])

theorem launch_thr_none_gen (hfin : min t D.2 ≠ ⊤) (h : stStatus (ExplState.launch s k D θ t) = stThr none) :
    D.2 = 0 ∧ stPt (ExplState.launch s k D θ t) = stPt s ∧ stAngle (ExplState.launch s k D θ t) = θ := by
  obtain ⟨-, hang, -, -, hst, hpt⟩ := launch_eq_of_ne_top s k D θ t hfin
  rw [hst] at h
  unfold lStatus at h
  by_cases ht : t < D.2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)] at h
    exact absurd h (by simp [stTip, stThr])
  rw [ite_eq_right_of_eq_false _ _ (eq_false ht)] at h
  by_cases h0 : D.2 = 0
  · refine ⟨h0, ?_, hang⟩
    rw [hpt]
    unfold lPt
    rw [ite_eq_right_of_eq_false _ _ (eq_false ht), ite_eq_left_of_eq_true _ _ (eq_true h0)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at h
    exfalso
    split_ifs at h <;> simp [stThr, stDead] at h

theorem launch_status_cases (hfin : min t D.2 ≠ ⊤) :
    stStatus (ExplState.launch s k D θ t) = stTip ∨ stStatus (ExplState.launch s k D θ t) = stDead ∨
      stStatus (ExplState.launch s k D θ t) = stThr none ∨
      stStatus (ExplState.launch s k D θ t) = stThr (some true) ∨
      stStatus (ExplState.launch s k D θ t) = stThr (some false) := by
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top s k D θ t hfin
  rw [hst]
  unfold lStatus
  split_ifs
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · exact Or.inr (Or.inl rfl)

end Outcome

/-! ### A launch with zero lifetime -/

/-- **A zero-lifetime launch keeps the real profile and both records.** -/
theorem launch_zero_eq {β : BoundaryWord} {s : ExplState} (hI : GInv b jumps β s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞) (hreg : IsRegularDriver D) (h0 : D.2 = 0) :
    rProf (stChart (ExplState.launch s k D θ t)) = rProf (stChart s) ∧
      stRecR (ExplState.launch s k D θ t) = stRecR s ∧ stRecL (ExplState.launch s k D θ t) = stRecL s := by
  obtain ⟨hc, ⟨-, hpos⟩, ⟨-, hlpos⟩, -, -, -⟩ := hI
  have hfin : min t D.2 ≠ ⊤ := by rw [h0, min_eq_right zero_le]; exact ENNReal.zero_ne_top
  obtain ⟨hch, -, hrec, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ t hfin
  have hT : stopTime t D = 0 := by simp [stopTime, h0]
  have hW0 : stopDrv t D 0 = 0 := stopDrv_zero hreg t
  have hal : ∀ x : ℝ, rProf (stChart s) x ≠ 0 → lAlive (stChart s) t D x := fun x hx => by
    unfold lAlive
    rw [hT, hc.eq_ofReal x]
    exact exists_isForwardSol_zero hW0 hx
  refine ⟨funext fun x => ?_, ?_, ?_⟩
  · rw [hch, hT]
    change (fwdMap (stopDrv t D) 0 ((stChart s).1 x)).re = _
    rw [fwdMap_zero_time hW0]
    rfl
  · rw [hrec]
    unfold lRecR
    have he : {x : ℝ | stRecR s < x ∧ ¬ lAlive (stChart s) t D x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun hx => hal x (hpos x hx).ne'
    rw [he, insert_empty_eq, csSup_singleton]
  · rw [hrecL]
    unfold lRecL
    have he : {x : ℝ | x < stRecL s ∧ ¬ lAlive (stChart s) t D x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun hx => hal x (rProf_neg_of_lProf hlpos hx).ne
    rw [he, insert_empty_eq, csInf_singleton]

/-! ### The invariant after a launch -/

/-- **The run invariant after a launch with a good record at a finite stop**, given the two threshold facts of the
stage and the origin of a zero-lifetime threshold. -/
theorem inv_launch (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {s : ExplState}
    (hI : Inv κ b jumps β s) (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf t D))) (hfin : min t D.2 ≠ ⊤)
    (hR : stStatus (ExplState.launch s k D θ t) = stThr (some true) →
      rightLim b (stRecR (ExplState.launch s k D θ t)) + θ * chiC κ ≤ -sleLambda κ ∧
        markPosL (rdrv (recOf t D)) (rtime (recOf t D)) 0 < 0)
    (hL : stStatus (ExplState.launch s k D θ t) = stThr (some false) →
      sleLambda κ ≤ leftLim b (stRecL (ExplState.launch s k D θ t)) + θ * chiC κ ∧
        0 < markPos (rdrv (recOf t D)) (rtime (recOf t D)) 0)
    (hN : stStatus (ExplState.launch s k D θ t) = stThr none →
      stStatus s = .inl () ∨ ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ) :
    Inv κ b jumps (stopWord κ (β, θ, recOf t D)) (ExplState.launch s k D θ t) := by
  have hG := gInv_launch hκ hb hI.1 k θ t hreg hgood hfin
  set s₁ := ExplState.launch s k D θ t with hs₁
  have hcases := launch_status_cases (s := s) (k := k) (θ := θ) hfin
  refine ⟨hG, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exfalso
    rcases hcases with e | e | e | e | e <;> rw [e] at h <;> simp [stTip, stDead, stThr] at h
  · obtain ⟨-, -, hhit, hpt, hang⟩ := launch_thr_true_gen hfin h
    have hsmall := rSmall_launch hI.1 k θ t hreg hgood hfin hhit
    obtain ⟨hlow', hopen⟩ := hR h
    refine ⟨⟨hpt, hsmall, ?_⟩, ?_⟩
    · rw [hpt, hang]; exact hlow'
    · rw [hang]
      refine ⟨-markPosL (rdrv (recOf t D)) (rtime (recOf t D)) 0, by linarith,
        stopWord_eq_left_of_open β θ (recOf t D) (w₀ := 0) (fun i => (sub_zero _).symm) fun i => ?_⟩
      rw [sub_zero, neg_neg]
      exact markPosL_mono (continuous_rdrv _) (rdrv_zero _) (rtime_nonneg _) le_rfl
        ((Theorem15.isOrderedForceWord_flowLine β.fn β.jumps 0).2.1 i)
  · obtain ⟨-, -, hhit, hpt, hang⟩ := launch_thr_false_gen hfin h
    have hsmall := lSmall_launch hI.1 k θ t hreg hgood hfin hhit
    obtain ⟨hhigh', hopen⟩ := hL h
    refine ⟨⟨hpt, hsmall, ?_⟩, ?_⟩
    · rw [hpt, hang]; exact hhigh'
    · rw [hang]
      refine ⟨markPos (rdrv (recOf t D)) (rtime (recOf t D)) 0, hopen,
        stopWord_eq_right_of_open β θ (recOf t D) (w₀ := 0) (fun j => (sub_zero _).symm) fun j => ?_⟩
      rw [sub_zero]
      exact markPos_mono (continuous_rdrv _) (rdrv_zero _) (rtime_nonneg _) le_rfl
        ((Theorem15.isOrderedForceWord_flowLine β.fn β.jumps 0).2.2.2 j)
  · exfalso
    rcases hcases with e | e | e | e | e <;> rw [e] at h <;> simp [stTip, stDead, stThr] at h
  · exfalso
    rcases hcases with e | e | e | e | e <;> rw [e] at h <;> simp [stTip, stDead, stThr] at h
  · obtain ⟨h0, hpt, hang⟩ := launch_thr_none_gen hfin h
    obtain ⟨hprof, hrR, hrL⟩ := launch_zero_eq hI.1 k θ t hreg h0
    rcases hN h with hroot | hadm
    · obtain ⟨⟨hpR, hsR⟩, ⟨hpL, hsL⟩⟩ := hI.2.1 hroot
      have hlprof : lProf (stChart s₁) = lProf (stChart s) := funext fun u => by
        rw [lProf_eq, lProf_eq, hprof]
      refine Or.inl ⟨⟨by rw [hpt, hrR, hpR], ?_⟩, ⟨by rw [hpt, hrL, hpL], ?_⟩⟩
      · rw [hrR, hprof]; exact hsR
      · rw [hrL, hlprof]; exact hsL
    · right
      rw [hpt, hang]
      exact hadm

/-! ### The invariant after a step without launch -/

/-- **A flow step that launches from a status other than the root and an interior tip passed the seed test.** -/
theorem admissible_of_flowStep_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hs0 : s.2.2.2.1 k = none) (hl : (ExplState.flowStep κ b false s k D θ t).2.2.2.1 k ≠ none)
    (hst : stStatus s ≠ .inl ()) (hst' : stStatus s ≠ .inr (.inl ())) :
    ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact absurd rfl hst
  · exact absurd rfl hst'
  all_goals
    by_contra hadm
    apply hl
    simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte, hadm]
    exact hs0

theorem arcs_moveAlong (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s r x m).2.1 ≠ s.2.1 := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  intro h
  have := congrArg List.length h
  simp [ExplState.moveAlong] at this

theorem isTerminal_moveToEnd' (s : ExplState) (r : Bool) : IsTerminal (ExplState.moveToEnd s r) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  exact Or.inl rfl

theorem shift_moveAlong (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    ((stChart s).1 0 - (stChart (ExplState.moveAlong s r x m)).1 0).re = rProf (stChart s) x := by
  rw [stChart_moveAlong]
  simp [InteractingSLE.Chart.recenter, rProf]

/-- **The invariant after a connector move** (right or left). -/
theorem inv_contStep_move (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {s : ExplState}
    (hI : Inv κ b jumps β s) (vStop : Option ℝ) (pref : Bool)
    (hne : (ExplState.contStep κ b jumps s vStop pref).2.1 ≠ s.2.1)
    (hlive : ¬ IsTerminal (ExplState.contStep κ b jumps s vStop pref)) :
    Inv κ b jumps (BoundaryWord.shiftW ((stChart s).1 0 -
      (stChart (ExplState.contStep κ b jumps s vStop pref)).1 0).re β)
      (ExplState.contStep κ b jumps s vStop pref) := by
  obtain ⟨hG, hC⟩ := hI
  rcases contStep_arc_cases s vStop pref hne with ⟨hst, he⟩ | ⟨hst, he⟩
  · -- rightward
    have hRC : RConn κ b s := by
      rcases hst with h | ⟨h, hlow⟩ | h
      · exact (hC.2.1 h).1
      · rcases hC.2.2.2.2.2 h with ⟨h0, -⟩ | hadm
        · exact rConn_of_ready h0 hlow
        · exact absurd hlow (not_le.2 hadm.2)
      · exact hC.2.2.2.1 h
    rw [he] at hlive ⊢
    rcases rMove_rBranch (κ := κ) (b := b) (jumps := jumps) s vStop with ⟨x, mk, hx, hpx, hj, hjf⟩ | ⟨hx, -⟩
    · rw [hx] at hlive ⊢
      rw [shift_moveAlong]
      have hxR : stRecR s < x := by rw [← hRC.1]; exact hpx
      refine ⟨gInv_moveAlong hG true (Or.inl hxR) (fun _ => hxR) (fun h => absurd h (by simp)) mk, ?_⟩
      have hstm := stStatus_moveAlong s true x mk
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rw [hstm] at h; exact absurd h (by simp)
      · rw [hstm] at h; exact absurd h (by simp [stThr])
      · rw [hstm] at h; exact absurd h (by simp [stThr])
      · rw [hstm] at h
        have hmk : mk = false := by simpa using h
        exact rConn_moveAlong hG hRC hpx (rightLim_low_of_lt hb hRC.2.2 (hjf hmk) hpx) mk
      · rw [hstm] at h; exact absurd h (by simp)
      · rw [hstm] at h; exact absurd h (by simp [stThr])
    · rw [hx] at hlive
      exact absurd (isTerminal_moveToEnd' s true) hlive
  · -- leftward
    have hLC : LConn κ b s := by
      rcases hst with h | ⟨h, hhigh⟩ | h
      · exact (hC.2.2.1 h).1
      · rcases hC.2.2.2.2.2 h with ⟨-, h0⟩ | hadm
        · exact lConn_of_ready h0 hhigh
        · exact absurd hhigh (not_le.2 hadm.1)
      · exact hC.2.2.2.2.1 h
    rw [he] at hlive ⊢
    rcases lMove_lBranch (κ := κ) (b := b) (jumps := jumps) s vStop with ⟨x, mk, hx, hxp, hj, hjf⟩ | ⟨hx, -⟩
    · rw [hx] at hlive ⊢
      rw [shift_moveAlong]
      have hxL : x < stRecL s := by rw [← hLC.1]; exact hxp
      refine ⟨gInv_moveAlong hG false (Or.inr hxL) (fun h => absurd h (by simp)) (fun _ => hxL) mk, ?_⟩
      have hstm := stStatus_moveAlong s false x mk
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rw [hstm] at h; exact absurd h (by simp)
      · rw [hstm] at h; exact absurd h (by simp [stThr])
      · rw [hstm] at h; exact absurd h (by simp [stThr])
      · rw [hstm] at h; exact absurd h (by simp)
      · rw [hstm] at h
        have hmk : mk = false := by simpa using h
        exact lConn_moveAlong hG hLC hxp (leftLim_high_of_gt hb hLC.2.2 (hjf hmk) hxp) mk
      · rw [hstm] at h; exact absurd h (by simp [stThr])
    · rw [hx] at hlive
      exact absurd (isTerminal_moveToEnd' s false) hlive

/-- **The invariant after a step that does not launch** (the chart shift is `0` unless the step moves along a
connector). -/
theorem inv_step_of_noLaunch (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {s : ExplState}
    (hI : Inv κ b jumps β s) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (ins : Instr) (j : ℕ)
    (hnl : (ExplState.step κ b jumps false D s (ins, j)).2.2.2.1 j = none)
    (hlive : ¬ IsTerminal (ExplState.step κ b jumps false D s (ins, j))) :
    Inv κ b jumps (BoundaryWord.shiftW ((stChart s).1 0 -
      (stChart (ExplState.step κ b jumps false D s (ins, j))).1 0).re β)
      (ExplState.step κ b jumps false D s (ins, j)) := by
  have hzero : ∀ s' : ExplState, s' = s → Inv κ b jumps (BoundaryWord.shiftW ((stChart s).1 0 -
      (stChart s').1 0).re β) s' := by
    rintro s' rfl
    rw [sub_self, Complex.zero_re, shiftW_zero]
    exact hI
  unfold ExplState.step at hnl hlive ⊢
  rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
  · exact hzero _ (flowStep_eq_self_of_noLaunch s j (D j) θ t hnl)
  all_goals
    simp only at hnl hlive ⊢
    first
    | (by_cases hne : (ExplState.contStep κ b jumps s none pref).2.1 = s.2.1
       · rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s none pref with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
         · exact hzero _ e
         · rw [e] at hlive; exact absurd (isTerminal_setDead s) hlive
         · rw [e] at hne; exact absurd hne (arcs_moveAlong s r x m)
         · rw [e] at hlive; exact absurd (isTerminal_moveToEnd' s r) hlive
       · exact inv_contStep_move hb hI none pref hne hlive)
    | (by_cases hne : (ExplState.contStep κ b jumps s (some v) pref).2.1 = s.2.1
       · rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s (some v) pref with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
         · exact hzero _ e
         · rw [e] at hlive; exact absurd (isTerminal_setDead s) hlive
         · rw [e] at hne; exact absurd hne (arcs_moveAlong s r x m)
         · rw [e] at hlive; exact absurd (isTerminal_moveToEnd' s r) hlive
       · exact inv_contStep_move hb hI (some v) pref hne hlive)

/-! ### The invariant between two launches -/

/-- **The run invariant between two launches** (Lemma GW1/GW2a, "a connector has no field reveal"): from the state
right after a launch, through the steps that do not launch, the invariant holds for the word recentred by the chart
shift. -/
theorem inv_run_between (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec) (hgw : spec.2.1 = false)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {ℓ : ℕ} {γ : BoundaryWord}
    (h1 : Inv κ b jumps γ (ExplState.run κ b jumps spec D (ℓ + 1))) :
    ∀ n, (∀ j, ℓ < j → j < ℓ + 1 + n → (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none) →
      ¬ IsTerminal (ExplState.run κ b jumps spec D (ℓ + 1 + n)) →
      Inv κ b jumps (BoundaryWord.shiftW (((ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.2.1.1 0 -
        (ExplState.run κ b jumps spec D (ℓ + 1 + n)).2.2.2.2.1.1 0).re) γ)
        (ExplState.run κ b jumps spec D (ℓ + 1 + n))
  | 0, _, _ => by
    rw [add_zero, sub_self, Complex.zero_re, shiftW_zero]
    exact h1
  | n + 1, hn, hnT => by
    set j := ℓ + 1 + n with hj
    have hj1 : ℓ + 1 + (n + 1) = j + 1 := by rw [hj]; ring
    rw [hj1] at hnT ⊢
    have hnTj : ¬ IsTerminal (ExplState.run κ b jumps spec D j) := fun hT =>
      hnT (isTerminal_run_of_le spec D hT (j + 1) (Nat.le_succ j)).1
    have ih := inv_run_between hb spec hgw D h1 n (fun i hi hin => hn i hi (by omega)) hnTj
    have hnl := hn j (by omega) (by omega)
    rw [run_succ spec D j] at hnl hnT ⊢
    cases hk : spec.2.2[j]? with
    | none =>
      simp only [hk] at hnl hnT ⊢
      exact ih
    | some ins =>
      simp only [hk] at hnl hnT ⊢
      rw [hgw] at hnl hnT ⊢
      have hstep := inv_step_of_noLaunch hb ih D ins j hnl hnT
      rw [shiftW_shiftW] at hstep
      convert hstep using 2
      simp only [Complex.sub_re]
      ring

/-! ### The seed of a launch at a threshold -/

/-- A function equal to `c` just left of `0` off a finite set has left limit `c` at `0`. -/
theorem leftLim_eq_of_eq {f : ℝ → ℝ} {J : Finset ℝ} {c ε : ℝ} (hε : 0 < ε)
    (h : ∀ z ∈ Ioo (-ε) (0 : ℝ), z ∉ J → f z = c) : leftLim f 0 = c := by
  have hev : ∀ᶠ z in 𝓝[<] (0 : ℝ), f z = c := by
    have h1 : ∀ᶠ z in 𝓝[<] (0 : ℝ), z ∈ Ioo (-ε) (0 : ℝ) :=
      Ioo_mem_nhdsLT (by linarith)
    have h2 : ∀ᶠ z in 𝓝[<] (0 : ℝ), z ∉ J :=
      (eventually_notMem_of_finite J.finite_toSet (0 : ℝ)).filter_mono
        (nhdsWithin_mono (0 : ℝ) fun z (hz : z < 0) => (ne_of_lt hz : z ≠ 0))
    filter_upwards [h1, h2] with z hz hzJ using h z hz hzJ
  have : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 c) := tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
  exact this.limUnder_eq

/-- A function equal to `c` just right of `0` off a finite set has right limit `c` at `0`. -/
theorem rightLim_eq_of_eq {f : ℝ → ℝ} {J : Finset ℝ} {c ε : ℝ} (hε : 0 < ε)
    (h : ∀ z ∈ Ioo (0 : ℝ) ε, z ∉ J → f z = c) : rightLim f 0 = c := by
  have hev : ∀ᶠ z in 𝓝[>] (0 : ℝ), f z = c := by
    have h1 : ∀ᶠ z in 𝓝[>] (0 : ℝ), z ∈ Ioo (0 : ℝ) ε := Ioo_mem_nhdsGT hε
    have h2 : ∀ᶠ z in 𝓝[>] (0 : ℝ), z ∉ J :=
      (eventually_notMem_of_finite J.finite_toSet (0 : ℝ)).filter_mono
        (nhdsWithin_mono (0 : ℝ) fun z (hz : 0 < z) => (ne_of_gt hz : z ≠ 0))
    filter_upwards [h1, h2] with z hz hzJ using h z hz hzJ
  have : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c) := tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
  exact this.limUnder_eq

/-- **The word just right of `0` is the original height right of the current point** at a state whose current point
is the right record and whose right profile tends to `0` there. -/
theorem rightLim_word_eq (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {s : ExplState}
    (hI : GInv b jumps β s) (h0 : RReady0 s) : rightLim β.fn 0 = rightLim b (stPt s) := by
  obtain ⟨-, ⟨hm, hpos⟩, -, hO, -, -⟩ := hI
  obtain ⟨hpt, hsmall⟩ := h0
  obtain ⟨hi, hhi, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim hb (stPt s)
  set x₁ := (stPt s + hi) / 2 with hx₁
  have hx₁R : stRecR s < x₁ := by rw [← hpt, hx₁]; linarith
  have hx₁hi : x₁ < hi := by rw [hx₁]; linarith
  refine rightLim_eq_of_eq (J := β.jumps) (hpos x₁ hx₁R) fun z hz hzJ => ?_
  obtain ⟨y, hy, hmy⟩ := (exists_eq_iff_exists_lt hm).2 (hsmall z hz.1)
  have hyx : y < x₁ := by
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · have := hm.1 hx₁R hy h
      linarith [hz.2]
    · rw [← h] at hmy
      linarith [hz.2]
  have hcy : ContinuousAt (rProf (stChart s)) y := hm.2.1.continuousAt (Ioi_mem_nhds hy)
  have hP : ∀ᶠ y' in 𝓝 y, y' < x₁ ∧ β.fn (rProf (stChart s) y') = β.fn z := by
    have h1 := hcy.eventually (by rw [hmy]; exact β.isPiecewiseConstantBoundaryData z hzJ)
    filter_upwards [gt_mem_nhds hyx, h1] with y' h2 h3
    exact ⟨h2, h3⟩
  obtain ⟨y', hy'R, hy'J, hmy'J, hy'x, hfn⟩ := exists_near_avoid hm.1 hy jumps β.jumps hP
  rw [← hfn, hO y' hy'R hy'J hmy'J]
  exact hconst y' ⟨by rw [hpt]; exact hy'R, hy'x.trans hx₁hi⟩

/-- The mirror of `rightLim_word_eq`. -/
theorem leftLim_word_eq (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {s : ExplState}
    (hI : GInv b jumps β s) (h0 : LReady0 s) : leftLim β.fn 0 = leftLim b (stPt s) := by
  obtain ⟨-, -, ⟨hl, hlpos⟩, -, hO, -⟩ := hI
  obtain ⟨hpt, hsmall⟩ := h0
  obtain ⟨lo, hlo, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_leftLim hb (stPt s)
  set x₁ := (stPt s + lo) / 2 with hx₁
  have hx₁L : x₁ < stRecL s := by rw [← hpt, hx₁]; linarith
  have hx₁lo : lo < x₁ := by rw [hx₁]; linarith
  have hmono := strictMonoOn_of_lProf hl.1
  refine leftLim_eq_of_eq (J := β.jumps) (neg_pos.2 (rProf_neg_of_lProf hlpos hx₁L)) fun z hz hzJ => ?_
  obtain ⟨u, hu, hmu⟩ := (exists_eq_iff_exists_lt hl).2 (hsmall (-z) (by linarith [hz.2]))
  set y := -u with hydef
  have hyL : y < stRecL s := by rw [hydef]; linarith
  have hmy : rProf (stChart s) y = z := by
    rw [hydef]
    rw [lProf_eq] at hmu
    linarith
  have hxy : x₁ < y := by
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · have := hmono hyL hx₁L h
      linarith [hz.1]
    · rw [h] at hmy
      linarith [hz.1]
  have hcy : ContinuousAt (rProf (stChart s)) y :=
    (continuousOn_rProf_of_lProf hl.2.1).continuousAt (Iio_mem_nhds hyL)
  have hP : ∀ᶠ y' in 𝓝 y, x₁ < y' ∧ β.fn (rProf (stChart s) y') = β.fn z := by
    have h1 := hcy.eventually (by rw [hmy]; exact β.isPiecewiseConstantBoundaryData z hzJ)
    filter_upwards [lt_mem_nhds hxy, h1] with y' h2 h3
    exact ⟨h2, h3⟩
  obtain ⟨y', hy'L, hy'J, hmy'J, hxy', hfn⟩ := exists_near_avoid_left hmono hyL jumps β.jumps hP
  rw [← hfn, hO y' hy'L hy'J hmy'J]
  exact hconst y' ⟨hx₁lo.trans hxy', by rw [hpt]; exact hy'L⟩

/-- **The seed of a launch at a right threshold is admissible for the word** whenever it is admissible for the heights
of the state (the conditional word just left of `0` is the stopped piece's left side height and just right of `0`
the original height). -/
theorem admissible_word_of_thr_true (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord}
    {s : ExplState} (hI : Inv κ b jumps β s) (hst : stStatus s = stThr (some true)) {θ : ℝ}
    (hadm : ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ) :
    ExplState.IsAdmissibleSeed κ (leftLim β.fn 0) (rightLim β.fn 0) θ := by
  obtain ⟨⟨hpt, hsmall, -⟩, ε, hε, hleft⟩ := hI.2.2.1 hst
  have hL := leftLim_eq_of_eq hε hleft
  have hR := rightLim_word_eq hb hI.1 ⟨hpt, hsmall⟩
  have hh : ExplState.heights κ b s = (-sleLambda κ - stAngle s * chiC κ, rightLim b (stPt s)) := by
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
    change st = _ at hst
    subst hst
    rfl
  rw [hh] at hadm
  rw [hL, hR]
  exact hadm

/-- The mirror of `admissible_word_of_thr_true`. -/
theorem admissible_word_of_thr_false (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord}
    {s : ExplState} (hI : Inv κ b jumps β s) (hst : stStatus s = stThr (some false)) {θ : ℝ}
    (hadm : ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ) :
    ExplState.IsAdmissibleSeed κ (leftLim β.fn 0) (rightLim β.fn 0) θ := by
  obtain ⟨⟨hpt, hsmall, -⟩, ε, hε, hright⟩ := hI.2.2.2.1 hst
  have hR := rightLim_eq_of_eq hε hright
  have hL := leftLim_word_eq hb hI.1 ⟨hpt, hsmall⟩
  have hh : ExplState.heights κ b s = (leftLim b (stPt s), sleLambda κ - stAngle s * chiC κ) := by
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
    change st = _ at hst
    subst hst
    rfl
  rw [hh] at hadm
  rw [hL, hR]
  exact hadm

/-- **The run invariant at the root.** -/
theorem inv_init {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    Inv κ b jumps (BoundaryWord.shiftW 0 c₀) (ExplState.init 0) := by
  have hG := gInv_init (b := b) hc₀J hc₀
  have hprof : rProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [rProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hlprof : lProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [lProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hR0 : RReady0 (ExplState.init 0) := ⟨rfl, fun ε hε => ⟨ε / 2, by
    change (0 : ℝ) < ε / 2; linarith, by rw [hprof]; linarith⟩⟩
  have hL0 : LReady0 (ExplState.init 0) := ⟨rfl, fun ε hε => ⟨ε / 2, by
    change -(0 : ℝ) < ε / 2; linarith, by rw [hlprof]; linarith⟩⟩
  refine ⟨hG, fun _ => ⟨hR0, hL0⟩, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    exact absurd h (by simp [ExplState.init, stThr])

end GW2aConn

end Theorem14

end InteractingSLE
