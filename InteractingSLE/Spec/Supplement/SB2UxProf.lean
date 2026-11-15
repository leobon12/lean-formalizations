/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2TwLock

/-!
# The profile invariant of a right walk without stage data

Packet PROVE-T14-SB2LIFT (round 21; the relative walk's `NoLeftHit`, handoff §R20.2 1). Round 15 proved the strong
`NoLeftHit` for the actual walk from the left profile `LProf3`, the right profile `RProf` at the launches (from GW1's
stage data) and `ZhanGT4.not_realSwallowAt_both`. For the relative walk there is no stage data. But the right profile
at a mark is itself invariant along the run: a launch with a right hit keeps it (`rProf_launch`, inside
`profiles_launch`), and a move to a mark beyond the record keeps it (**`rProf_moveAlong_true'`**). So the invariant

`InvR s := LProf3 s ∧ ThrOK s ∧ (at a mark: RProf s ∧ stPt s = stRecR s)`

passes along every launch from a mark (`invR_launch`), every killed state (`invR_setDead`) and every connector step
from an allowed state (`invR_cont`). At a launch from a mark it gives:

* **`noLeftHit_of_invR`**: no point left of the left record is hit, as soon as the walk does not end at a left
  threshold (`not_leftHit_of_lProf3`);
* `lStatus_ne_left`: the walk does not end at a left threshold when there is a right hit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkExit GW1WalkFinish

variable {κ θ : ℝ}

/-- **The profile invariant of a run state**: the left profile, the right profile with the point at the record at a
threshold, and the same at a mark. -/
def InvR (s : ExplState) : Prop :=
  LProf3 s ∧ ThrOK s ∧ (stStatus s = GW1W.stArcM true → RProf s ∧ stPt s = stRecR s)

/-- **The right profile survives a move right to a point beyond the record.** -/
theorem rProf_moveAlong_true' {s : ExplState} (hr : RProf s) {w : ℝ} (hw : stRecR s < w) (m : Bool) :
    RProf (ExplState.moveAlong s true w m) := by
  obtain ⟨hc, ⟨hmono, hcont, hunb⟩, -, -⟩ := hr
  set a := rProf (stChart s) w with hadef
  have hch : stChart (ExplState.moveAlong s true w m) = (stChart s).recenter a := GW1W.stChart_moveAlong s true w m
  have hrec : stRecR (ExplState.moveAlong s true w m) = w := by
    rw [GW1W.stRecR_moveAlong_true, max_eq_right hw.le]
  have hprof : ∀ x, rProf (stChart (ExplState.moveAlong s true w m)) x = rProf (stChart s) x - a := fun x => by
    rw [hch, rProf_recenter]
  have hwI : w ∈ Ioi (stRecR s) := hw
  unfold RProf
  rw [hrec]
  refine ⟨fun x => ?_, ⟨fun x hx y hy hxy => ?_, ?_, fun M => ?_⟩, fun x hx => ?_, fun ε hε => ?_⟩
  · rw [hch]
    show ((stChart s).1 x - (a : ℂ)).im = 0
    simp [hc x]
  · rw [hprof, hprof]
    have := hmono (lt_trans hw hx) (lt_trans hw hy) hxy
    linarith
  · have h : ContinuousOn (fun x => rProf (stChart s) x - a) (Ioi w) :=
      (hcont.mono (Ioi_subset_Ioi hw.le)).sub continuousOn_const
    exact h.congr fun x _ => hprof x
  · obtain ⟨x, hx, hMx⟩ := hunb (max (M + a) a)
    have hxw : w < x := by
      by_contra h
      have hle := hmono.monotoneOn hx hwI (not_lt.1 h)
      linarith [le_max_right (M + a) a]
    exact ⟨x, hxw, by rw [hprof]; linarith [le_max_left (M + a) a]⟩
  · rw [hprof]
    have := hmono hwI (lt_trans hw hx) hx
    linarith
  · have hca : ContinuousAt (rProf (stChart s)) w := hcont.continuousAt (isOpen_Ioi.mem_nhds hwI)
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hca ε hε
    refine ⟨w + δ / 2, by linarith, ?_⟩
    rw [hprof]
    have h1 := hδc (x := w + δ / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.2]

/-- After a launch the walk is not at a mark. -/
theorem stStatus_launch_ne_arcM (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ' : ℝ) :
    stStatus (ExplState.launch s k D θ' ⊤) ≠ GW1W.stArcM true := by
  by_cases hT : D.2 = ⊤
  · rw [(launch_eq_of_top s k D θ' ⊤ (by rw [hT, min_self])).2.2.2.2.1]
    intro h
    cases h
  · rw [(launch_eq_of_ne_top s k D θ' ⊤ (min_top_ne_top hT)).2.2.2.2.1]
    have hnlt : ¬ (⊤ : ℝ≥0∞) < D.2 := not_lt.2 le_top
    unfold lStatus
    simp only [hnlt, ↓reduceIte]
    split_ifs
    · split <;> (intro h; cases h)
    all_goals (intro h; cases h)

/-- **The invariant survives a launch from a mark** with a regular driver and a good record. -/
theorem invR_launch {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hI : InvR s) (hst : stStatus s = GW1W.stArcM true)
    (k : ℕ) (θ' : ℝ) (hreg : IsRegularDriver D) (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D))) :
    InvR (ExplState.launch s k D θ' ⊤) := by
  obtain ⟨hl, -, ha⟩ := hI
  obtain ⟨hr, hpt⟩ := ha hst
  obtain ⟨hl', ht'⟩ := profiles_launch hl hr ⟨Or.inr hst, hpt⟩ k θ' hreg hgood
  exact ⟨hl', ht', fun h => absurd h (stStatus_launch_ne_arcM s k D θ')⟩

/-- **The invariant survives killing the state.** -/
theorem invR_setDead {s : ExplState} (hI : InvR s) : InvR (setDead s) := by
  obtain ⟨hl, -, -⟩ := hI
  refine ⟨lProf3_of_eq (stChart_setDead s) (stRecL_setDead s) hl, fun h => ?_, fun h => ?_⟩
  · rw [stStatus_setDead] at h
    rcases h with h | h <;> exact absurd h (by intro h'; cases h')
  · rw [stStatus_setDead] at h
    exact absurd h (by intro h'; cases h')

/-- **The invariant survives a connector step from an allowed state.** -/
theorem invR_cont {b : ℝ → ℝ} {J : Finset ℝ} {s : ExplState} (hs : AllowedSt κ b s) (hI : InvR s) :
    InvR (ExplState.contStep κ b J s none true) := by
  obtain ⟨hl, ht, ha⟩ := hI
  obtain ⟨hl', ht'⟩ := profiles_cont (jumps := J) hs hl ht
  refine ⟨hl', ht', fun h => ?_⟩
  rcases hs with h0 | hd | hd | hout
  · rw [contStep_of_arcM h0] at h ⊢
    exact ha h
  · rw [contStep_of_done' hd, hd] at h
    exact absurd h (by intro h'; cases h')
  · obtain ⟨-, -, h3⟩ := contStep_dead_chart (κ := κ) (b := b) hd J true
    rw [h3] at h
    exact absurd h (by intro h'; cases h')
  · have hthr : stStatus s = stThr (some true) ∨
        (stStatus s = stThr none ∧ PiecewiseConstantBoundaryData.rightLim b (stPt s) +
          stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ) := by
      rcases hout with h | ⟨h, hlow⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by simpa using hlow⟩
    obtain ⟨hr, hpr⟩ := ht (hthr.imp id fun h => h.1)
    have hform : ExplState.contStep κ b J s none true = if hC : (restartSet κ b J s).Nonempty then
        ExplState.moveAlong s true ((restartSet κ b J s).min' hC) true else ExplState.moveToEnd s true := by
      rcases hthr with h | ⟨h, hlow⟩
      · exact contStep_thr_true' b J s h
      · exact contStep_thr_none_right b J s h hlow
    rw [hform] at h ⊢
    by_cases hC : (restartSet κ b J s).Nonempty
    · simp only [hC, ↓reduceDIte] at h ⊢
      have hmem := Finset.min'_mem _ hC
      simp only [restartSet, Finset.mem_filter] at hmem
      have hw : stRecR s < (restartSet κ b J s).min' hC := hpr ▸ hmem.2.1
      refine ⟨rProf_moveAlong_true' hr hw true, ?_⟩
      rw [GW1W.stPt_moveAlong, GW1W.stRecR_moveAlong_true, max_eq_right hw.le]
    · simp only [hC, ↓reduceDIte] at h
      rw [stStatus_moveToEnd''] at h
      exact absurd h (by intro h'; cases h')

/-- **A right hit at a finite launch ends the walk at a right threshold**, so not at a left one. -/
theorem lStatus_ne_left {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (k : ℕ) (θ' : ℝ)
    (hhit : D.2 ≠ ⊤ → D.2 ≠ 0 → ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ D x) :
    stStatus (ExplState.launch s k D θ' ⊤) ≠ stThr (some false) := by
  by_cases hT : D.2 = ⊤
  · rw [(launch_eq_of_top s k D θ' ⊤ (by rw [hT, min_self])).2.2.2.2.1]
    intro h
    cases h
  · rw [(launch_eq_of_ne_top s k D θ' ⊤ (min_top_ne_top hT)).2.2.2.2.1]
    have hnlt : ¬ (⊤ : ℝ≥0∞) < D.2 := not_lt.2 le_top
    unfold lStatus
    simp only [hnlt, ↓reduceIte]
    split_ifs with h0 hR hL
    · split <;> (intro h; cases h)
    · intro h
      cases h
    · exact absurd (hhit hT h0) hR
    · intro h
      cases h

/-- **No left hit at a launch from a mark** under the invariant, when the walk does not end at a left threshold. -/
theorem noLeftHit_of_invR {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hI : InvR s)
    (hst : stStatus s = GW1W.stArcM true) (k : ℕ) (θ' : ℝ) (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hthr : stStatus (ExplState.launch s k D θ' ⊤) ≠ stThr (some false)) :
    ¬ ∃ y : ℝ, y < stRecL s ∧ lHit (stChart s) ⊤ D y :=
  not_leftHit_of_lProf3 hI.1 (hI.2.2 hst).1 k θ' hreg hgood hthr

end InteractingSLE.Theorem14.SB.Lk
