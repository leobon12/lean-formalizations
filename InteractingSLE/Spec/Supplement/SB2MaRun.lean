/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MaL

/-!
# The strong exclusion of left hits along the right walk

Packet PROVE-T14-SB2LIFT (round 15; item 1 of handoff §R14.2). Under GW1's stage data (`WalkStageData`) the right
walk keeps its left profile, and at its right thresholds it has a right profile with the current point at the record.
Hence no launch hits a point left of the left record (`Lk.NoLeftHit`, the strong form):

* `ThrOK s`: at a right threshold or a zero-lifetime threshold, `RProf s` holds and the current point is the record;
* `profiles_launch`: a launch from a launch-ready state (`RProf`, `RReady`, a good record) keeps `LProf3` and gives
  `ThrOK`. A zero lifetime swallows nothing beyond the record (`lAlive_of_zero`), and a right threshold carries the
  right profile (`rProf_launch`, `rProf_launch_zero`);
* `profiles_cont`: a connector step from an allowed state keeps both. A right move goes to a mark beyond the record,
  which has a positive chart value (`lProf3_moveAlong_true`);
* **`profiles_run`**: `LProf3` and `ThrOK` at every stage;
* **`noLeftHit_of_stageData`**: `NoLeftHit` at every step (`not_leftHit_of_lProf3`, `noLeftThr_of_stageData`);
* **`ae_noLeftHit_of_theorem13`**: almost surely for the lower walk of a staged history (Theorem 1.3 at universe `0`,
  through `walkStageData_of_theorem13`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol fwdMap)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Restart GW1W GW1WalkExit GW1WalkFinish

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **At a right threshold or a zero-lifetime threshold the right profile holds and the point is the record.** -/
def ThrOK (s : ExplState) : Prop :=
  (stStatus s = stThr (some true) ∨ stStatus s = stThr none) → RProf s ∧ stPt s = stRecR s

theorem stRecL_setDead (s : ExplState) : stRecL (setDead s) = stRecL s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem stRecL_moveToEnd' (s : ExplState) (r : Bool) : stRecL (ExplState.moveToEnd s r) = stRecL s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem lProf3_of_eq {s t : ExplState} (hc : stChart t = stChart s) (hr : stRecL t = stRecL s) (h : LProf3 s) :
    LProf3 t := by
  unfold LProf3; rw [hc, hr]; exact h

/-- The connector step from a dead state keeps the chart and the left record. -/
theorem contStep_dead_chart {s : ExplState} (hs : stStatus s = stDead) (J : Finset ℝ) (pref : Bool) :
    stChart (ExplState.contStep κ b J s none pref) = stChart s ∧
      stRecL (ExplState.contStep κ b J s none pref) = stRecL s ∧
      stStatus (ExplState.contStep κ b J s none pref) = stDead := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at hs
  subst hs
  exact ⟨rfl, rfl, rfl⟩

/-- **A launch from a launch-ready state keeps the left profile and gives `ThrOK`.** -/
theorem profiles_launch {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hl : LProf3 s) (hr : RProf s)
    (hready : RReady s) (k : ℕ) (θ' : ℝ) (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D))) :
    LProf3 (ExplState.launch s k D θ' ⊤) ∧ ThrOK (ExplState.launch s k D θ' ⊤) := by
  by_cases hT : D.2 = ⊤
  · have e := launch_eq_of_top s k D θ' ⊤ (by rw [hT, min_self])
    refine ⟨lProf3_of_eq e.1 e.2.2.2.1 hl, fun h => ?_⟩
    rw [e.2.2.2.2.1] at h
    rcases h with h | h <;> exact absurd h (by intro h'; cases h')
  · refine ⟨lProf3_launch hl k θ' hreg (hgood hT) hT, fun hthr => ?_⟩
    obtain ⟨-, -, hrec, -, hst, hpt⟩ := launch_eq_of_ne_top s k D θ' ⊤ (min_top_ne_top hT)
    have hnlt : ¬ (⊤ : ℝ≥0∞) < D.2 := not_lt.2 le_top
    by_cases h0 : D.2 = 0
    · refine ⟨(rProf_launch_zero hr k θ' hreg h0).1, ?_⟩
      rw [hpt, hrec]
      have hptl : lPt s ⊤ D = stPt s := by simp only [lPt, h0, ↓reduceIte, ite_self]
      have hempty : {x : ℝ | stRecR s < x ∧ ¬ lAlive (stChart s) ⊤ D x} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
        intro hx
        refine lAlive_of_zero hreg.2.1 h0 ?_
        rw [hr.1.eq_ofReal x]
        exact_mod_cast (hr.2.2.1 x hx).ne'
      have hlrec : lRecR s ⊤ D = stRecR s := by
        unfold lRecR
        rw [hempty, insert_empty_eq, csSup_singleton]
      rw [hptl, hlrec]
      exact hready.2
    · -- a positive finite lifetime: the threshold is a right one, with a right hit
      have hR : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ D x := by
        by_contra hR
        rw [hst] at hthr
        by_cases hL : ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) ⊤ D x
        · simp only [lStatus, hnlt, h0, hR, hL, ↓reduceIte] at hthr
          rcases hthr with h | h <;> exact absurd h (by intro h'; cases h')
        · simp only [lStatus, hnlt, h0, hR, hL, ↓reduceIte] at hthr
          rcases hthr with h | h <;> exact absurd h (by intro h'; cases h')
      refine ⟨(rProf_launch hr k θ' hreg (hgood hT) hT hR).1, ?_⟩
      rw [hpt, hrec]
      simp only [lPt, hnlt, h0, hR, ↓reduceIte]

/-- **A connector step from an allowed state keeps the left profile and `ThrOK`.** -/
theorem profiles_cont {s : ExplState} (hs : AllowedSt κ b s) (hl : LProf3 s) (ht : ThrOK s) :
    LProf3 (ExplState.contStep κ b jumps s none true) ∧ ThrOK (ExplState.contStep κ b jumps s none true) := by
  rcases hs with ha | hd | hd | hout
  · rw [contStep_of_arcM ha]
    exact ⟨hl, ht⟩
  · rw [contStep_of_done' hd]
    exact ⟨hl, ht⟩
  · obtain ⟨h1, h2, h3⟩ := contStep_dead_chart (κ := κ) (b := b) hd jumps true
    refine ⟨lProf3_of_eq h1 h2 hl, fun h => ?_⟩
    rw [h3] at h
    rcases h with h | h <;> exact absurd h (by intro h'; cases h')
  · have hthr : stStatus s = stThr (some true) ∨
        (stStatus s = stThr none ∧ PiecewiseConstantBoundaryData.rightLim b (stPt s) +
          stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ) := by
      rcases hout with h | ⟨h, hlow⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by simpa using hlow⟩
    obtain ⟨hr, hpr⟩ := ht (hthr.imp id fun h => h.1)
    have hform : ExplState.contStep κ b jumps s none true = if hC : (restartSet κ b jumps s).Nonempty then
        ExplState.moveAlong s true ((restartSet κ b jumps s).min' hC) true else ExplState.moveToEnd s true := by
      rcases hthr with h | ⟨h, hlow⟩
      · exact contStep_thr_true' b jumps s h
      · exact contStep_thr_none_right b jumps s h hlow
    rw [hform]
    by_cases hC : (restartSet κ b jumps s).Nonempty
    · simp only [hC, ↓reduceDIte]
      have hmem := Finset.min'_mem _ hC
      simp only [restartSet, Finset.mem_filter] at hmem
      have hw : stRecR s < (restartSet κ b jumps s).min' hC := hpr ▸ hmem.2.1
      refine ⟨lProf3_moveAlong_true hl (hr.2.2.1 _ hw) true, fun h => ?_⟩
      rw [stStatus_moveAlong'] at h
      rcases h with h | h <;> exact absurd h (by intro h'; cases h')
    · simp only [hC, ↓reduceDIte]
      refine ⟨lProf3_of_eq (stChart_moveToEnd' s true) (stRecL_moveToEnd' s true) hl, fun h => ?_⟩
      rw [stStatus_moveToEnd''] at h
      rcases h with h | h <;> exact absurd h (by intro h'; cases h')

/-- **The left profile and `ThrOK` at every stage** under the stage data. -/
theorem profiles_run {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : WalkStageData κ b jumps θ true D)
    (hreg : ∀ j, IsRegularDriver (D j)) :
    ∀ n, LProf3 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∧
      ThrOK (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)
  | 0 => by
    have e : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0 = ExplState.init 0 := by
      simp [ExplState.run, boundaryWalkSpec]
    rw [e]
    refine ⟨lProf3_init 0, fun h => ?_⟩
    rcases h with h | h <;> exact absurd h (by intro h'; cases h')
  | n + 1 => by
    obtain ⟨hl, ht⟩ := profiles_run hS hreg n
    set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hsdef
    by_cases hk : n < (boundaryWalkSpec b jumps θ true).2.2.length
    · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
      · have hstep := GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true)
          (D := D) hk hev
        rcases flowStep_trichotomy (κ := κ) (b := b) false s n (D n) θ ⊤ with e | e | e
        · rw [hstep, e]; exact ⟨hl, ht⟩
        · rw [hstep, e]
          refine ⟨lProf3_of_eq (stChart_setDead s) (stRecL_setDead s) hl, fun h => ?_⟩
          rw [stStatus_setDead] at h
          rcases h with h | h <;> exact absurd h (by intro h'; cases h')
        · have hlne : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none := by
            rw [hstep, e]; exact launched_launch s n (D n) θ ⊤
          obtain ⟨hprof, hrdy, hgood, -⟩ := hS n hlne
          rw [hstep, e]
          exact profiles_launch hl hprof hrdy n θ (hreg n) hgood
      · have hstep := GW1W.run_succ_walk_cont (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true)
          (D := D) hk hodd
        have hn1 : 1 ≤ n := by omega
        have hall := (allowedSt_run hS n).1 hn1
        rw [hstep]
        exact profiles_cont hall hl ht
    · have e : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) = s := by
        rw [run_succ]
        have : (boundaryWalkSpec b jumps θ true).2.2[n]? = none := List.getElem?_eq_none (not_lt.1 hk)
        rw [this]
      rw [e]; exact ⟨hl, ht⟩

/-- **No launch hits a point left of the left record** under the stage data. -/
theorem noLeftHit_of_stageData {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : WalkStageData κ b jumps θ true D)
    (hreg : ∀ j, IsRegularDriver (D j)) (n : ℕ) : NoLeftHit κ b jumps θ D n := by
  intro hlne
  obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hlne
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
  obtain ⟨hprof, -, hgood, -⟩ := hS n hlne
  have hthr : stStatus (ExplState.launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) n (D n)
      θ' ⊤) ≠ stThr (some false) := by
    rw [← he]; exact noLeftThr_of_stageData hS n hlne
  exact not_leftHit_of_lProf3 (profiles_run hS hreg n).1 hprof n θ' (hreg n) hgood hthr

/-- **Almost surely no launch of the lower walk hits a point left of the left record** (Theorem 1.3 at universe `0`,
in the setting of `GW1WalkFinish.WalkLocalStatement`). -/
theorem ae_noLeftHit_of_theorem13 (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec k ω, IsRegularDriver (E spec k ω)) :
    ∀ᵐ ω ∂P, ∀ n, NoLeftHit κ b jumps (-(Real.pi / 2))
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n := by
  have hS := walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true
  filter_upwards [hS] with ω hω n
  exact noLeftHit_of_stageData hω (fun j => hreg _ j ω) n

end InteractingSLE.Theorem14.SB.Lk
