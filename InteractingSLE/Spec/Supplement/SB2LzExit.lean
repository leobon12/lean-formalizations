/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LyRun
import InteractingSLE.Spec.Supplement.GW1WalkExitData

/-!
# No left moves from GW1's stage data

Packet PROVE-T14-SB2LIFT (round 14; item 2 of handoff §R13.2, the GW1-type inputs). GW1 proves almost surely, for
the right boundary walk of a staged history, the stage data `GW1WalkExit.WalkStageData`
(`GW1WalkExit.ae_walkStageData_right`, `walkStageData_of_theorem13`). In particular every launch has a classified
exit: after it the walk is done, or at an outward right threshold (a right threshold, or a zero-lifetime threshold
with a low right height). This file draws the deterministic consequences:

* **`AllowedSt κ b s`**: a right mark, done, dead, or an outward right threshold;
* **`allowedSt_run`**: every stage after the first flow instruction is allowed. The root launches into a classified
  exit. A flow step keeps the state, kills it, or launches into a classified exit. A connector step from an allowed
  status moves right, ends, or keeps the state;
* **`noLeftMove_of_stageData`**: the walk never moves left (`Lk.NoLeftMove` at every step);
* **`noLeftThr_of_stageData`**: no launch ends at a left threshold (`NoLeftThr`, the status form of "no left hit").

`NoLeftMove` is the named input of `recInv_ptRec_run`/`walkMovesRight_run` (round 12). `NoLeftThr` is GW1's form of
the left-hit exclusion; the full `NoLeftHit` (no left hit at all, even alongside a right hit) additionally needs that
real points on the two sides of the driver are not swallowed at the same time (§R14.2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkExit GW1WalkFinish
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The allowed statuses of the right walk**: a right mark, done, dead, or an outward right threshold. -/
def AllowedSt (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : Prop :=
  stStatus s = GW1W.stArcM true ∨ stStatus s = stDone ∨ stStatus s = stDead ∨ OutwardThreshold κ b true s

/-- **No launch ends at a left threshold** (status form of "no left hit"). -/
def NoLeftThr (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) : Prop :=
  (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none →
    stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) ≠ stThr (some false)

/-- A classified exit is an allowed status. -/
theorem allowedSt_of_classifiedExit {s t : ExplState} (h : ClassifiedExit κ b true s t) : AllowedSt κ b t := by
  rcases h.1 with hd | ⟨-, hout⟩
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr (Or.inr hout))

/-- The launches recorded by a launch. -/
theorem launched_launch (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ' : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k d θ' t).2.2.2.1 k ≠ none := by
  rw [launches_launch, Function.update_self]; simp

/-- **A flow step from an allowed (or root) state gives an allowed state** under the stage data. -/
theorem allowedSt_flow {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : WalkStageData κ b jumps θ true D) {k : ℕ}
    (hk : k < (boundaryWalkSpec b jumps θ true).2.2.length) (hev : k % 2 = 0)
    (hs : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) ∨
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) = .inl ()) :
    AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) ∧
      NoLeftMove κ b jumps θ D k := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k with hsdef
  have hstep := GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) (D := D) hk hev
  -- a flow step never moves along the boundary
  have hnm : NoLeftMove κ b jumps θ D k := by
    intro w m e
    rw [hstep] at e
    have hne := arcs_moveAlong_ne s false w m
    rcases flowStep_trichotomy (κ := κ) (b := b) false s k (D k) θ ⊤ with e' | e' | e' <;> rw [e'] at e
    · exact hne (congrArg (fun t : ExplState => t.2.1) e).symm
    · exact hne ((congrArg (fun t : ExplState => t.2.1) e).symm.trans (arcs_setDead s))
    · exact hne ((congrArg (fun t : ExplState => t.2.1) e).symm.trans (GW2aCont.arcs_launch s k (D k) θ ⊤))
  refine ⟨?_, hnm⟩
  rcases flowStep_trichotomy (κ := κ) (b := b) false s k (D k) θ ⊤ with e' | e' | e'
  · rw [hstep, e']
    rcases hs with hs | hs
    · exact hs
    · -- the root always launches
      exfalso
      have : ExplState.flowStep κ b false s k (D k) θ ⊤ = ExplState.launch s k (D k) θ ⊤ := by
        obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
        change status = _ at hs
        subst hs
        rfl
      rw [this] at e'
      have h1 := launched_launch s k (D k) θ ⊤
      rw [e'] at h1
      exact h1 (launches_run_of_le (κ := κ) (b := b) (jumps := jumps) _ D (le_refl k))
  · rw [hstep, e']
    exact Or.inr (Or.inr (Or.inl (stStatus_setDead s)))
  · have hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none := by
      rw [hstep, e']; exact launched_launch s k (D k) θ ⊤
    exact allowedSt_of_classifiedExit (hS k hl).2.2.2

/-- **A connector step from an allowed state gives an allowed state and does not move left.** -/
theorem allowedSt_cont {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hk : k < (boundaryWalkSpec b jumps θ true).2.2.length) (hodd : k % 2 = 1)
    (hs : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) :
    AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) ∧
      NoLeftMove κ b jumps θ D k := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k with hsdef
  have hstep := GW1W.run_succ_walk_cont (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) (D := D) hk hodd
  -- the step from an outward threshold, in the restart form
  have hright : ∀ hthr : (stStatus s = stThr (some true) ∨
      (stStatus s = stThr none ∧ rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ)),
      ExplState.contStep κ b jumps s none true = if hC : (restartSet κ b jumps s).Nonempty then
        ExplState.moveAlong s true ((restartSet κ b jumps s).min' hC) true else ExplState.moveToEnd s true := by
    rintro (h | ⟨h, hlow⟩)
    · exact contStep_thr_true' b jumps s h
    · exact contStep_thr_none_right b jumps s h hlow
  have hform : ∀ hthr : (stStatus s = stThr (some true) ∨
      (stStatus s = stThr none ∧ rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ)),
      AllowedSt κ b (ExplState.contStep κ b jumps s none true) ∧
        ∀ (w : ℝ) (m : Bool), ExplState.contStep κ b jumps s none true ≠ ExplState.moveAlong s false w m := by
    intro hthr
    rw [hright hthr]
    by_cases hC : (restartSet κ b jumps s).Nonempty
    · simp only [hC, ↓reduceDIte]
      refine ⟨Or.inl (stStatus_moveAlong' _ _ _ _), fun w m e => ?_⟩
      have := congrArg stStatus e
      rw [stStatus_moveAlong', stStatus_moveAlong'] at this
      simp at this
    · simp only [hC, ↓reduceDIte]
      refine ⟨Or.inr (Or.inl (stStatus_moveToEnd'' _ _)), fun w m e => ?_⟩
      have := congrArg stStatus e
      rw [stStatus_moveToEnd'', stStatus_moveAlong'] at this
      exact absurd this (by intro h; cases h)
  -- the unchanged and dead steps keep their connectors
  have hsame : ∀ t : ExplState, t.2.1 = s.2.1 → ∀ (w : ℝ) (m : Bool), t ≠ ExplState.moveAlong s false w m :=
    fun t ht w m e => arcs_moveAlong_ne s false w m (by rw [← e]; exact ht)
  rcases hs with ha | hd | hd | hout
  · rw [hstep, contStep_of_arcM ha]
    exact ⟨Or.inl ha, fun w m e => hsame s rfl w m (by rw [hstep, contStep_of_arcM ha] at e; exact e)⟩
  · rw [hstep, contStep_of_done' hd]
    exact ⟨Or.inr (Or.inl hd), fun w m e => hsame s rfl w m (by rw [hstep, contStep_of_done' hd] at e; exact e)⟩
  · obtain ⟨-, h2, -, -, h5⟩ := contStep_of_dead (κ := κ) (b := b) (J := jumps) hd true
    rw [hstep]
    exact ⟨Or.inr (Or.inr (Or.inl h2)), fun w m e => hsame _ h5 w m (by rw [hstep] at e; exact e)⟩
  · have hthr : stStatus s = stThr (some true) ∨
        (stStatus s = stThr none ∧ rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ) := by
      rcases hout with h | ⟨h, hlow⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by simpa using hlow⟩
    obtain ⟨h1, h2⟩ := hform hthr
    rw [hstep]
    exact ⟨h1, fun w m e => h2 w m (by rw [hstep] at e; exact e)⟩

/-- **Every stage after the first flow instruction is allowed, and the walk never moves left**, under the stage
data (while the program has instructions; afterwards the run is constant). -/
theorem allowedSt_run {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : WalkStageData κ b jumps θ true D) :
    ∀ n, (1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
      NoLeftMove κ b jumps θ D n
  | 0 => by
    have hroot : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = .inl () := by
      simp [ExplState.run, ExplState.init]
    have hlen : 0 < (boundaryWalkSpec b jumps θ true).2.2.length := by
      rw [GW1WalkFinish.boundaryWalk_length]; omega
    exact ⟨fun h => absurd h (by omega), (allowedSt_flow hS hlen rfl (Or.inr hroot)).2⟩
  | n + 1 => by
    obtain ⟨ih, -⟩ := allowedSt_run hS n
    have hcur : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hroot : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = .inl () := by
          simp [ExplState.run, ExplState.init]
        have hlen : 0 < (boundaryWalkSpec b jumps θ true).2.2.length := by
          rw [GW1WalkFinish.boundaryWalk_length]; omega
        exact (allowedSt_flow hS hlen rfl (Or.inr hroot)).1
      · have hs := ih hn
        by_cases hk : n < (boundaryWalkSpec b jumps θ true).2.2.length
        · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
          · exact (allowedSt_flow hS hk hev (Or.inl hs)).1
          · exact (allowedSt_cont hk hodd hs).1
        · have e : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) =
              ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n := by
            rw [run_succ]
            have : (boundaryWalkSpec b jumps θ true).2.2[n]? = none := List.getElem?_eq_none (not_lt.1 hk)
            rw [this]
          rw [e]; exact hs
    refine ⟨fun _ => hcur, ?_⟩
    by_cases hk : n + 1 < (boundaryWalkSpec b jumps θ true).2.2.length
    · rcases Nat.mod_two_eq_zero_or_one (n + 1) with hev | hodd
      · exact (allowedSt_flow hS hk hev (Or.inl hcur)).2
      · exact (allowedSt_cont hk hodd hcur).2
    · intro w m e
      have e' : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1 + 1) =
          ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) := by
        rw [run_succ]
        have : (boundaryWalkSpec b jumps θ true).2.2[n + 1]? = none := List.getElem?_eq_none (not_lt.1 hk)
        rw [this]
      rw [e'] at e
      exact arcs_moveAlong_ne _ false w m (congrArg (fun t : ExplState => t.2.1) e).symm

/-- **The walk never moves left** under the stage data. -/
theorem noLeftMove_of_stageData {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : WalkStageData κ b jumps θ true D) (n : ℕ) :
    NoLeftMove κ b jumps θ D n :=
  (allowedSt_run hS n).2

/-- **No launch ends at a left threshold** under the stage data. -/
theorem noLeftThr_of_stageData {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : WalkStageData κ b jumps θ true D) (n : ℕ) :
    NoLeftThr κ b jumps θ D n := by
  intro hl he
  rcases (hS n hl).2.2.2.1 with hd | ⟨-, h | ⟨h, -⟩⟩
  · rw [he] at hd; exact absurd hd (by intro h'; cases h')
  · rw [he] at h; exact absurd h (by intro h'; cases h')
  · rw [he] at h; exact absurd h (by intro h'; cases h')

/-- **Almost surely the lower walk never moves left and no launch ends at a left threshold** (Theorem 1.3 at universe
`0`, through GW1's stage data `walkStageData_of_theorem13`; the setting of `GW1WalkFinish.WalkLocalStatement`). -/
theorem ae_noLeftMove_noLeftThr_of_theorem13 (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec k ω, IsRegularDriver (E spec k ω)) :
    ∀ᵐ ω ∂P, ∀ n, NoLeftMove κ b jumps (-(Real.pi / 2))
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n ∧
      NoLeftThr κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n := by
  have hS := walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true
  filter_upwards [hS] with ω hω n
  exact ⟨noLeftMove_of_stageData hω n, noLeftThr_of_stageData hω n⟩

end InteractingSLE.Theorem14.SB.Lk
