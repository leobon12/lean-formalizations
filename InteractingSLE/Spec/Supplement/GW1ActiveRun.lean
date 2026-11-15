/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveChart

/-!
# Lemma GW1's walks: between two launches (deterministic bookkeeping)

Packet PROVE-T14-GW1W. A boundary walk program (`boundaryWalkSpec`, Lemma GW1, p. 618) alternates ordinary pieces
(`flow θ ⊤`, even indices) and boundary continuations (`cont right`, odd indices). Between two consecutive launches
`ℓ < k` of a walk:

* both indices are even, so `ℓ + 2 ≤ k`;
* the state at `k` is the state right after the continuation `ℓ + 1` that follows the piece `ℓ`
  (`run_eq_of_last_launch`): a flow instruction that does not launch and a continuation from a state *on an arc at a
  mark*, *done* or *dead* change nothing;
* that state is *on an arc at a mark* (`status_run_of_last_launch`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (IsForwardSol chiC fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart

/-- The status *on an arc at its restart mark*, moving right (`r = true`) or left. -/
abbrev stArcM (r : Bool) : ExplStatus := .inr (.inr (.inr (.inl (r, true))))

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- A flow step of a non-GW2 program keeps the state or launches. -/
theorem flowStep_false_cases (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ b false s k D θ t = s ∨
      ExplState.flowStep κ b false s k D θ t = ExplState.launch s k D θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  rcases status with u | u | o | bb | u | u
  · exact Or.inr rfl
  · exact Or.inr rfl
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- A flow step of a non-GW2 program that does not launch changes nothing. -/
theorem flowStep_eq_self_of_noLaunch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hn : (ExplState.flowStep κ b false s k D θ t).2.2.2.1 k = none) :
    ExplState.flowStep κ b false s k D θ t = s := by
  rcases flowStep_false_cases (κ := κ) (b := b) s k D θ t with e | e
  · exact e
  · rw [e, launches_launch, Function.update_self] at hn
    exact absurd hn (by simp)

/-- After a boundary continuation without a stop point, the state is *on an arc at a mark*, *done* or *dead*. -/
theorem status_contStep (s : ExplState) (pref : Bool) :
    (∃ r, stStatus (ExplState.contStep κ b jumps s none pref) = stArcM r) ∨
      stStatus (ExplState.contStep κ b jumps s none pref) = stDone ∨
      stStatus (ExplState.contStep κ b jumps s none pref) = stDead := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.contStep
  dsimp only
  repeat' first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | split

/-- A boundary continuation from a state *on an arc at a mark*, *done* or *dead* changes nothing. -/
theorem contStep_eq_self (s : ExplState) (pref : Bool)
    (hs : (∃ r, stStatus s = stArcM r) ∨ stStatus s = stDone ∨ stStatus s = stDead) :
    ExplState.contStep κ b jumps s none pref = s := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases hs with ⟨r, h⟩ | h | h <;> change status = _ at h <;> subst h <;> rfl

end Run

section Walk

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A launch of a walk happens at an even index inside the program. -/
theorem even_of_launches_walk {k : ℕ}
    (h : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    k % 2 = 0 ∧ k < (boundaryWalkSpec b jumps θ right).2.2.length := by
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 h
  obtain ⟨hk, -, -⟩ := eq_launch_of_launches _ _ hcθ
  rw [GW1Conn.getElem?_boundaryWalkSpec] at hk
  split_ifs at hk with hlt hev
  · exact ⟨hev, hlt⟩
  · exact absurd hk (by simp)

/-- A continuation instruction of a walk. -/
theorem run_succ_walk_cont {k : ℕ} (hk : k < (boundaryWalkSpec b jumps θ right).2.2.length) (hodd : k % 2 = 1) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1) =
      ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) none right := by
  rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  rfl

/-- An ordinary-piece instruction of a walk. -/
theorem run_succ_walk_flow {k : ℕ} (hk : k < (boundaryWalkSpec b jumps θ right).2.2.length) (hev : k % 2 = 0) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1) =
      ExplState.flowStep κ b false (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) k (D k) θ ⊤ := by
  rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_left_of_eq_true _ _ (eq_true hev)]
  rfl

/-- **Between two consecutive launches `ℓ < k` of a walk** the state at `k` is the state right after the boundary
continuation `ℓ + 1`, and it is on an arc at a mark. -/
theorem run_eq_of_last_launch {ℓ k : ℕ} (hℓk : ℓ < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hn : ∀ j, ℓ < j → j < k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j = none) :
    ℓ + 2 ≤ k ∧ ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k =
        ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (ℓ + 1))
          none right ∧
      ∃ r, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) = stArcM r := by
  obtain ⟨hℓe, -⟩ := even_of_launches_walk hl
  obtain ⟨hke, hklen⟩ := even_of_launches_walk hk
  have h2 : ℓ + 2 ≤ k := by omega
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D with hR
  have hc : R (ℓ + 1 + 1) = ExplState.contStep κ b jumps (R (ℓ + 1)) none right :=
    run_succ_walk_cont (by omega) (by omega)
  have hst := status_contStep (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) right
  rw [← hc] at hst
  have hconst : ∀ n, ℓ + 2 + n ≤ k → R (ℓ + 2 + n) = R (ℓ + 2) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn'
      have ih' := ih (by omega)
      rw [show ℓ + 2 + (n + 1) = ℓ + 2 + n + 1 by ring]
      rcases Nat.mod_two_eq_zero_or_one (ℓ + 2 + n) with hev | hodd
      · have e := run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := right) (D := D)
          (k := ℓ + 2 + n) (by omega) hev
        have hnl := hn (ℓ + 2 + n) (by omega) (by omega)
        rw [← hR] at e
        rw [e] at hnl
        rw [e, flowStep_eq_self_of_noLaunch _ _ _ _ _ hnl, ih']
      · have e := run_succ_walk_cont (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := right) (D := D)
          (k := ℓ + 2 + n) (by omega) hodd
        rw [← hR] at e
        rw [e, ih']
        exact contStep_eq_self _ _ hst
  have hRk : R k = R (ℓ + 2) := by
    have := hconst (k - (ℓ + 2)) (by omega)
    rwa [show ℓ + 2 + (k - (ℓ + 2)) = k by omega] at this
  refine ⟨h2, by rw [hRk]; exact hc, ?_⟩
  rw [hRk]
  rcases hst with h | h | h
  · exact h
  all_goals
    exfalso
    have hT : IsTerminal (R k) := by rw [hRk]; unfold IsTerminal; first | exact Or.inl h | exact Or.inr h
    have e := run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := right) (D := D)
      (k := k) hklen hke
    rw [← hR] at e
    rw [e, isTerminal_flowStep hT, hR, launches_run_of_le _ _ le_rfl] at hk
    exact hk rfl

end Walk

/-! ### One stage of the right walk -/

section Stage

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A flow step from a state on an arc at its mark with an inadmissible seed changes nothing. -/
theorem flowStep_arc_eq_self (s : ExplState) (k : ℕ) (D₀ : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hst : stStatus s = .inr (.inr (.inr (.inl (true, true)))))
    (hna : ¬ ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ) :
    ExplState.flowStep κ b false s k D₀ θ t = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  change st = _ at hst
  subst hst
  simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h
  · exact absurd h hna
  · rfl

/-- The angle and the own time of a launched instruction of a walk. -/
theorem launch_walk {k : ℕ} {right : Bool}
    (h : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1) =
      ExplState.launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) k (D k) θ ⊤ := by
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 h
  obtain ⟨hk, hrun, -⟩ := eq_launch_of_launches _ _ hcθ
  have hk' := hk
  rw [GW1Conn.getElem?_boundaryWalkSpec] at hk'
  split_ifs at hk' with hlt hev
  · have ht : instrTime (boundaryWalkSpec b jumps θ right) k = ⊤ := by
      unfold instrTime
      rw [GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left_of_eq_true _ _ (eq_true hlt),
        ite_eq_left_of_eq_true _ _ (eq_true hev)]
    rw [ht] at hk'
    simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at hk'
    rw [hrun, ht, hk'.1]
  · exact absurd hk' (by simp)

/-- **One stage of the right walk restores the invariant at the next launch** (Lemma GW1, deterministic part): from a
launch-ready state with the invariant for the word `β` at the launch `ℓ`, if the next launch is at `k`, the piece `ℓ`
has a regular driver with a good record at a finite stop, it does not end at a new left record, and a right threshold
leaves a low original height outward, then the state at `k` is launch-ready with the invariant for the word
`shiftW a (stopWord κ (β, θ, record))`, where `a` is the recentring of the chart. -/
theorem rInv_walk_step (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {ℓ k : ℕ}
    (hℓk : ℓ < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hn : ∀ j, ℓ < j → j < k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j = none)
    (hI : RInv κ θ b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hR : RReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hroot : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) = .inl () →
      leftLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)) + θ * chiC κ <
        sleLambda κ)
    (hreg : IsRegularDriver (D ℓ)) (hgood : (D ℓ).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D ℓ))))
    (hnoL : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)) ≠ stThr (some false))
    (hF2 : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)) = stThr (some true) →
      rightLim b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1))) + θ * chiC κ ≤
        -sleLambda κ) :
    RInv κ θ b jumps (BoundaryWord.shiftW (rProf (stChart (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ true) D (ℓ + 1))) (stPt (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ true) D k))) (stopWord κ (β, θ, recOf ⊤ (D ℓ))))
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) ∧
    RReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) ∧
    rProf (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) =
      ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1))).1 0 -
        (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)).1 0).re := by
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D with hRdef
  obtain ⟨-, hrunk, r, hstk⟩ := run_eq_of_last_launch hℓk hk hl hn
  have hrun1 : R (ℓ + 1) = ExplState.launch (R ℓ) ℓ (D ℓ) θ ⊤ := launch_walk hl
  have hγL : ∀ y, y < 0 → (stopWord κ (β, θ, recOf ⊤ (D ℓ))).fn y + θ * chiC κ < sleLambda κ :=
    fun y hy => stopWord_fn_add_lt_of_neg hκ hI.1 _ hy
  have hstk' : ∃ r, stStatus (R k) = .inr (.inr (.inr (.inl (r, true)))) := ⟨r, hstk⟩
  -- the lifetime of the piece
  by_cases htop : (D ℓ).2 = ⊤
  · exfalso
    have hmin : min ⊤ (D ℓ).2 = ⊤ := by rw [htop]; rfl
    have hd := (launch_eq_of_top (R ℓ) ℓ (D ℓ) θ ⊤ hmin).2.2.2.2.1
    rw [← hrun1] at hd
    have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) true (Or.inr (Or.inl hd))
    rw [← hrunk, ] at this
    rw [this, hd] at hstk
    exact absurd hstk (by simp [stArcM])
  by_cases h0 : (D ℓ).2 = 0
  · -- a zero lifetime: only at the root does a boundary continuation follow
    have hnt : stStatus (R ℓ) ≠ .inr (.inl ()) := by
      rcases hR.1 with h | h <;> rw [h] <;> simp
    obtain ⟨hst1, hpt1, hang1⟩ := launch_zero (k := ℓ) (θ := θ) h0 hnt
    rw [← hrun1] at hst1 hpt1 hang1
    rcases hR.1 with hroot' | harc
    · -- the root
      have hL0 := hroot hroot'
      by_cases hlow : rightLim b (stPt (R (ℓ + 1))) + θ * chiC κ ≤ -sleLambda κ
      · have hc := contStep_thr_none_right (κ := κ) b jumps (R (ℓ + 1)) hst1 (by rw [hang1]; exact hlow)
        rw [← hrunk] at hc
        obtain ⟨hs₁, hrel⟩ := rProf_launch_zero hI.2.1 ℓ θ hreg h0
        rw [← hrun1] at hs₁ hrel
        have hO := rOrig_of_rel hκ hb (s₁ := R (ℓ + 1)) hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩
        have hRR : stRecR (R (ℓ + 1)) = stRecR (R ℓ) := by
          have h1 := hs₁.2.2.2
          rw [hrun1]
          obtain ⟨-, -, hrec, -, -, -⟩ := launch_eq_of_ne_top (R ℓ) ℓ (D ℓ) θ ⊤ (min_top_ne_top htop)
          rw [hrec]
          unfold lRecR
          have he : {x : ℝ | stRecR (R ℓ) < x ∧ ¬ lAlive (stChart (R ℓ)) ⊤ (D ℓ) x} = ∅ := by
            ext x
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
            intro hx
            unfold lAlive
            have hT : stopTime ⊤ (D ℓ) = 0 := by simp [stopTime, h0]
            rw [hT, hI.2.1.1.eq_ofReal x]
            exact exists_isForwardSol_zero (stopDrv_zero hreg ⊤) (hI.2.1.2.2.1 x hx).ne'
          rw [he, insert_empty_eq, csSup_singleton]
        have hpt : stPt (R (ℓ + 1)) = stRecR (R (ℓ + 1)) := by rw [hpt1, hRR]; exact hR.2
        exact rInv_tail hκ hb hs₁ hO hγL hpt hang1 hlow hc hstk'
      · -- no boundary continuation: the walk dies
        exfalso
        have hd := contStep_thr_none_dead (κ := κ) b jumps (R (ℓ + 1)) hst1
          (by rw [hpt1, hang1]; exact hL0) (by rw [hang1]; exact lt_of_not_ge hlow) true
        rw [← hrunk, hstk] at hd
        exact absurd hd (by simp [stArcM, stDead])
    · -- on an arc: the seed was admissible, so the walk dies
      exfalso
      have hadm : ExplState.IsAdmissibleSeed κ (leftLim b (stPt (R ℓ))) (rightLim b (stPt (R ℓ))) θ := by
        have e := run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) (D := D)
          (k := ℓ) (even_of_launches_walk hl).2 (even_of_launches_walk hl).1
        rw [← hRdef] at e
        by_contra hna
        have hfs : ExplState.flowStep κ b false (R ℓ) ℓ (D ℓ) θ ⊤ = R ℓ :=
          flowStep_arc_eq_self (R ℓ) ℓ (D ℓ) θ ⊤ harc hna
        rw [e, hfs, launches_run_of_le _ _ le_rfl] at hl
        exact hl rfl
      have hd := contStep_thr_none_dead (κ := κ) b jumps (R (ℓ + 1)) hst1
        (by rw [hpt1, hang1]; exact hadm.1) (by rw [hpt1, hang1]; exact hadm.2) true
      rw [← hrunk, hstk] at hd
      exact absurd hd (by simp [stArcM, stDead])
  · -- a finite positive lifetime: a right threshold
    have hcases := launch_status_of_pos (s := R ℓ) (k := ℓ) (θ := θ) htop h0
    rw [← hrun1] at hcases
    rcases hcases with hthr | hthr | hthr
    · obtain ⟨-, hhit, hpt, hang⟩ := launch_thr_true (s := R ℓ) (k := ℓ) (θ := θ) htop (by rw [← hrun1]; exact hthr)
      rw [← hrun1] at hpt hang
      obtain ⟨hs₁, hrel⟩ := rProf_launch hI.2.1 ℓ θ hreg (hgood htop) htop hhit
      rw [← hrun1] at hs₁ hrel
      have hO := rOrig_of_rel hκ hb (s₁ := R (ℓ + 1)) hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩
      have hc := contStep_thr_true' (κ := κ) b jumps (R (ℓ + 1)) hthr
      rw [← hrunk] at hc
      exact rInv_tail hκ hb hs₁ hO hγL hpt hang (by rw [hpt]; exact hF2 hthr) hc hstk'
    · exact absurd hthr hnoL
    · exfalso
      have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) true (Or.inr (Or.inr hthr))
      rw [← hrunk] at this
      rw [this, hthr] at hstk
      exact absurd hstk (by simp [stArcM, stDead])

end Stage

end GW1W

end Theorem14

end InteractingSLE
