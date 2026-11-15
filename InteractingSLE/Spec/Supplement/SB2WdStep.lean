/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WdLaunch

/-!
# SB2(1)'s active word: the lower walk's left side through one stage

Packet PROVE-T14-SB2WORD, steps 2–3 of `planning/handoffs/PROVE-T14-SB2FIN5.md` §R3. The left-side invariant `LW` of
a state and a word (the inward profile `LLeft`, the original word on the untouched left ray `LOrig`, the low side
`LLow`, continuity on the ray `LCont`, the real points of the pieces right of the left record, and `recL ≤ 0`) is
carried through one stage of the right walk (a launch, then the rightward continuation along a low connector), in the
form of GW1's `rInv_walk_step` (deterministic):

* `fn_le_of_connector`: on the connector the word has its original, low heights;
* **`lLow_moveAlong`**, **`lw_launch`**, **`lw_moveAlong`**, **`lw_tail`**, **`lw_walk_step`**, **`lw_root`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

namespace InteractingSLE.Theorem14.GW1W

open Exist Exist.StagedLaw Exist.Staged Restart
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-! ### The rightward continuation -/

section Move

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **On a low connector the word has its original, low heights** (Lemma GW1, (GW1.3); SB2(1), p. 632: "The exposed
rightward connectors retain their original heights `H ≤ −Λ`"): between the image `0` of the right record and the
image of the next restart mark `w`, the word is the original word at points of the connector. -/
theorem fn_le_of_connector {γ : BoundaryWord} {s₁ : ExplState} (hs₁ : RProf s₁) (hO : ROrig b jumps γ s₁) {w : ℝ}
    (hw : stRecR s₁ < w)
    (hlow : ∀ x, stRecR s₁ < x → x < w → x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ) {y : ℝ} (hy : 0 < y)
    (hyw : y < rProf (stChart s₁) w) (hyJ : y ∉ γ.jumps) : γ.fn y ≤ -sleLambda κ - θ * chiC κ := by
  obtain ⟨hc, hm, hpos, hsmall⟩ := hs₁
  set m := rProf (stChart s₁) with hmdef
  obtain ⟨x, hx, hmx⟩ := RProf.exists_eq ⟨hc, hm, hpos, hsmall⟩ hy
  rw [← hmdef] at hmx
  have hxw : x < w := by
    by_contra h
    push Not at h
    have := hm.1.monotoneOn hw hx h
    rw [hmx] at this
    linarith
  have hcx : ContinuousAt m x := hm.2.1.continuousAt (Ioi_mem_nhds hx)
  have hP : ∀ᶠ x' in 𝓝 x, x' < w ∧ γ.fn (m x') = γ.fn y := by
    have h1 := hcx.eventually (by rw [hmx]; exact γ.isPiecewiseConstantBoundaryData y hyJ)
    filter_upwards [gt_mem_nhds hxw, h1] with x' h2 h3
    exact ⟨h2, h3⟩
  obtain ⟨x', hx'R, hx'J, hmx'J, hx'w, hfn⟩ := exists_near_avoid hm.1 hx jumps γ.jumps hP
  rw [← hfn, hO x' hx'R hx'J hmx'J]
  have := hlow x' hx'R hx'w hx'J
  linarith

theorem pieces_moveAlong (s : ExplState) (r : Bool) (w : ℝ) (m : Bool) : (ExplState.moveAlong s r w m).1 = s.1 := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

/-- **The low side after a rightward move** along a low connector: the chart is recentred at the image `a > 0` of
the new point; points of `[−a, 0)` are images of the connector (original, low heights), the others are the old chart
points left of the tip, shifted. -/
theorem lLow_moveAlong {γ : BoundaryWord} {s₁ : ExplState} (hs₁ : RProf s₁) (hO : ROrig b jumps γ s₁)
    (hL : LLow κ θ γ s₁) {w : ℝ} (hw : stRecR s₁ < w)
    (hlow : ∀ x, stRecR s₁ < x → x < w → x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ) :
    LLow κ θ (BoundaryWord.shiftW (rProf (stChart s₁) w) γ) (ExplState.moveAlong s₁ true w true) := by
  set a := rProf (stChart s₁) w with hadef
  have ha : 0 < a := hs₁.2.2.1 w hw
  have hprof : ∀ x, rProf (stChart (ExplState.moveAlong s₁ true w true)) x = rProf (stChart s₁) x - a := by
    intro x
    rw [stChart_moveAlong, rProf_recenter]
    rfl
  intro y hy hyJ hyR
  have hyJ' : y + a ∉ γ.jumps := fun h => hyJ (by
    rw [BoundaryWord.jumps_shiftW]; exact Finset.mem_image.2 ⟨y + a, h, by ring⟩)
  rw [BoundaryWord.fn_shiftW]
  rw [stRecL_moveAlong_true'] at hyR
  rcases lt_trichotomy (y + a) 0 with hneg | hzero | hposa
  · refine hL (y + a) hneg hyJ' fun x hx => ?_
    have := hyR x hx
    rw [hprof] at this
    linarith
  · -- at the old tip, approach from the right (inside the connector)
    have hev := γ.isPiecewiseConstantBoundaryData (y + a) hyJ'
    have hfin : ∀ᶠ z in 𝓝[>] (y + a), z ∉ γ.jumps :=
      (eventually_notMem_of_finite γ.jumps.finite_toSet (y + a)).filter_mono
        (nhdsWithin_mono _ fun z hz => ne_of_gt hz)
    have hlt : ∀ᶠ z in 𝓝[>] (y + a), z < a := (gt_mem_nhds (by linarith : y + a < a)).filter_mono
      nhdsWithin_le_nhds
    obtain ⟨z, ⟨⟨hz, hzJ⟩, hza⟩, hzpos⟩ := (((hev.filter_mono nhdsWithin_le_nhds).and hfin).and hlt).and
      self_mem_nhdsWithin |>.exists
    rw [← hz]
    exact fn_le_of_connector hs₁ hO hw hlow (hzero ▸ hzpos) hza hzJ
  · exact fn_le_of_connector hs₁ hO hw hlow hposa (by linarith) hyJ'

end Move

/-! ### The left-side invariant -/

/-- **The left-side invariant of the lower walk** at a state `s` with word `β`. -/
def LW (κ θ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  LLeft s ∧ LOrig b jumps β s ∧ LLow κ θ β s ∧ LCont s ∧ PiecesRealBound s ∧ stRecL s ≤ 0

section Bundle

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The left-side invariant through a launch** with a good record at a finite stop (the stop word). -/
theorem lw_launch (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {s : ExplState}
    (hc : IsRealChart (stChart s)) (hcc : (stChart s).IsConformal) (hI : LW κ θ b jumps β s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D) (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hfin : D.2 ≠ ⊤) (hP : GW1P.PieceRegular D.1 D.2) :
    LW κ θ b jumps (stopWord κ (β, θ, recOf ⊤ D)) (ExplState.launch s k D θ ⊤) := by
  obtain ⟨hs, hO, hL, hC, hB, h0⟩ := hI
  obtain ⟨-, hs₁, hrel⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  exact ⟨hs₁, lOrig_of_rel' hκ hb hs hO θ ⟨hs₁, hrel⟩, lLow_launch hκ hc hs hL k hreg hgood hfin,
    lCont_launch hc hs hC k θ hreg hgood hfin, piecesRealBound_launch hcc hc hs hC hB k θ hreg hgood hfin hP,
    (stRecL_launch_le hc hs k θ hreg hgood hfin).trans h0⟩

/-- **The left-side invariant through a rightward move along a low connector** (the recentred word). -/
theorem lw_moveAlong {γ : BoundaryWord} {s₁ : ExplState} (hs₁ : RProf s₁) (hO : ROrig b jumps γ s₁)
    (hI : LW κ θ b jumps γ s₁) {w : ℝ} (hw : stRecR s₁ < w)
    (hlow : ∀ x, stRecR s₁ < x → x < w → x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ) :
    LW κ θ b jumps (BoundaryWord.shiftW (rProf (stChart s₁) w) γ) (ExplState.moveAlong s₁ true w true) := by
  obtain ⟨hs, hOL, hL, hC, hB, h0⟩ := hI
  have ha : 0 < rProf (stChart s₁) w := hs₁.2.2.1 w hw
  refine ⟨lLeft_moveAlong_true hs true ha.le, lOrig_moveAlong_true hOL true, lLow_moveAlong hs₁ hO hL hw hlow,
    fun x hx => ?_, fun p hp z hz hz0 => ?_, ?_⟩
  · rw [stRecL_moveAlong_true'] at hx
    rw [stChart_moveAlong]
    exact (hC x hx).sub continuousAt_const
  · rw [pieces_moveAlong] at hp
    rw [stRecL_moveAlong_true']
    exact hB p hp z hz hz0
  · rw [stRecL_moveAlong_true']
    exact h0

/-- **The end of a stage** (the mirror of `rInv_tail` for `LW`): a rightward boundary continuation from the right
record to the next restart mark keeps the left-side invariant for the recentred word. -/
theorem lw_tail (hb : IsPiecewiseConstantBoundaryData b jumps) {γ : BoundaryWord} {s₁ s₂ : ExplState}
    (hs₁ : RProf s₁) (hO : ROrig b jumps γ s₁) (hI : LW κ θ b jumps γ s₁) (hpt : stPt s₁ = stRecR s₁)
    (hang : stAngle s₁ = θ) (hlow : rightLim b (stPt s₁) + θ * chiC κ ≤ -sleLambda κ)
    (he : s₂ = if hC : (restartSet κ b jumps s₁).Nonempty then
      ExplState.moveAlong s₁ true ((restartSet κ b jumps s₁).min' hC) true else ExplState.moveToEnd s₁ true)
    (hst : ∃ r, stStatus s₂ = .inr (.inr (.inr (.inl (r, true))))) :
    LW κ θ b jumps (BoundaryWord.shiftW (rProf (stChart s₁) (stPt s₂)) γ) s₂ := by
  split_ifs at he with hC
  swap
  · exfalso
    obtain ⟨r, hr⟩ := hst
    rw [he] at hr
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    exact absurd hr (by simp [ExplState.moveToEnd, stStatus])
  subst he
  set w := (restartSet κ b jumps s₁).min' hC with hw
  have hmem := Finset.mem_filter.1 (Finset.min'_mem _ hC)
  have hpw : stPt s₁ < w := hmem.2.1
  have hlowc : ∀ x, stRecR s₁ < x → x < w → x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ := by
    intro x hx hxw hxJ
    rw [← hpt] at hx
    refine add_le_neg_of_connector hb hlow (fun z hz hqz hzw => ?_) hx hxw hxJ
    by_contra hgt
    push Not at hgt
    have hz' : z ∈ restartSet κ b jumps s₁ := Finset.mem_filter.2 ⟨hz, hqz, by rw [hang]; exact hgt⟩
    exact absurd ((restartSet κ b jumps s₁).min'_le z hz') (not_le.2 hzw)
  rw [stPt_moveAlong]
  exact lw_moveAlong hs₁ hO hI (by rw [← hpt]; exact hpw) hlowc

/-- **The left-side invariant at the root** (the original word, the identity chart, no pieces; the low side is
vacuous). -/
theorem lw_root {c₀ : BoundaryWord} (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    LW κ θ b jumps (BoundaryWord.shiftW 0 c₀) (ExplState.init 0) := by
  have hprof : rProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [rProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hlprof : lProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    rw [lProf_eq, hprof, neg_neg]
  have hL0 : stRecL (ExplState.init 0) = 0 := rfl
  refine ⟨⟨?_, fun x hx => ?_⟩, fun x hx hxJ hzJ => ?_, fun y hy _ hyR => ?_, fun x _ => ?_,
    fun p hp => ?_, le_of_eq hL0⟩
  · rw [hlprof, hL0, neg_zero]
    exact ⟨strictMonoOn_id, continuousOn_id, fun M => ⟨max M 0 + 1, by positivity, by
      linarith [le_max_left M 0]⟩⟩
  · rw [hlprof]; rw [hL0, neg_zero] at hx; exact hx
  · rw [hprof, BoundaryWord.fn_shiftW, add_zero]
    exact hc₀ x hxJ
  · exfalso
    have := hyR (y / 2) (by rw [hL0]; linarith)
    rw [hprof] at this
    linarith
  · have hc : (stChart (ExplState.init 0)).1 = fun z => z - ((0 : ℝ) : ℂ) := by
      funext z
      simp [ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
    rw [hc]
    exact (continuous_id.sub continuous_const).continuousAt
  · exact absurd hp (by simp [ExplState.init])

end Bundle

/-! ### One stage of the right walk -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **One stage of the right walk keeps the left-side invariant** (the companion of `rInv_walk_step`, same
hypotheses, plus the left-side invariant at the launch `ℓ`, the conformality of the launch chart and the regularity
of the launched piece): the state at the next launch `k` has the invariant for the word
`shiftW a (stopWord κ (β, θ, record))` of `rInv_walk_step`. -/
theorem lw_walk_step (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {ℓ k : ℕ}
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
        -sleLambda κ)
    (hLW : LW κ θ b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hcc : (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)).IsConformal)
    (hP : (D ℓ).2 ≠ ⊤ → GW1P.PieceRegular (D ℓ).1 (D ℓ).2) :
    LW κ θ b jumps (BoundaryWord.shiftW (rProf (stChart (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ true) D (ℓ + 1))) (stPt (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ true) D k))) (stopWord κ (β, θ, recOf ⊤ (D ℓ))))
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) := by
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D with hRdef
  obtain ⟨-, hrunk, r, hstk⟩ := run_eq_of_last_launch hℓk hk hl hn
  have hrun1 : R (ℓ + 1) = ExplState.launch (R ℓ) ℓ (D ℓ) θ ⊤ := launch_walk hl
  have hstk' : ∃ r, stStatus (R k) = .inr (.inr (.inr (.inl (r, true)))) := ⟨r, hstk⟩
  by_cases htop : (D ℓ).2 = ⊤
  · exfalso
    have hmin : min ⊤ (D ℓ).2 = ⊤ := by rw [htop]; rfl
    have hd := (launch_eq_of_top (R ℓ) ℓ (D ℓ) θ ⊤ hmin).2.2.2.2.1
    rw [← hrun1] at hd
    have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) true (Or.inr (Or.inl hd))
    rw [← hrunk] at this
    rw [this, hd] at hstk
    exact absurd hstk (by simp [stArcM])
  have hLW1 : LW κ θ b jumps (stopWord κ (β, θ, recOf ⊤ (D ℓ))) (R (ℓ + 1)) := by
    rw [hrun1]
    exact lw_launch hκ hb hI.2.1.1 hcc hLW ℓ hreg (hgood htop) htop (hP htop)
  by_cases h0 : (D ℓ).2 = 0
  · have hnt : stStatus (R ℓ) ≠ .inr (.inl ()) := by
      rcases hR.1 with h | h <;> rw [h] <;> simp
    obtain ⟨hst1, hpt1, hang1⟩ := launch_zero (k := ℓ) (θ := θ) h0 hnt
    rw [← hrun1] at hst1 hpt1 hang1
    rcases hR.1 with hroot' | harc
    · have hL0 := hroot hroot'
      by_cases hlow : rightLim b (stPt (R (ℓ + 1))) + θ * chiC κ ≤ -sleLambda κ
      · have hc := contStep_thr_none_right (κ := κ) b jumps (R (ℓ + 1)) hst1 (by rw [hang1]; exact hlow)
        rw [← hrunk] at hc
        obtain ⟨hs₁, hrel⟩ := rProf_launch_zero hI.2.1 ℓ θ hreg h0
        rw [← hrun1] at hs₁ hrel
        have hO := rOrig_of_rel hκ hb (s₁ := R (ℓ + 1)) hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩
        have hRR : stRecR (R (ℓ + 1)) = stRecR (R ℓ) := by
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
        exact lw_tail hb hs₁ hO hLW1 hpt hang1 hlow hc hstk'
      · exfalso
        have hd := contStep_thr_none_dead (κ := κ) b jumps (R (ℓ + 1)) hst1
          (by rw [hpt1, hang1]; exact hL0) (by rw [hang1]; exact lt_of_not_ge hlow) true
        rw [← hrunk, hstk] at hd
        exact absurd hd (by simp [stArcM, stDead])
    · exfalso
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
  · have hcases := launch_status_of_pos (s := R ℓ) (k := ℓ) (θ := θ) htop h0
    rw [← hrun1] at hcases
    rcases hcases with hthr | hthr | hthr
    · obtain ⟨-, hhit, hpt, hang⟩ := launch_thr_true (s := R ℓ) (k := ℓ) (θ := θ) htop (by rw [← hrun1]; exact hthr)
      rw [← hrun1] at hpt hang
      obtain ⟨hs₁, hrel⟩ := rProf_launch hI.2.1 ℓ θ hreg (hgood htop) htop hhit
      rw [← hrun1] at hs₁ hrel
      have hO := rOrig_of_rel hκ hb (s₁ := R (ℓ + 1)) hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩
      have hc := contStep_thr_true' (κ := κ) b jumps (R (ℓ + 1)) hthr
      rw [← hrunk] at hc
      exact lw_tail hb hs₁ hO hLW1 hpt hang (by rw [hpt]; exact hF2 hthr) hc hstk'
    · exact absurd hthr hnoL
    · exfalso
      have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) true (Or.inr (Or.inr hthr))
      rw [← hrunk] at this
      rw [this, hthr] at hstk
      exact absurd hstk (by simp [stArcM, stDead])

end Stage

end InteractingSLE.Theorem14.GW1W
