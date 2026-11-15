/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PathLeftLow
import InteractingSLE.Spec.Supplement.GW1PathReduce

/-!
# GW1's retargeting for the left walk, and the reduction of `RetargetPathStatement`

Packet PROVE-GW1-PATH. The left mirrors of `GW1PathWitness` and `GW1PathKernel`:

* `exists_post_witness_left_prof`, **`ae_post_high_left`**: almost surely at a next launch of the left walk,
  `v = postShift < 0` and the post-piece word is high on `(v, 0)` (`λ ≤ γ(y) + (π/2)χ`);
* **`ae_kernel_retarget_left`**: the kernel identification of `U` with `Q` retargeted at `v` (Corollary BR4a under the
  conditional law, BR6 by reflection, Theorem 1.2's determination);
* **`retargetPathStatement_of_det`**: `GW1Laws.RetargetPathStatement` from Corollary BR4a, Theorems 1.2 (R44 form)
  and 1.3, and the two deterministic statements `DetRetargetStatement` and `ConnectorPhysStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Path

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData GW1W GW1WalkExit GW1Laws
  GW1RestartPair

section Witness

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The next-launch word of the left walk is the recentred stop word**, with the left profile and the
original-word property of the post-piece state (the construction of `GW1Laws.exists_post_witness_left`). -/
theorem exists_post_witness_left_prof (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (Real.pi / 2) false) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hambL : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hambR : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + Real.pi / 2 * chiC κ) (n : ℕ) :
    ∃ (βk : Ω → BoundaryWord) (Yk : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps (Real.pi / 2) false) E (2 * (n + 1)) βk Yk ∧
      ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
          (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
          (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
        ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
          βk ω = BoundaryWord.shiftW
            (postShift κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω) n) γ ∧
          LProf (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
            (2 * n + 1)) ∧
          LOrig b jumps γ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun j => E j ω) (2 * n + 1)) := by
  set θ : ℝ := Real.pi / 2 with hθ
  set spec := boundaryWalkSpec b jumps θ false with hspec
  have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E ℓ β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        LInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        LReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
          -sleLambda κ < rightLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ) :=
    fun ℓ => exists_witness_left hκ hb hh hE hreg hambR ℓ
  choose β Y hW hI using H
  obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    (k := 2 * (n + 1)) (by omega) (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y
    fun ℓ _ => hW ℓ
  refine ⟨βk, Yk, hWk, ?_⟩
  filter_upwards [hI (2 * n), ae_stage_left hκ hb hh hE hreg (hW (2 * n)) ((hI (2 * n)).mono fun ω hω hl => (hω hl).1)]
    with ω hIω hst hlk hl
  have hn : ∀ j, 2 * n < j → j < 2 * (n + 1) →
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none := by
    intro j hj1 hj2
    have hj : j = 2 * n + 1 := by omega
    subst hj
    exact GW1RestartPair.noLaunch_walk_odd _ n
  have hβ := hexpl (2 * n) ω (by omega) hlk hl hn
  rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl] at hβ
  obtain ⟨hinv, -, -⟩ := hIω hl
  obtain ⟨hnoR, hgood, -⟩ := hst hl
  obtain ⟨hfin, hcase⟩ := post_case (D := fun j => E j ω) true hl hlk hnoR
  have hrun1 := launch_walk (D := fun j => E j ω) hl
  rw [hrun1] at hcase
  obtain ⟨hP, hO⟩ := post_lProf_lOrig hκ hb hinv (hreg (2 * n) ω) hgood hfin hcase
  have h0 : stRecL (ExplState.launch (ExplState.run κ b jumps spec (fun j => E j ω) (2 * n)) (2 * n)
      (E (2 * n) ω) θ ⊤) ≤ 0 := by
    rw [← hrun1]
    exact stRecL_run_nonpos κ b jumps spec _ le_rfl _
  refine ⟨stopWord κ (β (2 * n) ω, θ, recOf ⊤ (E (2 * n) ω)), ⟨isSorted_stopWord κ _,
    fn_bound_neg_of_lOrig hP hO h0 hambL, fun y hy _ => stopWord_fn_add_gt_of_pos hκ hinv.1 _ hy⟩, ?_,
    by rw [hrun1]; exact hP, by rw [hrun1]; exact hO⟩
  rw [hβ]
  rfl

end Witness

section High

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The post-piece word is high on the connector** (left walk): almost surely at a next launch, `v = postShift` is
negative and `postWord` is high on `(v, 0)` at angle `π/2`. -/
theorem ae_post_high_left (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hstages : ∀ᵐ ω ∂P, WalkStageData κ b jumps (Real.pi / 2) false (fun j => E j ω)) (n : ℕ)
    {βk : Ω → BoundaryWord}
    (hgood : ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
          (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
          (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
        ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
          βk ω = BoundaryWord.shiftW
            (postShift κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω) n) γ ∧
          LProf (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
            (2 * n + 1)) ∧
          LOrig b jumps γ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun j => E j ω) (2 * n + 1)))
    (hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      postShift κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω) n < 0 ∧
      ∀ y, postShift κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω) n < y → y < 0 →
        y ∉ (postWord κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) E n βk ω).jumps →
        sleLambda κ ≤ (postWord κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) E n βk ω).fn y +
          Real.pi / 2 * chiC κ := by
  set θ : ℝ := Real.pi / 2 with hθ
  set spec := boundaryWalkSpec b jumps θ false with hspec
  filter_upwards [hgood, hprev, hstages] with ω hg hp hs hlk
  have hl := hp hlk
  obtain ⟨γ, -, hβk, hP, hO⟩ := hg hlk hl
  set R := ExplState.run κ b jumps spec (fun j => E j ω) with hRdef
  obtain ⟨hprof, hready, hgd, hC⟩ := hs (2 * n) hl
  change OwnProfile false (R (2 * n)) at hprof
  change OwnReady false (R (2 * n)) at hready
  change ClassifiedExit κ b false (R (2 * n)) (R (2 * n + 1)) at hC
  have hrun1 : R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (E (2 * n) ω) θ ⊤ := launch_walk hl
  have hnoR : stStatus (R (2 * n + 1)) ≠ stThr (some true) := by
    intro hbad
    rcases hC.1 with hd | ⟨-, ho⟩
    · rw [hbad] at hd; exact absurd hd (by simp)
    · rcases ho with he | ⟨he, -⟩ <;> rw [hbad] at he <;> exact absurd he (by simp)
  obtain ⟨hfin, -⟩ := post_case (D := fun j => E j ω) true hl hlk hnoR
  have hgd' : LocalExt.IsDrvGood (recHist (recOf ⊤ (E (2 * n) ω))) := hgd hfin
  rw [hrun1] at hC
  obtain ⟨-, hpt⟩ := profile_point_of_finite_classified hprof hready (2 * n) (hreg (2 * n) ω) hgd' hfin hC
  rw [← hrun1] at hC hpt
  have hpt' : stPt (R (2 * n + 1)) = stRecL (R (2 * n + 1)) := by
    simp only [GW1WalkFinish.sideCoord, outwardRecord, Bool.false_eq_true, ↓reduceIte, neg_inj] at hpt
    exact hpt
  have hang : stAngle (R (2 * n + 1)) = θ := by rw [hrun1]; exact angle_launch _ _ _ _
  obtain ⟨hwq, hhighx, hchart, -⟩ := connector_left hb hl hlk hC hang
  set w := stPt (R (2 * (n + 1))) with hw
  have hv : postShift κ b jumps spec (fun j => E j ω) n = rProf (stChart (R (2 * n + 1))) w := by
    unfold postShift
    change ((stChart (R (2 * n + 1))).1 0 - (stChart (R (2 * (n + 1)))).1 0).re = _
    change stChart (R (2 * (n + 1))) =
      (stChart (R (2 * n + 1))).recenter (rProf (stChart (R (2 * n + 1))) w) at hchart
    rw [hchart]
    simp only [InteractingSLE.Chart.recenter, rProf, Complex.sub_re, Complex.ofReal_re]
    ring
  have hwr : w < stRecL (R (2 * n + 1)) := by rw [← hpt']; exact hwq
  have hneg : rProf (stChart (R (2 * n + 1))) w < 0 := by
    have h1 : 0 < lProf (stChart (R (2 * n + 1))) (-w) := hP.2.2.1 (-w) (by linarith)
    rw [GW1W.lProf_eq, neg_neg] at h1
    linarith
  have hpw : postWord κ b jumps spec E n βk ω = γ := by
    unfold postWord
    rw [hβk, shiftW_neg_shiftW]
  refine ⟨hv ▸ hneg, fun y hvy hy hyJ => ?_⟩
  rw [hpw] at hyJ ⊢
  rw [hv] at hvy
  refine fn_high_of_lOrig hP hO hwr (fun x hx hxq hxJ => ?_) y hvy hy hyJ
  exact hhighx x hx (by rw [hpt']; exact hxq) hxJ

end High

section Retarget

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Retargeting inside the conditional pair (left walk).** For almost every `ω₀` at a next launch, the recentring
amount `v = postShift ω₀` is negative and, under the regular conditional law given `pastSigma (2n+1)`, almost surely
the terminal relative driver `Q` visits `v` and the next-launch driver `U` is `Q` retargeted at `v` (Corollary BR4a
under the conditional law, the retargeted driver identified with `U` by Theorem 1.2's determination). -/
theorem ae_kernel_retarget_left (hBR4a : BR4a.BR4aStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E false n V ζV ℓ)
    {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞} {β : Ω → ℝ≥0 → ℝ≥0}
    (hQ : IsTerminalRestart κ b jumps P h false (E (GW1Z.walkSpec b jumps false)) n V Q ζQ β)
    {U : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hU : IsForcedRetargetCond κ b jumps P h false (E (GW1Z.walkSpec b jumps false)) n U ζ) :
    ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps false) (fun j => E (GW1Z.walkSpec b jumps false) j ω₀)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      postShift κ b jumps (GW1Z.walkSpec b jumps false) (fun j => E (GW1Z.walkSpec b jumps false) j ω₀) n < 0 ∧
      ∀ᵐ ω ∂(condExpKernel P
          (pastSigma κ b jumps (GW1Z.walkSpec b jumps false) (E (GW1Z.walkSpec b jumps false)) (2 * n + 1)) ω₀),
        ((postShift κ b jumps (GW1Z.walkSpec b jumps false) (fun j => E (GW1Z.walkSpec b jumps false) j ω₀) n : ℝ) :
            ℂ) ∈ infinitySourceChart.tipSet (fun t => Q t ω) ⊤ ∧
        IsRetargetOf (fun s => U s ω) (fun s => Q s ω)
          (postShift κ b jumps (GW1Z.walkSpec b jumps false) (fun j => E (GW1Z.walkSpec b jumps false) j ω₀) n) := by
  have hκ := hdata.pos
  have hκ4 := hdata.lt_four
  have hb := hdata.boundary
  have hh := hdata.field
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc false) false
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps false)
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀)
    hκ hκ4 hb hh hdata.counterflow hdata.complete
  obtain ⟨βk, Yk, hW, hgood⟩ := exists_post_witness_left_prof hκ hb hh hE hreg hambL hambR n
  have hstages : ∀ᵐ ω ∂P, WalkStageData κ b jumps (Real.pi / 2) false
      (fun j => E (GW1Z.walkSpec b jumps false) j ω) := by
    filter_upwards [hdata.stages] with ω hω
    simpa only [Bool.false_eq_true, ↓reduceIte] using hω
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps false) (fun j => E (GW1Z.walkSpec b jumps false) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps false) (fun j => E (GW1Z.walkSpec b jumps false) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hstages, hdata.pieces _ hprog] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  have hgood' : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps false) (fun j => E (GW1Z.walkSpec b jumps false) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps false) (fun j => E (GW1Z.walkSpec b jumps false) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
        βk ω = BoundaryWord.shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps false)
          (fun j => E (GW1Z.walkSpec b jumps false) j ω) n) γ := by
    filter_upwards [hgood] with ω hω hlk hl
    obtain ⟨γ, hγ, hβ, -, -⟩ := hω hlk hl
    exact ⟨γ, hγ, hβ⟩
  have hK := ae_terminal_kernel hb hE hreg hW hgood' hprev
  have hLow := ae_post_high_left (P := P) hb hreg hstages n hgood hprev
  have hker : ∀ ω, condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps false)
        (E (GW1Z.walkSpec b jumps false)) (2 * (n + 1))) ω =
      condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps false)
        (E (GW1Z.walkSpec b jumps false)) (2 * n + 1)) ω :=
    condExpKernel_walk_connector (κ := κ) (b := b) (jumps := jumps) (θ := Real.pi / 2) (right := false) P _ n
  filter_upwards [hK, hLow, hQ.conditional, hU.2, hprev] with ω₀ hk hlow hq hu hpv hlk
  obtain ⟨hgw, hgff, -, hconf, hlift, htrans⟩ := hk hlk
  obtain ⟨hv0, hlowv⟩ := hlow hlk
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
  -- the field read in the post-piece chart, exactly
  have hh' : ∀ ω, IsChartTransport (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps false)
      (fun j => E (GW1Z.walkSpec b jumps false) j ω₀) (2 * n + 1))) 1 0 (chiC κ) (h ω)
      (Chart.chartTransport hconf 1 0 (chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'm : Measurable fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) :=
    (Chart.measurable_chartTransport _ _ _ _).comp hh.1
  have hgffμ := isGFFWithBoundaryData_congr_ae hgff hh'm (htrans _ hh')
  rw [hker ω₀] at hgffμ
  obtain ⟨hQcf, hQζ⟩ := hq hlk _ hh'
  have hvis := ae_visit_of_high_neg hT13 hT13₀ hκ hκ4 hgffμ hQcf hQζ hv0 hlowv
  obtain ⟨hv, Wv, ζv, ℓv, hvtr, hvcf, -, hvae⟩ :=
    hBR4a κ hκ hκ4 _ _ (postWord κ b jumps (GW1Z.walkSpec b jumps false) (E (GW1Z.walkSpec b jumps false)) n βk
      ω₀).isPiecewiseConstantBoundaryData _ _ hgffμ Q ζQ hQcf hQζ _ hv0.ne hvis
  -- the next launch chart is the post-piece chart recentred at `v`
  have hc := launchChart_next_eq (hpv hlk) hcθ
  have htrc : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hv ω) := by
    intro ω
    have h1 := IsChartTransport.trans hconf (isConformal_shiftChart _) hlift (continuousOn_shiftChart_lift _)
      (hh' ω) (hvtr ω)
    rw [hc, Chart.recenter_eq_trans]
    exact h1
  obtain ⟨hUcf, hUζ⟩ := hu c θ hcθ hv htrc
  -- determination: `U` is the retargeted driver
  have hvgff : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps false)
      (E (GW1Z.walkSpec b jumps false)) (2 * n + 1)) ω₀) hv
      (BoundaryWord.shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps false)
        (fun j => E (GW1Z.walkSpec b jumps false) j ω₀) n)
        (postWord κ b jumps (GW1Z.walkSpec b jumps false) (E (GW1Z.walkSpec b jumps false)) n βk ω₀)).fn
      (BoundaryWord.shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps false)
        (fun j => E (GW1Z.walkSpec b jumps false) j ω₀) n)
        (postWord κ b jumps (GW1Z.walkSpec b jumps false) (E (GW1Z.walkSpec b jumps false)) n βk ω₀)).jumps := by
    have h1 := isGFFWithBoundaryData_shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps false)
      (fun j => E (GW1Z.walkSpec b jumps false) j ω₀) n) hgffμ
    have e : (fun ω => flowField (postShift κ b jumps (GW1Z.walkSpec b jumps false)
        (fun j => E (GW1Z.walkSpec b jumps false) j ω₀) n) 0
          (Chart.chartTransport hconf 1 0 (chiC κ) (h ω))) = hv :=
      funext fun ω => (isChartTransport_shiftChart _ (chiC κ) _).unique (isConformal_shiftChart _) (hvtr ω)
    rw [e] at h1
    exact h1
  have hdet := GW4Ident.ae_eq_of_isCenteredCounterflowDriver h12p hT13 hκ
    (BoundaryWord.isPiecewiseConstantBoundaryData _) hvgff hUcf hUζ hvcf (hvae.mono fun ω hω => hω.1)
  -- the retargeted driver has a transient trace (Theorem 1.3)
  obtain ⟨bv, Jv, hv'', -, -, hvfl⟩ := hvcf
  have hvtrace := GW2aSingle.ae_chosenTrace hT13 (show (0 : ℝ) < 16 / κ by positivity) hvfl
  refine ⟨hv0, ?_⟩
  filter_upwards [hvis, hvae, hdet, hvtrace] with ω hvisω hvω hdω htω
  obtain ⟨hζv, hc1, hc2, hc3, hc4⟩ := hvω
  rw [hζv] at htω
  refine ⟨hvisω, ⟨GW2aSingle.chosenTrace Wv ζv ω, ?_, ?_⟩, ℓv ω, hc1, hc2, hc3, fun r z => ?_⟩
  · rw [hdω]
    exact htω.1
  · exact htω.2 rfl
  · rw [hdω]
    exact hc4 r z

/-- **GW1's forced retargeting, pathwise half, for the left walk** from Corollary BR4a (`BR4a.BR4aStatement`, an
existing Theorem 1.4 leaf), Theorems 1.2 (R44 form) and 1.3, and the two deterministic statements: the body of
`GW1Laws.RetargetPathStatement` at `right = false`. -/
theorem retargetPath_left_of_det (hBR4a : BR4a.BR4aStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hDet : DetRetargetStatement) (hPhys : ConnectorPhysStatement)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E false n V ζV ℓ)
    {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞} {β : Ω → ℝ≥0 → ℝ≥0}
    (hQ : IsTerminalRestart κ b jumps P h false (E (GW1Z.walkSpec b jumps false)) n V Q ζQ β)
    {U : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hU : IsForcedRetargetCond κ b jumps P h false (E (GW1Z.walkSpec b jumps false)) n U ζ)
    (hUreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps false)
        (fun j => E (GW1Z.walkSpec b jumps false) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0) :
    ∃ a : Ω → ℝ≥0 → ℝ≥0,
      IsForcedRetargetPath κ b jumps P false (E (GW1Z.walkSpec b jumps false)) n Q U ζ a :=
  forcedRetargetPath_of_kernel hDet hPhys hdata hQ hU.1 hUreg
    ((ae_kernel_retarget_left hBR4a h12p hT13 hT13₀ hdata hQ hU).mono fun _ hk hl =>
      ⟨(hk hl).1.ne, (hk hl).2⟩)

end Retarget

/-- **`GW1Laws.RetargetPathStatement` from Corollary BR4a and the two deterministic statements** (with Theorems 1.2
(R44 form) and 1.3): the probabilistic content of BW2–BR4a in the retained conditional pair is Corollary BR4a under the
conditional law (`ae_kernel_retarget_right`, `ae_kernel_retarget_left`); the rest is deterministic Loewner and walk
geometry (`DetRetargetStatement`, `ConnectorPhysStatement`). -/
theorem retargetPathStatement_of_det (hBR4a : BR4a.BR4aStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hDet : DetRetargetStatement) (hPhys : ConnectorPhysStatement) :
    RetargetPathStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h W' ζ' E right n V ζV ℓ hdata Q ζQ β hQ U ζ hU _ hUreg
  cases right
  · exact retargetPath_left_of_det hBR4a h12p hT13 hT13₀ hDet hPhys hdata hQ hU hUreg
  · exact retargetPath_right_of_det hBR4a h12p hT13 hT13₀ hDet hPhys hdata hQ hU hUreg

/-- **GW1's finite retargeting law** (`GW1RestartPair.FiniteRetargetLawStatement`) from Corollary BR4a, Theorems 1.2
(R44 form) and 1.3, and the two deterministic statements. -/
theorem finiteRetargetLawStatement_of_det (hBR4a : BR4a.BR4aStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hDet : DetRetargetStatement) (hPhys : ConnectorPhysStatement) :
    FiniteRetargetLawStatement.{u} :=
  finiteRetargetLawStatement_of_path h12p hT13 hT13₀
    (retargetPathStatement_of_det hBR4a h12p hT13 hT13₀ hDet hPhys)

end InteractingSLE.Theorem14.GW1Path
