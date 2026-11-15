/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1TermStatement

/-!
# BW1 at a walk launch: the restarted one-instruction history

Packet PROVE-BW1.

* `rProf_init`, `lProf_init`: the root state has both real profiles;
* **`exists_endsAtThresholdSide`**: if a launch of a walk ends at a threshold on the walk's side, the same piece,
  launched from the root, ends at a threshold (on some side) — the hit real point of the original launch is a hit real
  point of the restarted one, read through the launch chart's profile;
* **`isStagedHistory_termSpec`**: a measurable regular flow-line driver of a field (angle `θ`, any piecewise-constant
  data) is a one-instruction staged history of that field for the program `termSpec θ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Term

open Exist Exist.StagedLaw Exist.Staged GW1RestartPair

/-! ### The root state -/

theorem rProf_init : GW1W.RProf (ExplState.init 0) := by
  have hr : ∀ x : ℝ, rProf (stChart (ExplState.init 0)) x = x := fun x => by
    simp [rProf, stChart, ExplState.init, Chart.recenter, Chart.id]
  have hrec : stRecR (ExplState.init 0) = 0 := rfl
  refine ⟨fun x => ?_, ⟨?_, ?_, fun M => ⟨max M 0 + 1, ?_, ?_⟩⟩, fun x hx => ?_, fun ε hε => ⟨ε / 2, ?_, ?_⟩⟩
  · simp [stChart, ExplState.init, Chart.recenter, Chart.id]
  · intro x _ y _ hxy
    rw [hr, hr]
    exact hxy
  · exact (continuous_id.congr fun x => (hr x).symm).continuousOn
  · rw [hrec]
    positivity
  · rw [hr]
    linarith [le_max_left M 0]
  · rw [hr]
    rw [hrec] at hx
    exact hx
  · rw [hrec]
    positivity
  · rw [hr]
    linarith

theorem lProf_init : GW1W.LProf (ExplState.init 0) := by
  have hr : ∀ x : ℝ, lProf (stChart (ExplState.init 0)) x = x := fun x => by
    simp [lProf, stChart, ExplState.init, Chart.recenter, Chart.id]
  have hrec : -stRecL (ExplState.init 0) = 0 := by simp [stRecL, ExplState.init]
  refine ⟨fun x => ?_, ⟨?_, ?_, fun M => ⟨max M 0 + 1, ?_, ?_⟩⟩, fun x hx => ?_, fun ε hε => ⟨ε / 2, ?_, ?_⟩⟩
  · simp [stChart, ExplState.init, Chart.recenter, Chart.id]
  · intro x _ y _ hxy
    rw [hr, hr]
    exact hxy
  · exact (continuous_id.congr fun x => (hr x).symm).continuousOn
  · rw [hrec]
    positivity
  · rw [hr]
    linarith [le_max_left M 0]
  · rw [hr]
    rw [hrec] at hx
    exact hx
  · rw [hrec]
    positivity
  · rw [hr]
    linarith

/-! ### The threshold of the restarted launch -/

/-- **A threshold of a walk launch is a threshold of the restarted launch.** For a state with the walk's own profile
(`RProf` for the right walk, `LProf` for the left one), if the launch of a piece of finite lifetime ends at a
threshold on the walk's side, the same piece launched from the root ends at a threshold. -/
theorem exists_endsAtThresholdSide {s : ExplState} {k : ℕ} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ θ' : ℝ} (right : Bool)
    (hs : GW1WalkExit.OwnProfile right s) (hfin : D.2 ≠ ⊤)
    (h : stStatus (ExplState.launch s k D θ ⊤) = stThr (some right)) :
    ∃ r : Bool, BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 D θ' ⊤) r := by
  cases right
  · -- the left walk
    have hL : GW1W.LProf s := by simpa [GW1WalkExit.OwnProfile] using hs
    obtain ⟨h0, ⟨x, hx, hhit⟩, -⟩ := GW1W.launch_thr_false hfin h
    have hh := (lHit_iff hL.1 ⊤ D x).1 hhit
    have hneg : rProf (stChart s) x < 0 := by
      have h1 := hL.2.2.1 (-x) (by linarith)
      rw [GW1W.lProf_eq, neg_neg] at h1
      linarith
    by_cases hR : stStatus (ExplState.launch (ExplState.init 0) 0 D θ' ⊤) = stThr (some true)
    · exact ⟨true, hR⟩
    · exact ⟨false, GW1WalkExit.launch_thr_false_of_hit lProf_init 0 θ' hfin h0 hR
        ⟨rProf (stChart s) x, hneg, hh.1, hh.2⟩⟩
  · -- the right walk
    have hR : GW1W.RProf s := by simpa [GW1WalkExit.OwnProfile] using hs
    obtain ⟨h0, ⟨x, hx, hhit⟩, -⟩ := GW1W.launch_thr_true hfin h
    have hh := (lHit_iff hR.1 ⊤ D x).1 hhit
    exact ⟨true, GW1WalkExit.launch_thr_true_of_hit rProf_init 0 θ' hfin h0
      ⟨rProf (stChart s) x, hR.2.2.1 x hx, hh.1, hh.2⟩⟩

/-! ### The one-instruction staged history -/

section Staged

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The restarted program has no launch after its single instruction. -/
theorem launches_termSpec_of_pos (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    {k : ℕ} (hk : 1 ≤ k) : (ExplState.run κ b jumps (termSpec θ) D (k + 1)).2.2.2.1 k = none :=
  GW2Sched.launches_run_succ_of_length_le κ b jumps (termSpec θ) D (by simpa [termSpec] using hk)

/-- The launch record of the restarted instruction. -/
theorem launches_termSpec_zero (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (termSpec θ) D 1).2.2.2.1 0 = some (Chart.id.recenter 0, θ) := by
  rw [run_termSpec_one, launches_launch, Function.update_self]
  rfl

/-- **A measurable regular flow-line driver is a one-instruction staged history.** -/
theorem isStagedHistory_termSpec {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J')
    {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hem : Measurable e) (hreg : ∀ ω, IsRegularDriver (e ω))
    (hfl : IsFlowLineDriver κ b' J' θ Q h (fun t ω => (e ω).1 t) (fun ω => (e ω).2)) :
    IsStagedHistory κ b J Q h (termSpec θ) (fun _ => e) := by
  have hpm := measurable_pastMap (κ := κ) runMeasStatement hb (termSpec θ) (E := fun _ => e)
    (k := 0) (fun _ _ => hem) (fun _ _ => hreg)
  refine ⟨fun _ => hem, fun k => ?_, fun _ => Eventually.of_forall fun ω => (hreg ω).2.2.2, fun k => ?_⟩
  · rw [pastSigma_eq_comap]
    exact (measurable_pastMap (κ := κ) runMeasStatement hb (termSpec θ) (E := fun _ => e) (k := k)
      (fun _ _ => hem) (fun _ _ => hreg) k le_rfl).comap_le
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine Eventually.of_forall fun ω₀ c θ' hl => ?_
      rw [launches_termSpec_zero] at hl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
      refine ⟨b', J', h, hb', fun ω => ?_, ?_⟩
      · rw [Chart.recenter_zero]
        exact isChartTransport_id _ _
      · rw [GW1.pastSigma_zero_eq_bot, GW1.condExpKernel_bot_apply]
        exact hfl
    · refine Eventually.of_forall fun ω₀ c θ' hl => ?_
      rw [launches_termSpec_of_pos κ b J θ _ hk] at hl
      exact absurd hl (by simp)

end Staged

/-! ### Congruence of a launch in the record of its piece -/

/-- **The status of a launch depends on its driver only through the stopped driver and the lifetime.** -/
theorem stStatus_launch_congr {s : ExplState} {k : ℕ} {θ : ℝ} {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h1 : (retOf ⊤ e).1 = (retOf ⊤ e').1) (h2 : e.2 = e'.2) :
    stStatus (ExplState.launch s k e θ ⊤) = stStatus (ExplState.launch s k e' θ ⊤) := by
  by_cases htop : e.2 = ⊤
  · have hm : min ⊤ e.2 = ⊤ := by rw [htop]; rfl
    have hm' : min ⊤ e'.2 = ⊤ := by rw [← h2, htop]; rfl
    rw [(launch_eq_of_top s k e θ ⊤ hm).2.2.2.2.1, (launch_eq_of_top s k e' θ ⊤ hm').2.2.2.2.1]
  · have hm : min ⊤ e.2 ≠ ⊤ := GW1W.min_top_ne_top htop
    have hm' : min ⊤ e'.2 ≠ ⊤ := GW1W.min_top_ne_top (h2 ▸ htop)
    rw [(launch_eq_of_ne_top s k e θ ⊤ hm).2.2.2.2.1, (launch_eq_of_ne_top s k e' θ ⊤ hm').2.2.2.2.1]
    have hd : stopDrv ⊤ e = stopDrv ⊤ e' := by
      funext x
      simp only [stopDrv, h1]
    have ht : stopTime ⊤ e = stopTime ⊤ e' := by simp only [stopTime, h2]
    unfold lStatus lHit lAlive
    rw [hd, ht, h2]

/-- The rational times are dense in `ℝ≥0`. -/
theorem denseRange_toNNReal_rat : DenseRange (fun q : ℚ => Real.toNNReal q) :=
  (Function.Surjective.denseRange (fun x : ℝ≥0 => ⟨(x : ℝ), Real.toNNReal_coe⟩)).comp Rat.denseRange_cast
    continuous_real_toNNReal

/-- The stopped driver of a regular piece is continuous. -/
theorem continuous_retOf {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : GW1P.PieceRegular e.1 (min ⊤ e.2)) :
    Continuous (retOf ⊤ e).1 := by
  have h := (GW1P.PieceRegular.continuous_stoppedReal he).1.comp NNReal.continuous_coe
  refine h.congr fun r => ?_
  simp only [Function.comp_apply, Real.toNNReal_coe, retOf]

/-- **The record of a regular piece determines its stopped driver and its lifetime.** -/
theorem retOf_eq_of_recOf_eq {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : GW1P.PieceRegular e.1 (min ⊤ e.2))
    (he' : GW1P.PieceRegular e'.1 (min ⊤ e'.2)) (h : recOf ⊤ e = recOf ⊤ e') :
    (retOf ⊤ e).1 = (retOf ⊤ e').1 ∧ e.2 = e'.2 := by
  have h2 : e.2 = e'.2 := by
    have := congrArg (fun r : RecData => r.2.1) h
    simpa [recOf, readRec, retOf] using this
  refine ⟨?_, h2⟩
  have hq : ∀ q : ℚ, (retOf ⊤ e).1 (q : ℝ).toNNReal = (retOf ⊤ e').1 (q : ℝ).toNNReal := fun q => by
    have := congrFun (congrArg (fun r : RecData => r.1) h) q
    simpa only [recOf, readRec] using this
  exact (continuous_retOf he).ext_on denseRange_toNNReal_rat (continuous_retOf he')
    (by rintro _ ⟨q, rfl⟩; exact hq q)

/-- A launch ending at a threshold has a finite lifetime. -/
theorem ne_top_of_endsAtThresholdSide {s : ExplState} {k : ℕ} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} {r : Bool}
    (h : BW1.EndsAtThresholdSide (ExplState.launch s k e θ ⊤) r) : e.2 ≠ ⊤ := by
  intro htop
  have hmin : min ⊤ e.2 = ⊤ := by rw [htop]; rfl
  have hd := (launch_eq_of_top s k e θ ⊤ hmin).2.2.2.2.1
  unfold BW1.EndsAtThresholdSide at h
  have h' : stStatus (ExplState.launch s k e θ ⊤) = stThr (some r) := h
  rw [hd] at h'
  simp [stDone, stThr] at h'

/-! ### Proposition BW1 for the restarted piece -/

section BW1Apply

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Proposition BW1 for one flow-line piece of a field, in the launch coordinate.** For a GFF `hc` with
piecewise-constant data, its centred counterflow `V` with infinite lifetime and a measurable regular flow-line driver
`e` of angle `θ ∈ [−π/2, π/2]`: for each side `r` there is a driver `Wr` which, under the regular conditional law
given the record of the piece, on the event that the restarted piece ends at a threshold on the side `r`, is the
centred counterflow of the field read in `termChart`, and which is almost surely there the relative counterflow of
`V` after the piece, with infinite lifetime. -/
theorem bw1_termRel (hBW1 : BW1.BW1Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b' : ℝ → ℝ}
    {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J') {Q₀ : Measure Ω} [IsProbabilityMeasure Q₀]
    {hc : Ω → DistOn upperHalfPlaneOpens} (hgff : IsGFFWithBoundaryData Q₀ hc b' J')
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ Q₀ hc V ζV)
    (hζ : ∀ᵐ ω ∂Q₀, ζV ω = ⊤) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hem : Measurable e) (hreg : ∀ ω, IsRegularDriver (e ω))
    (hfl : IsFlowLineDriver κ b' J' θ Q₀ hc (fun t ω => (e ω).1 t) (fun ω => (e ω).2)) (r : Bool) :
    ∃ (Wr : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      (∀ᵐ ω₁ ∂Q₀, BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 (e ω₁) θ ⊤) r →
        ∃ h'' : Ω → DistOn upperHalfPlaneOpens,
          (∀ ω, IsChartTransport (termChart (e ω₁)) 1 0 (QuantumZipper.chiC κ) (hc ω) (h'' ω)) ∧
          IsCenteredCounterflowDriver κ (condExpKernel Q₀ (pastSigma κ b' J' (termSpec θ) (fun _ => e) 1) ω₁)
            h'' Wr ζr) ∧
      ∀ᵐ ω ∂Q₀, BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 (e ω) θ ⊤) r →
        ζr ω = ⊤ ∧ IsTermRelOf (fun t => Wr t ω) (fun t => V t ω) (e ω) := by
  have hst := isStagedHistory_termSpec (κ := κ) hb' hb' hem hreg hfl
  obtain ⟨Wr, ζr, ℓ, hcond, -, hpath⟩ :=
    hBW1 κ hκ hκ4 b' J' hb' Q₀ hc hgff V ζV hcf hζ θ hθ ⊤ false [] (fun _ => e) hst r
  refine ⟨Wr, ζr, ?_, ?_⟩
  · filter_upwards [hcond] with ω₁ hω hev
    obtain ⟨h'', htr, hcd⟩ := hω hev
    refine ⟨h'', fun ω => ?_, hcd⟩
    have := htr ω
    rwa [stateChart_run_termSpec κ b' J' θ (fun _ => e ω₁) (ne_top_of_endsAtThresholdSide hev)] at this
  · filter_upwards [hpath] with ω hω hev
    obtain ⟨hζr, -, -, hc1, hc2, hrange, htip⟩ := hω hev
    refine ⟨hζr, ℓ ω, hc1, hc2, ?_, fun s z => ?_⟩
    · rw [hrange]
      have := prefixPhysSet_termSpec κ b' J' θ (fun _ => e ω)
      exact congrArg (fun A => {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart (fun t => V t ω) A}) this
    · have := htip s z
      rwa [stateChart_run_termSpec κ b' J' θ (fun _ => e ω) (ne_top_of_endsAtThresholdSide hev)] at this

end BW1Apply

end InteractingSLE.Theorem14.BW1Term
