/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedInduct
import InteractingSLE.Spec.Sec5.FrameQConsumers

/-!
# `FrameQ.QScheduleFirstHitStatement` from Lemma 4.7 and the restart law at a switch

Packet PROVE-QSCHED. Lemma 5.7 (spec. pp. 138–139) for the finite extreme-angle schedules of Proposition 5.13 in
the centred Q frame, by induction on the number of switches (`QSchedInduct`), reduced to:

* `h44 : Sec7.AdmCode.Theorem12ParamCond44Statement` (R74; the schedules' pieces are good paths with infinite
  lifetimes, and the regularized histories have the same prefixes),
* `h47 : Prop411Q.Lemma47QHitStatement` (Lemma 4.7 at `π/2`) and `href : Sec7.Lemma71H.Cond44ReferenceStatement`,
* `hcg : CounterflowGivenPrefix44Statement` (Lemma 4.7's conditional law at a switch, under the (4.4) heights).

Main results:

* **`ae_isFirstHitQ_driverTree`**: one schedule, one rational time;
* **`qScheduleFirstHitStatement_of_input`**: `FrameQ.QScheduleFirstHitStatement` from `h44`, `h47`, `href`, `hcg`;
* `qScheduleFirstHitStatement_of_A2`: the same from `h47`, A.2's crosscut statements and `hcg` (the derivations of
  `h44` and `href` already used by `Prop513Asm.theorem12ParamCond44Statement_of_lemma47Q_of_A2`);
* `prop513_comap_of_histExp_cg`: Proposition 5.13 of the current wiring with `hQ` replaced by `hcg`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`;
`h44` is R74's restricted statement, derived from Lemma 4.7Q and A.2.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u v

namespace InteractingSLE.Sec5.QSched

open WangWu (negInv histLine)
open Prop411Q (IsFirstHitQ)
open Sec7.Lemma71I (realPath)
open Cond44Ref (cfHistory)
open Exist Exist.Staged Exist.StagedLaw
open Restart (BoundaryWord)
open Prop513TreeExtract Prop513Schedule Prop513Target

/-! ### The tree coordinates are the trace of the continued driver -/

/-- On the closed horizon, the canonical tree coordinates of a schedule with good pieces are the trace of its
continued driver. -/
theorem prefixTrace_eq_pathTrace {Ω : Type*} {F : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {s : Schedule} {ω : Ω}
    (hg : GoodPieces (F s) s ω) {t : ℝ} (ht : t ∈ Icc 0 (terminal s : ℝ)) :
    prefixTrace (prefixDriver F) s ω t = pathTrace (F s) s 0 ω t.toNNReal := by
  have hne : scheduleList s ≠ [] := fun h' => s.2.1 (List.map_eq_nil_iff.1 h')
  have hL : 0 < (scheduleList s).length := List.length_pos_iff.2 hne
  have hw := joinedDriver_continuous (F s) ω 0 0 (scheduleList s)
    (fun j _ hj => ⟨(hg j (by omega)).1, (hg j (by omega)).2.1⟩)
  obtain ⟨-, -, htr, -⟩ := tail_trace hg hL
  have hη : IsGeneratingTrace (prefixDriver F s ω) (terminal s) (pathTrace (F s) s 0 ω) := by
    refine Sec7.IsGeneratingTrace.congr_lt (htr.mono_horizon le_top) fun r hr => ?_
    rw [tailDrv_zero]
    apply joinedDriver_eq_continued (F s) ω 0 0 (scheduleList s) (timeOrdered_scheduleList s)
    simpa only [← terminal_eq_lastTime, tsub_zero] using (ENNReal.coe_lt_coe.1 hr).le
  exact prefixTrace_eq hw.1.continuousOn hw.2 (fun _ _ => rfl) hη ht

/-- Good paths at every piece give good pieces. -/
theorem goodPieces_of_goodPath {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {s : Schedule} {ω : Ω}
    (hr : ∀ j, IsRegularDriver (E j ω))
    (hg : ∀ j < (scheduleSpec s).2.2.length, E j ω ∈ Sec7.StripWall.goodPathSet) : GoodPieces E s ω := by
  intro j hj
  have hj' : j < (scheduleSpec s).2.2.length := by rwa [length_scheduleSpec]
  have htop := (Sec7.StripWall.mem_goodPathSet.1 (hg j hj')).1
  have hcont := Sec7.StripWall.continuous_of_isRegularDriver (hr j) htop
  have hgood : WangWu.ImgDrv.GoodPath (E j ω).1 ⊤ := by
    simpa only [htop] using Sec7.StripWall.mem_goodPathSet.1 (hg j hj')
  obtain ⟨η, hη, hinj, hH, _⟩ := Sec7.StripWall.exists_simple_trace_of_goodPath hcont (hr j).2.1 hgood
  exact ⟨hcont, (hr j).2.1, η, hη, hinj, hH⟩

/-! ### One schedule -/

section One

variable {κ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}

/-- A positive time before the terminal time lies in some piece: `τ k < σ ≤ τ (k + 1)`. -/
theorem exists_piece {s : Schedule} {σ : ℝ} (hσ : 0 < σ) (hσT : σ < terminal s) :
    ∃ k, k < (scheduleList s).length ∧ (tau s k : ℝ) < σ ∧ σ ≤ tau s (k + 1) := by
  classical
  have hne : scheduleList s ≠ [] := fun h' => s.2.1 (List.map_eq_nil_iff.1 h')
  have hL : 0 < (scheduleList s).length := List.length_pos_iff.2 hne
  have hex : ∃ j, σ ≤ tau s (j + 1) := ⟨(scheduleList s).length - 1, by
    rw [Nat.sub_add_cancel hL, tau_length]
    exact hσT.le⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have hle : Nat.find hex ≤ (scheduleList s).length - 1 := Nat.find_min' hex (by
      rw [Nat.sub_add_cancel hL, tau_length]
      exact hσT.le)
    omega
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]
      simpa only [tau, NNReal.coe_zero] using hσ
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      rw [hj]
      exact lt_of_not_ge this

/-- **Lemma 5.7 in the Q frame for one schedule and one rational time** (spec. pp. 138–139): almost surely the
counterflow first contacts the schedule's prefix `η((0, σ])` at `η(σ)`. -/
theorem ae_isFirstHitQ_driverTree (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hcg : CounterflowGivenPrefix44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) {F : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hF : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (F s))
    (hFr : ∀ s j ω, IsRegularDriver (F s j ω)) (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) (n : ℕ) (σ : ℚ)
    (hσ : 0 < (σ : ℝ)) (hσT : (σ : ℝ) < treeTime n) :
    ∀ᵐ ω ∂P, IsFirstHitQ (driverTree F n ω) (fun t : ℝ => γ ω t.toNNReal) σ := by
  set s := scheduleAt n with hsdef
  have hσ0 : (0 : ℚ) < σ := by exact_mod_cast hσ
  have hle := (hF s).2.1
  -- the pieces are good paths with infinite lifetimes
  have hgp := ae_schedule_goodPath h44 hκ hκ4 c hc hh s (hF s) (hFr s)
  have hTop : ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (F s j ω).2 = ⊤ :=
    hgp.mono fun _ hω j hj => (Sec7.StripWall.mem_goodPathSet.1 (hω j hj)).1
  have hgood : ∀ᵐ ω ∂P, GoodPieces (F s) s ω := hgp.mono fun ω hω => goodPieces_of_goodPath (hFr s · ω) hω
  -- the piece containing `σ`
  obtain ⟨k, hk, hτk, hσk⟩ := exists_piece hσ (by simpa only [treeTime] using hσT)
  have hk' : k < (scheduleSpec s).2.2.length := by rwa [length_scheduleSpec]
  have hq' : 0 < (σ : ℝ) - tau s k := sub_pos.2 hτk
  have hqd : (σ : ℝ) - tau s k ≤ dur s k := by
    rw [tau_succ hk, NNReal.coe_add] at hσk
    linarith
  have hst := stage_firstHit h47 href hcg hκ hκ4 hc hh (hF s) (hFr s) hTop hgood hcf hζ hγ hk' hq' hqd
  rw [add_sub_cancel] at hst
  -- the measurable version of the counterflow
  have hYm := Cond44Ref.measurable_cfHistory (Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  have hpathW : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    obtain ⟨b', J', g, -, -, hd⟩ := hcf
    obtain ⟨g', 𝓕', VL', VR', B', -, hC'⟩ := hd
    filter_upwards [hC'.1.2.2.2.2] with ω hp
    exact ⟨hp.1, hp.2.2.2.1⟩
  have hhl : ∀ᵐ ω ∂P, histLine (cfHistory W ζ ω) = fun s : ℝ => γ ω s.toNNReal := by
    filter_upwards [hζ, hγ, hpathW] with ω hζω hγω hpω
    have hw : Continuous fun t => W t ω := by
      have := hpω.2
      rw [hζω] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    rw [CfRegQ.histLine_eq_traceAt, GlueCond.hDrv_cfHistory hζω hw]
    funext t
    exact LP.traceAt_eq_of_isGeneratingTrace hγω hw.continuousOn hpω.1 ENNReal.coe_lt_top
  -- the path facts
  have hpath : ∀ᵐ ω ∂P, GoodPieces (F s) s ω ∧ histLine (cfHistory W ζ ω) = (fun s : ℝ => γ ω s.toNNReal) ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hgood, hhl, hγ] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hσle : (σ : ℝ) ≤ terminal s := by simpa only [treeTime] using hσT.le
  have hcode : ∀ ω, GoodPieces (F s) s ω → IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) →
      ContinuousOn (driverTree F n ω) (Ioc 0 σ) ∧ (∀ t ∈ Ioc (0 : ℝ) σ, driverTree F n ω t ≠ 0) ∧
        Continuous (fun t : ℝ => γ ω t.toNNReal) := by
    intro ω hg hγω
    obtain ⟨-, -, htr, hH⟩ := tail_trace hg (List.length_pos_iff.2 fun h' => s.2.1 (List.map_eq_nil_iff.1 h'))
    have hpc : Continuous (pathTrace (F s) s 0 ω) :=
      continuousOn_univ.1 (htr.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have he : EqOn (driverTree F n ω) (fun t : ℝ => pathTrace (F s) s 0 ω t.toNNReal) (Ioc 0 σ) := fun t ht =>
      prefixTrace_eq_pathTrace hg ⟨ht.1.le, ht.2.trans hσle⟩
    refine ⟨((hpc.comp continuous_real_toNNReal).continuousOn).congr he, fun t ht h0 => ?_,
      (continuousOn_univ.1 (hγω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)).comp
        continuous_real_toNNReal⟩
    have h0' : pathTrace (F s) s 0 ω t.toNNReal = 0 := (he ht).symm.trans h0
    have := hH t.toNNReal (Real.toNNReal_pos.2 ht.1)
    rw [h0'] at this
    exact lt_irrefl 0 (show (0 : ℂ).im > 0 from this)
  -- the measurable first-contact event along the nested laws
  have hAm : MeasurableSet {ω | RestartGen.FirstHitCode σ (driverTree F n ω) (histLine (cfHistory W ζ ω))} :=
    RestartGen.measurableSet_firstHitCode (γ := fun ω => driverTree F n ω)
      (β := fun ω => histLine (cfHistory W ζ ω))
      (fun t => measurable_prefixTrace (fun s' => measurable_prefixDriver_of_staged hF s') s t)
      (fun t => (WangWu.measurable_histLine t).comp hYm) σ
  have hA : ∀ᶠ ω in stageFilter P (pastSigma κ c.fn c.jumps (scheduleSpec s) (F s)) (k + 1),
      ω ∈ {ω | RestartGen.FirstHitCode σ (driverTree F n ω) (histLine (cfHistory W ζ ω))} := by
    have h1 := eventually_stageFilter_succ.2 hst
    filter_upwards [h1, stageFilter_of_ae hle (k + 1) hpath] with ω hω hpω
    obtain ⟨hg, hhlω, hγω⟩ := hpω
    obtain ⟨hdc, hd0, hγc⟩ := hcode ω hg hγω
    have hfh : IsFirstHitQ (driverTree F n ω) (fun t : ℝ => γ ω t.toNNReal) σ :=
      (isFirstHitQ_congr_left hσ fun t ht =>
        (prefixTrace_eq_pathTrace hg ⟨ht.1.le, ht.2.trans hσle⟩).symm).1 hω
    show RestartGen.FirstHitCode σ (driverTree F n ω) (histLine (cfHistory W ζ ω))
    rw [hhlω]
    exact RestartGen.firstHitCode_of_isFirstHitQ hγc hσ0 hdc hd0 hfh
  have hAP := ae_of_stageFilter hle (k + 1) hAm hA
  filter_upwards [hAP, hpath] with ω hω hpω
  obtain ⟨hg, hhlω, hγω⟩ := hpω
  obtain ⟨hdc, hd0, hγc⟩ := hcode ω hg hγω
  have hcodeω : RestartGen.FirstHitCode σ (driverTree F n ω) (fun t : ℝ => γ ω t.toNNReal) := by
    have h' : RestartGen.FirstHitCode σ (driverTree F n ω) (histLine (cfHistory W ζ ω)) := hω
    rwa [hhlω] at h'
  refine RestartGen.isFirstHitQ_of_firstHitCode hγc ?_ hσ0 hdc hd0 hcodeω
  show γ ω (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero]
  exact hγω.1

end One

/-! ### The statement -/

/-- **`FrameQ.QScheduleFirstHitStatement` from Lemma 4.7 and the restart law at a switch.** The given staged
histories are first regularized at every sample (`Theorem14.StagedReg.regHist`, a staged history again under R51);
`h44` identifies their prefixes with the original ones almost surely. -/
theorem qScheduleFirstHitStatement_of_input (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hcg : CounterflowGivenPrefix44Statement.{u}) : FrameQ.QScheduleFirstHitStatement.{u} := by
  intro κ hκ hκ4 c hc Ω _ _ P _ h hh W ζ γ hcf hζ hγ E hE hR _ n σ hσ hσT
  let F : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun s => Theorem14.StagedReg.regHist (scheduleSpec s) (E s)
  have hF : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (F s) := fun s =>
    Theorem14.StagedReg.isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s)
  have hFr : ∀ s j ω, IsRegularDriver (F s j ω) := fun _ _ _ => Theorem14.StagedReg.isRegularDriver_regHist _ _
  filter_upwards [ae_isFirstHitQ_driverTree h44 h47 href hcg hκ hκ4 hc hh hF hFr hcf hζ hγ n σ hσ hσT,
    ae_prefixDriver_regHist h44 hκ hκ4 c hc hh hE hR] with ω h1 h2
  have he : driverTree E n ω = driverTree F n ω := by
    funext t
    change (LP.drivingTrace ((terminal (scheduleAt n) : ℝ≥0∞), prefixDriver E (scheduleAt n) ω)).2 t.toNNReal =
      (LP.drivingTrace ((terminal (scheduleAt n) : ℝ≥0∞),
        prefixDriver (fun s => Theorem14.StagedReg.regHist (scheduleSpec s) (E s)) (scheduleAt n) ω)).2 t.toNNReal
    rw [h2]
  rw [he]
  exact h1

/-- **The same from Lemma 4.7 at `π/2`, A.2's crosscut statements and the restart law at a switch** (the
derivations of `h44` and of the §4.2 reference used by `Prop513Asm.theorem12ParamCond44Statement_of_lemma47Q_of_A2`). -/
theorem qScheduleFirstHitStatement_of_A2 (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hcg : CounterflowGivenPrefix44Statement.{u}) : FrameQ.QScheduleFirstHitStatement.{u} :=
  qScheduleFirstHitStatement_of_input (Prop513Asm.theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') h47
    (Cond44Ref.cond44ReferenceStatement_of_prop411Q
      (Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47
        (partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'))) hcg

end InteractingSLE.Sec5.QSched

namespace InteractingSLE.Sec5.QSched

open QuantumZipper LQGMetric Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire
open Restart Exist Exist.Staged Exist.StagedLaw StripRevVisit Prop513Asm Prop59Stage

/-- **REVVISIT's physical first-exit input** (`StripRevVisit.StagedPrefixFirstHitStatement`, Lemma 5.7's first exit
for the Figure 5.1 prefixes) from Lemma 4.7 at `π/2`, A.2 and the restart law at a switch. -/
theorem stagedPrefixFirstHitStatement_of_cg (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hcg : CounterflowGivenPrefix44Statement.{u}) : StagedPrefixFirstHitStatement.{u} :=
  FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit_A2 hA2 hA2'
    (qScheduleFirstHitStatement_of_A2 h47 hA2 hA2' hcg)

/-- **Proposition 5.13 of the current wiring with `hQ` replaced by the restart law at a switch** (exactly the
binders and conclusion of `FrameQ.prop513_comap_of_histExp_qSchedule`, with `hQ` replaced by `hcg`). -/
theorem prop513_comap_of_histExp_cg
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hcg : CounterflowGivenPrefix44Statement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa)
      (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ,
      (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  FrameQ.prop513_comap_of_histExp_qSchedule h47 hA2 hA2' (qScheduleFirstHitStatement_of_A2 h47 hA2 hA2' hcg)
    hκ hκ4 hb hG hcf htr hE hR X₀ hL₀ X hL

end InteractingSLE.Sec5.QSched
