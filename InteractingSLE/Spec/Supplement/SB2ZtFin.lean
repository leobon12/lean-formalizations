/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ZtEnd
import InteractingSLE.Spec.Supplement.SB2ZsSucc
import InteractingSLE.Spec.Supplement.SB2MuLife
import InteractingSLE.Spec.Supplement.SBS3DxDrvAssemble
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwVkLink
import InteractingSLE.Spec.Supplement.SBS3DwVnTr

/-!
# SB2(1)'s final gluing, part 3: the driver link from the successor version half and E7

Packet PROVE-T14-SB2DRV (round 16; decisions D4, D10, D19, D22). SB2(1)'s per-sample identification of the remainder
(`Lv.SB2RemainderCodeLeStatement`, hence the bounded driver link `Lv.SB2DriverLinkAmbLeStatement`) from Theorems
1.2–1.3 and E7 in its bounded form (`Vh.SB2RemainderLifeLeStatement`, PROVE-T14-SB2WORD's target). The proof runs
D4's order:

1. **identification at the stops**: PROVE-AUX61-NOJUMP's successor version (`Vt.exists_stopDataLe`, the stop data
   behind `Vt.sb2LineVersionSLeStatement_of_thm'`) and this packet's `Lv.ae_isStopDrvMatch_of_versionS` (K2 at each
   stop, Aux. lemma 54's regular-stop form, Theorem 1.2): every frozen driver is the canonical driver code before its
   stop;
2. **gluing**: the stops are cofinal in the relative lifetime `U` (`Zt.ae_cofinal`), so the relative driver is the
   canonical code before `U` and `U ≤ ζc` (`isStopDrvMatch_glue`);
3. **endpoint**: the canonical conditional driver has its trace event almost surely (`ae_mem_traceSet_of_condFlowLine`),
   so the relative trace converges at a finite `U` (`exists_tendsto_capTrace`), the physical lifetime is then finite
   (NOJUMP's step 2, `Vn.ae_ne_top_of_capTrace_tendstoLe`) and the frozen trace is linked (`Vk.isRemainderLink_frz`);
4. **`U = ζc`** (D4 step 3): if `U < ζc`, the canonical driver frozen at a rational `q ∈ (U, ζc)` is continuous, is the
   relative driver before `U`, generates the frozen trace and is linked to the remainder; E7 makes `U` its threshold,
   while the canonical flow line has no threshold before its lifetime (`Mu.ae_lt_thr_frozenCanon`): `U > q`.

* `isStopDrvMatch_glue`, `exists_tendsto_capTrace` (deterministic);
* **`sb2RemainderCodeLeStatement_of_remainderLife`**, **`sb2DriverLinkAmbLeStatement_of_remainderLife`**;
* `sb2RemainderLifeLeStatement_of_vh`: SB2WORD's unbounded E7 gives the bounded one.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only. No source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Zt

open Exist Exist.Staged Exist.StagedLaw Restart GW1W WalkInf Lv Sec7.PocketTraversal Supp8.Q3Stop Sec2.Assembly
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-! ### Deterministic gluing -/

/-- **Gluing the stopped matches**: drivers frozen at stops `V m ≤ U`, each the relative driver through its stop and
each matching a code before its stop, with stops cofinal in `U`, make the relative driver match the code before
`U`. -/
theorem isStopDrvMatch_glue {p : PCode × ℝ≥0∞} {Wr : ℝ≥0 → ℝ} {U : ℝ≥0∞} {Vs : ℕ → ℝ≥0∞}
    {Wm : ℕ → ℝ≥0 → ℝ} (hm : ∀ m, IsStopDrvMatch p (Wm m) (Vs m))
    (hWm : ∀ m (t : ℝ≥0), (t : ℝ≥0∞) ≤ Vs m → Wm m t = Wr t)
    (hcof : ∀ s : ℝ≥0, (s : ℝ≥0∞) < U → ∃ m, (s : ℝ≥0∞) < Vs m) : IsStopDrvMatch p Wr U := by
  refine ⟨le_of_not_gt fun hlt => ?_, fun n k hnk => ?_⟩
  · obtain ⟨s, hs1, hs2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    obtain ⟨m, hm'⟩ := hcof s hs2
    exact absurd (hm'.trans_le (hm m).1) (not_lt.2 hs1.le)
  · obtain ⟨m, hm'⟩ := hcof _ hnk
    rw [← hWm m _ hm'.le]
    exact (hm m).2 n k hm'

/-- **The relative trace converges at a finite lifetime below the canonical one** (deterministic): the relative
driver agrees before `U` with a regular driver in the trace set whose lifetime is at least `U`. -/
theorem exists_tendsto_capTrace {ρ : ℝ → ℂ} {Wr : ℝ≥0 → ℝ}
    (hgen : ∀ T : ℝ≥0∞, T < Sec7.Lemma71C.capLife ρ → IsGeneratingTrace Wr T (capTrace ρ))
    (hWrc : ContinuousOn Wr {t | (t : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ}) (hWr0 : Wr 0 = 0)
    (hU0 : 0 < Sec7.Lemma71C.capLife ρ) (hU : Sec7.Lemma71C.capLife ρ ≠ ⊤) {Dd : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hDr : IsRegularDriver Dd) (htr : Dd ∈ Sec7.RandRestart.traceSet) (hle : Sec7.Lemma71C.capLife ρ ≤ Dd.2)
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ → Wr t = Dd.1 t) :
    ∃ z, Tendsto (capTrace ρ) (𝓝[<] (Sec7.Lemma71C.capLife ρ).toNNReal) (𝓝 z) := by
  set U := Sec7.Lemma71C.capLife ρ with hUdef
  have hft : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U → capTrace ρ t = LP.traceAt t Dd.1 := by
    intro t ht
    obtain ⟨T, htT, hTU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have h1 := LP.traceAt_eq_of_isGeneratingTrace (hgen T hTU) (hWrc.mono fun s hs => lt_trans hs hTU) hWr0 htT
    rw [← h1]
    exact LP.traceAt_congr fun r hr => hag r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht)
  change (Dd.2 = ⊤ ∧ Sec7.RandRestart.ratVals Dd.1 ∈ Sec7.RandRestart.transientSet) ∨
    (Dd.2 ≠ ⊤ ∧ Sec7.RandRestart.FinCond Dd.1 Dd.2) at htr
  rcases htr with ⟨htop, hrat⟩ | ⟨-, hfc⟩
  · have hc : Continuous Dd.1 := by
      rw [← continuousOn_univ]
      refine hDr.1.mono fun t _ => ?_
      show (t : ℝ≥0∞) < Dd.2
      rw [htop]; exact ENNReal.coe_lt_top
    obtain ⟨η, hη, -⟩ := (Sec7.RandRestart.mem_transientSet_iff hc hDr.2.1).1 hrat
    have hηc : Continuous η := by
      rw [← continuousOn_univ]
      refine hη.2.1.mono fun t _ => ?_
      show (t : ℝ≥0∞) ≤ ⊤
      exact le_top
    have heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U → capTrace ρ t = η t := fun t ht => by
      rw [hft t ht]
      exact LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn hDr.2.1 ENNReal.coe_lt_top
    refine ⟨η U.toNNReal, (hηc.tendsto _).mono_left nhdsWithin_le_nhds |>.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine (heq t ?_).symm
    rw [← ENNReal.coe_toNNReal hU]
    exact ENNReal.coe_lt_coe.2 ht
  · exact exists_tendsto_of_finCond hfc hle hU hU0 (Vk.continuousOn_of_forall_lt hgen) hft

/-! ### The final assembly -/

/-- SB2WORD's E7 (unbounded) gives the bounded E7. -/
theorem sb2RemainderLifeLeStatement_of_vh (hE7 : Vh.SB2RemainderLifeStatement.{u}) :
    Vh.SB2RemainderLifeLeStatement.{u} :=
  fun κ b jumps _ _ _ P _ h E k u ψ η ζ HP _ I u₀ D w hw => hE7 κ b jumps P h E k u ψ η ζ HP I u₀ D w hw

/-- **SB2(1)'s per-sample identification of the remainder for `ψ ≤ π/2`**, from Theorems 1.2–1.3 and E7. -/
theorem sb2RemainderCodeLeStatement_of_remainderLife (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12p₀ : Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hE7 : Vh.SB2RemainderLifeLeStatement.{u}) :
    SB2RemainderCodeLeStatement h12p := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP _ I
  classical
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension HP.boundary
  obtain ⟨D⟩ := exists_entranceUnion h12p HP u₀ hu₀
  have hS3 := Tc.sb2EntranceNoCommonArcLeStatement_of_thm h12p h13 h12p₀ h13₀
  obtain ⟨S⟩ := Vt.exists_stopDataLe h13 hS3 (Vt.sb2RelSeedAdmLeStatement h13 hS3) HP I D
  have hκ := HP.kappa_pos
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hSt := HP.staged (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) hprog
  have h𝒢 := hSt.2.1 (k + 1)
  have hF : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma HP.boundary hSt.1
      (HP.drivers_regular (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)
  have hr := measurable_pastMap (κ := κ) runMeasStatement HP.boundary
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j _ => hSt.1 j)
    (fun j _ => HP.drivers_regular (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j) (k + 1) le_rfl
  -- the canonical conditional driver of the launch chart
  obtain ⟨Dd, hDm, hDr, hD⟩ := exists_condFlowLineDriverOn_of_chartField h12p h13 hκ ψ hr HP.field.1
    I.word_measurable I.chart_measurable I.frozen I.field
  have hWm : ∀ t, Measurable (fun ω => (Dd ω).1 t) := fun t => (measurable_pi_apply t).comp hDm.fst
  have hcode := ae_codeMatch_of_isCondFlowLineDriverOn h12p h13 hκ ψ h𝒢 hF HP.field.1 I.word_measurable
    I.chart_measurable (I.frozen.mono fun _ h _ => h) hWm hDm.snd hD
  have htrace := ae_mem_traceSet_of_condFlowLine h13 hκ h𝒢 hF hDm hDr hD
  -- the chart field and its conditional law
  set Y : Ω → DistOn upperHalfPlaneOpens := fun ω =>
    Chart.chartTransport (I.chart_measurable.1 ω) 1 0 (chiC κ) (h ω) with hYdef
  have hcm := I.chart_measurable.mono h𝒢
  have hYm : Measurable Y := Chart.measurable_chartTransport_random' I.chart_measurable.1 hcm.2.2.2.1
    hcm.2.2.2.2.1 hcm.2.2.2.2.2.2 I.chart_measurable.2.1 HP.field.1 1 0 (chiC κ)
  have hlawY : ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀) Y (I.word ω₀).fn (I.word ω₀).jumps := by
    filter_upwards [I.field, ae_frozen_chart_of_le HP I h𝒢 le_rfl] with ω₀ hf hfr hF₀
    obtain ⟨-, h', hct, hg⟩ := hf hF₀
    refine isGFFWithBoundaryData_congr_ae hg hYm ?_
    filter_upwards [hfr hF₀] with ω hω
    have hH : Y ω = Chart.chartTransport (I.chart_measurable.1 ω₀) 1 0 (chiC κ) (h ω) :=
      CondDriverBridge.chartTransport_congr_chart (I.chart_measurable.1 ω) (I.chart_measurable.1 ω₀) hω 1 0
        (chiC κ) (h ω)
    rw [hH]
    exact (IsChartTransport.unique (I.chart_measurable.1 ω₀) (hct ω)
      (CondDriverBridge.isChartTransport_chartTransport_of_continuousOn (I.chart_measurable.1 ω₀)
        (I.chart_measurable.2.1 ω₀) 1 0 (chiC κ) (h ω)))
  have hthr : ∀ r : ℚ, ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ I.word (launchSet κ b jumps E (k + 1)) w →
      (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (driverOf h12p hκ ψ (I.word ω, Y ω)).2 →
      (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w)
        (Mu.frozenCanon h12p hκ ψ I.word Y (r : ℝ).toNNReal) (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω :=
    fun r w _ => Mu.ae_lt_thr_frozenCanon h12p h13 hκ ψ h𝒢 hF I.word_measurable hYm hlawY w (r : ℝ).toNNReal
  have hE7' := fun w hw => hE7 κ b jumps P h E k u ψ η ζ HP I u₀ D w hw
  have hid := ae_isStopDrvMatch_of_versionS h12p h13 HP I hu₀ D S.versionS
  filter_upwards [hid, ae_cofinal HP S, hcode, htrace,
    ae_all_iff.2 fun r => (ae_ball_iff I.types_countable).2 (hthr r), (ae_ball_iff I.types_countable).2 hE7',
    Vk.ae_lift_chartLe h13 hS3 HP, Vn.ae_ne_top_of_capTrace_tendstoLe h13 hS3 HP S.hρ, D.ae_mem_event_iff,
    I.cover] with ω hidω hcofω hcodeω htrω hthrω hE7ω hliftω hfinω hevω hcovω hFω hvis
  have hDω : ω ∈ D.event := (hevω hFω).2 hvis
  obtain ⟨hGs, hcof'⟩ := hcofω hDω
  have hg := S.good hGs
  have hρω := S.ρ'_eq hGs
  set ρ := S.ρ ω with hρdef
  set U := Sec7.Lemma71C.capLife ρ with hUdef
  have hgen : ∀ T : ℝ≥0∞, T < U → IsGeneratingTrace (S.Wr · ω) T (capTrace ρ) := fun T hT => by
    have := S.isGeneratingTrace_Wr ω (T := T) (by rw [hρω]; exact hT)
    rwa [hρω] at this
  have hWrc : ContinuousOn (S.Wr · ω) {t | (t : ℝ≥0∞) < U} := by
    have := S.continuousOn_Wr ω
    rwa [hρω] at this
  have hWr0 : S.Wr 0 ω = 0 := S.Wr_zero ω
  have hU0 : 0 < U := Vk.capLife_pos hg.driven
  set p := driverCode h12p hκ ψ (I.word ω, Y ω) with hpdef
  -- 1–2: identification at the stops and gluing
  have hm : ∀ m, IsStopDrvMatch p (S.W m · ω) (S.V m ω) := fun m => hidω hDω m
  have hglue : IsStopDrvMatch p (S.Wr · ω) U := by
    refine isStopDrvMatch_glue hm (fun m t ht => S.W_eq_Wr hGs (by rw [← S.V_eq hGs]; exact ht)) fun s hs => ?_
    obtain ⟨m, hm'⟩ := hcof' s hs
    exact ⟨m, by rw [S.V_eq hGs]; exact hm'⟩
  have hDd := eqOn_of_isStopDrvMatch_of_isDriverCodeMatch hglue (hcodeω hFω) hWrc (hDr ω).1
  -- 3: the endpoint and the link
  have hlim : U ≠ ⊤ → ∃ z, Tendsto (capTrace ρ) (𝓝[<] U.toNNReal) (𝓝 z) := fun hU =>
    exists_tendsto_capTrace hgen hWrc hWr0 hU0 hU (hDr ω) (htrω hFω) hDd.1 hDd.2
  have hζfin : U ≠ ⊤ → ζ ω ≠ ⊤ := fun hU => by
    obtain ⟨z, hz⟩ := hlim hU
    exact hfinω hFω hg.ent hg.driven hU z hz
  set Γ : ℝ≥0 → ℂ := Vk.frz (capTrace ρ) U with hΓdef
  have hΓgen : IsGeneratingTrace (S.Wr · ω) U Γ :=
    Sec7.IsGeneratingTrace.congr_lt (Vk.isGeneratingTrace_frz hU0 hgen hlim) fun t ht =>
      (Vk.frz_of_lt (f := fun x => S.Wr x ω) ht).symm
  have hlink : IsRemainderLink (Lv.launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
      (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) (fun s => Γ s + launchEntry κ b jumps E (k + 1) u ω) U :=
    Vk.isRemainderLink_frz hg.driven hg.fam1 hg.fam2 hζfin (hliftω hFω hg.ent)
  -- 4: the relative lifetime is the canonical one (E7)
  have hUp : U = p.2 := by
    refine le_antisymm hglue.1 (le_of_not_gt fun hlt => ?_)
    obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    set q : ℝ≥0 := (r : ℝ).toNNReal with hqdef
    have hq : (q : ℝ≥0∞) = ENNReal.ofReal r := rfl
    have hq1 : U < (q : ℝ≥0∞) := hq ▸ hr1
    have hq2 : (q : ℝ≥0∞) < (driverOf h12p hκ ψ (I.word ω, Y ω)).2 := hq ▸ hr2
    obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (I.word ω) = w₀ := ⟨_, rfl⟩
    have hw₀ : w₀ ∈ I.types := hw₀e ▸ hcovω hFω
    have h1 := hthrω r w₀ hw₀ ⟨hFω, hw₀e⟩ hq2
    obtain ⟨-, hcan⟩ := eqOn_of_isStopDrvMatch_of_isDriverCodeMatch hglue
      (Mu.isDriverCodeMatch_driverOf h12p hκ ψ (I.word ω, Y ω)) hWrc
      (Mu.continuousOn_driverOf h12p hκ ψ (I.word ω, Y ω))
    have hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U →
        Mu.frozenCanon h12p hκ ψ I.word Y q t ω = S.Wr t ω := fun t ht => by
      have htq : t ≤ q := (ENNReal.coe_lt_coe.1 (ht.trans hq1)).le
      simp only [Mu.frozenCanon, hq2, ↓reduceIte, min_eq_left htq]
      exact (hcan t ht).symm
    have hWq0 : Mu.frozenCanon h12p hκ ψ I.word Y q 0 ω = 0 := by
      rw [hag 0 (by exact_mod_cast hU0), hWr0]
    have hgenq : IsGeneratingTrace (fun t => Mu.frozenCanon h12p hκ ψ I.word Y q t ω) U Γ :=
      Sec7.IsGeneratingTrace.congr_lt hΓgen fun t ht => hag t ht
    have h2 := hE7ω w₀ hw₀ hFω hvis ⟨hDω, hw₀e⟩ (Mu.frozenCanon h12p hκ ψ I.word Y q) U Γ
      (Mu.continuous_frozenCanon h12p hκ ψ I.word Y q ω) hWq0 hgenq hlink
    rw [← h2] at h1
    exact absurd (h1.trans hq1) (lt_irrefl _)
  refine ⟨(S.Wr · ω), U, Γ, hWrc, ⟨hUp, ?_, fun n k hnk => hglue.2 n k hnk⟩, hΓgen, hlink⟩
  have h00 := hglue.2 0 0 (by rw [Exist.dyad_zero_zero]; exact_mod_cast hU0)
  rw [Exist.dyad_zero_zero] at h00
  exact h00

/-- **SB2(1)'s bounded driver link from Theorems 1.2–1.3 and E7** (`Lv.SB2DriverLinkAmbLeStatement`). -/
theorem sb2DriverLinkAmbLeStatement_of_remainderLife (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12p₀ : Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hE7 : Vh.SB2RemainderLifeLeStatement.{u}) :
    SB2DriverLinkAmbLeStatement.{u} :=
  sb2DriverLinkAmbStatement_of_remainderCodeLe h12p h13
    (sb2RemainderCodeLeStatement_of_remainderLife h12p h13 h12p₀ h13₀ hE7)

end InteractingSLE.Theorem14.SB.Zt
