/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NvTop

/-!
# BUF's death threshold for version families stopped at the candidate's stop (D49 (A))

Packet PROVE-GW2-NOTHR (round 5). `GW2Nv.deathThrX_of_export` (round 4) asked for D27's exhaustion below the death
clock at every sample, including those where the candidate outlives its cap (death clock `⊤`, exhaustion up to the
contact). A version family stopped at the candidate's stop (decision D49 (A), needed by the `mean` statement) cannot
exhaust up to the contact there. The proof only reads the exhaustion when the death clock is finite. This file is the
same proof with that weaker hypothesis:

* **`ae_kernel_deathEvent_fin`**, **`deathThrX_of_export_fin`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Nv

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Supp8.Q3Stop
  MartChar.RealFlow GW2Nu Sec5.Prop513Schedule

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The death event of every root-`x` instance holds under the launch kernel** of a launched candidate, from
D46's death clause, D27's exhaustion below a FINITE death clock and the caps below the death. -/
theorem ae_kernel_deathEvent_fin (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a j : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hD27 : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      deathClockX c r l a ω < ⊤ → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
        (ver Ω c r l a).V n ω)
    (hcaps : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      0 < candLife c r l a ω → ∀ n, (ver Ω c r l a).V n ω < deathClockX c r l a ω)
    (hexp : StageDeathExportX c r l a (instX h13 ver ch Ω c r l a j hx) (ver Ω c r l a).R (ver Ω c r l a).V
      (rootPt r.1)) :
    ∀ᵐ ω₀ ∂c.P, AllSucc (specDelta (GW2Olm.futSpec c r l a)) (fun i => GW2Olm.futFam c r l a i ω₀)
        (GW2Olm.curIdx c r l) →
      ∀ᵐ ξ ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀),
        ξ ∈ deathEvent c r l a (instX h13 ver ch Ω c r l a j hx) (ver Ω c r l a).R (ver Ω c r l a).V
          (rootPt r.1) := by
  set I := instX h13 ver ch Ω c r l a j hx with hI
  set x := rootPt r.1 with hxdef
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := hS.2.1 k
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hGTs := schedGTX_spec h13 c r l a
  have hGT := hGTs.1
  have hver : ∀ n, IsRelVersionX x c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α
      ((ver Ω c r l a).R n) ((ver Ω c r l a).V n) := fun n => ((ver Ω c r l a).isA hx n).1.1
  filter_upwards [hexp, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hD27,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hcaps, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hGTs.2.2,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_srecX_mem_launchBadRec_iff h13 c r l a I x)]
    with ω₀ hX hD27₀ hcaps₀ hGT₀ hbad₀ hL₀
  have hlaunch := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _) (fun i => E i ω₀) (show k < spec.2.2.length by omega)).1 hL₀
  obtain ⟨b, J, h, Wα, ζα, α, b', J', h', cw, W, ζ, γ, t₀, lam, F, hb, hb', hT, hfl, hα, hcf, hγ, hcwJ, hcwb,
    hcl⟩ := hX _ _ hlaunch
  have hG := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb hfl
  have hpos := ae_stage_threshold_at_death c.hκ c.hκ4 hb hG hb' hT hfl hα hcf hγ cw hcwJ hcwb
  have hseed := ae_stage_seed_at_death c.hκ hb hG hb' hT hfl hcf hγ cw hcwJ hcwb
  filter_upwards [hcl, hpos, hseed, hD27₀, hcaps₀, hGT₀, hbad₀]
    with ξ hclξ hposξ hseedξ hD27ξ hcapsξ hGTξ hbadξ hGξ holdξ hSV hfin
  have hgood : cfRec c.s c.W c.ζ ξ ∈ goodX x c.s := hGTξ.1 hGξ
  have hd : deathClockX c r l a ξ < ⊤ := (mem_deathFin_iff c r l a hGT I rfl rfl rfl hGξ).1 hfin
  obtain ⟨hγH, hlam, hFfin, hdat, hζα, hposcl⟩ := hclξ hGξ holdξ hSV hd
  set S := stgStartX x c.s c.W c.ζ I.W I.GT I.V I.T ξ with hSdef
  refine ⟨fun hbadrec => ?_, fun hnotbad => ?_⟩
  · -- a zero lifetime: the seed threshold
    have hz : candLife c r l a ξ = 0 := (hbadξ holdξ).1 hbadrec
    have h1 := hseedξ (t₀ ξ) (hζα.trans hz) (I.β (I.srecX c r l x ξ)) (lam ξ) (F ξ) (fun _ => (0 : ℝ)) hlam hFfin
      hdat continuous_const rfl
    exact (stageThresholdN_zero_iff (I.β (I.srecX c r l x ξ)) continuous_const rfl).1 h1
  · -- a positive lifetime: the threshold at the death, read through the versions
    have hclpos : 0 < candLife c r l a ξ := pos_iff_ne_zero.2 fun hz => hnotbad ((hbadξ holdξ).2 hz)
    obtain ⟨hTc, hclk, Wd, hWdc, hWd0, hWdagree, hhull⟩ := hposcl hclpos
    obtain ⟨hSeq, hS0, -, hSlt, -⟩ := stage_start_death c r l a hGT hs hx hGξ ((ver Ω c r l a).fin j ξ) hSV hd
    have hSeq' : (S : ℝ) = clockX x c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ξ := hSeq
    have hdeq := deathClockX_eq_of_lt_top c r l a hd
    set dN := (deathClockX c r l a ξ).toNNReal with hdNdef
    have hdN : (dN : ℝ≥0∞) = deathClockX c r l a ξ := ENNReal.coe_toNNReal hd.ne_top
    have hclN : (((candLife c r l a ξ).toNNReal : ℝ≥0) : ℝ≥0∞) = candLife c r l a ξ :=
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top
        ((deathClockX_lt_top_iff c r l a ξ).1 hd).1)
    have hlt := hSlt hclpos
    have hdNr : (dN : ℝ) = clockX x c.s c.W c.ζ (schedW c r l a) (historyTime c r l +
        (candLife c r l a ξ).toNNReal) ξ := by
      rw [hdNdef, ENNReal.coe_toNNReal_eq_toReal, hdeq, ENNReal.toReal_ofReal (hS0.trans hlt.le)]
    have hSd : S < dN := by
      have h1 : (S : ℝ) < (dN : ℝ) := by rw [hSeq', hdNr]; exact hlt
      exact NNReal.coe_lt_coe.1 h1
    set u := dN - S with hudef
    have hu : 0 < u := tsub_pos_of_lt hSd
    have hSu : S + u = dN := add_tsub_cancel_of_le hSd.le
    have hucoe : (u : ℝ) = (deathClockX c r l a ξ).toReal - (S : ℝ) := by
      rw [hudef, NNReal.coe_sub hSd.le]
      rfl
    -- the versions at `ξ`
    have hcapsN : ∀ n, (ver Ω c r l a).V n ξ < (dN : ℝ≥0∞) := fun n => hdN ▸ hcapsξ hgood holdξ hclpos n
    have hexhN : ∀ q : ℝ≥0, q < dN → ∃ n, (q : ℝ≥0∞) < (ver Ω c r l a).V n ξ := fun q hq =>
      exists_cap_gt c r l a hGT hs hx hGξ hd (hD27ξ hgood holdξ hd) (hdN ▸ ENNReal.coe_lt_coe.2 hq)
    have hmono : Monotone fun n => (ver Ω c r l a).V n ξ := monotone_nat_of_le_succ fun n => (ver Ω c r l a).mono n ξ
    have hsup : (⨆ n, (ver Ω c r l a).V n ξ) = (dN : ℝ≥0∞) := by
      refine le_antisymm (iSup_le fun n => (hcapsN n).le) (ENNReal.le_of_forall_nnreal_lt fun q hq => ?_)
      obtain ⟨n, hn⟩ := hexhN q (ENNReal.coe_lt_coe.1 hq)
      exact hn.le.trans (le_iSup (fun n => (ver Ω c r l a).V n ξ) n)
    have hprox := stageProxy_eq (R := fun n q => (ver Ω c r l a).R n q ξ) (V := fun n => (ver Ω c r l a).V n ξ)
      (fun n => (hver n).2.1 ξ) (fun n => (hver n).2.2.1 ξ) hmono (fun n t ht => (hver n).2.2.2.1 ξ t ht)
      hcapsN hexhN hWdc hWd0 hWdagree hSu hu
    -- SAFE's converse at the death
    have hT0 : 0 < (candLife c r l a ξ).toNNReal :=
      ENNReal.toNNReal_pos hclpos.ne' (by rw [← hclN]; exact ENNReal.coe_ne_top)
    have hthr := hposξ (t₀ ξ) hγH (candLife c r l a ξ).toNNReal hT0 (hζα.trans hclN.symm) hTc
      (I.β (I.srecX c r l x ξ)) (lam ξ) (F ξ) (stgDrv Wd S) u hlam hFfin hdat (continuous_stgDrv hWdc S)
      (stgDrv_zero Wd S) (by rw [hucoe]; exact hclk) hhull
    show ProxThr c.κ (I.β (I.srecX c r l x ξ)) (fun n q => (ver Ω c r l a).R n q ξ) S
      ((⨆ n, (ver Ω c r l a).V n ξ).toNNReal - S)
    rw [hsup, ENNReal.toNNReal_coe, ← hudef]
    unfold ProxThr
    rw [hprox.1]
    simp only [hprox.2.1, hprox.2.2]
    exact hthr

/-- **BUF's `DeathThrXStatement` from D46's death clause, exhaustion needed only below a finite death clock** (as a
version family stopped at the candidate's stop, D49 (A), provides; `GW2Nv.deathThrX_of_export` asked for it also when
the candidate outlives its cap). -/
theorem deathThrX_of_export_fin (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (ch Ω c r l a).β ∧
        (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧ ∀ y, ((ch Ω c r l a).β y).IsSorted)
    (hD27 : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        deathClockX c r l a ω < ⊤ → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
          (ver Ω c r l a).V n ω)
    (hcaps : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        0 < candLife c r l a ω → ∀ n, (ver Ω c r l a).V n ω < deathClockX c r l a ω)
    (hexp : DeathExportFamily h13 ver ch) : DeathThrXStatementN h13 ver ch := by
  intro Ω mΩ' _ c r l a h hord
  set x := rootPt r.1 with hxdef
  have hx : 0 ≤ x := h.1
  have hs : 0 < c.s := h.2
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ' := hS.2.1 k
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hLS : MeasurableSet[GW2Olm.pastG c r l a] {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    measurableSet_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl (isFlowProg_spec x true L)
      (specDelta_ne_top _) E (by rw [hlen]; omega)
  have hGTs := schedGTX_spec h13 c r l a
  have hGT := hGTs.1
  have hWm : ∀ t, Measurable (schedW c r l a t) := measurable_schedW c r l a
  have hver : ∀ n, IsRelVersionX x c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α
      ((ver Ω c r l a).R n) ((ver Ω c r l a).V n) := fun n => ((ver Ω c r l a).isA hx n).1.1
  -- the death event of every instance, `P`-almost surely
  have hZ : ∀ j : ℕ, ∀ᵐ ξ ∂c.P, ξ ∈ {ω | AllSucc (specDelta spec) (fun j => E j ω) k} →
      ξ ∈ deathEvent c r l a (instX h13 ver ch Ω c r l a j hx) (ver Ω c r l a).R (ver Ω c r l a).V x := by
    intro j
    set I := instX h13 ver ch Ω c r l a j hx with hI
    have hverR : IsRelVersionXR x c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α I.R I.V :=
      ((ver Ω c r l a).isA hx j).1
    have hpre : Measurable (stgPreRecX x c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
      (measurable_stgPreRecX hGTs.1 hs hx (measurable_gb6Rec_src c) hWm
        (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGTs.2.1 hGTs.2.2) hverR I.T).mono
        ((physFilt (measurable_gb6Rec_src c) hWm c.P).le I.T) le_rfl
    have hmeas := measurableSet_deathEvent c r l a I x hGTs.2.1 (measurable_stgStartX_of_pre hpre)
      (hver j).2.2.2.2.1 (measurableSet_deathFin h13 c r l a I rfl rfl)
      (measurable_augRec (measurable_stageEncRec c r l) hpre) (hword Ω c r l hord h a).1 (hword Ω c r l hord h a).2.1
      (fun n => (hver n).1) (fun n => (hver n).2.1) (fun n => (hver n).2.2.2.2.1)
    exact GW2Schedule.ae_of_ae_condExpKernel_on h𝒢 hLS hmeas
      (ae_kernel_deathEvent_fin h13 ver ch c r l a j hx hs (hD27 Ω c r l a h hord) (hcaps Ω c r l a h hord)
        (hexp Ω c r l hord h a j))
  filter_upwards [ae_all_iff.2 hZ, hD27 Ω c r l a h hord, hcaps Ω c r l a h hord, hGTs.2.2,
    ae_all_iff.2 fun j => ae_srecX_mem_launchBadRec_iff h13 c r l a (instX h13 ver ch Ω c r l a j hx) x]
    with ξ hZξ hD27ξ hcapsξ hGTξ hbadξ hGξ hold Wc hcanon hdL j hSV
  obtain ⟨hWc, hWc0, hagree, -, -⟩ := hcanon
  set I := instX h13 ver ch Ω c r l a j hx with hI
  have hgood : cfRec c.s c.W c.ζ ξ ∈ goodX x c.s := hGTξ.1 hGξ
  have hd : deathClockX c r l a ξ < ⊤ := hdL.trans ENNReal.ofReal_lt_top
  have hfin : ξ ∈ deathFin c r l a I x := (mem_deathFin_iff c r l a hGT I rfl rfl rfl hGξ).2 hd
  have hev := hZξ j (Gm.allSucc_future_of_oldSuccess c r l a ξ hold) hGξ hold hSV hfin
  set S := stgStartX x c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
    (historyTime c r l) ξ with hSdef
  obtain ⟨hSeq, hS0, -, hSlt, hSeqz⟩ := stage_start_death c r l a hGT hs hx hGξ ((ver Ω c r l a).fin j ξ) hSV hd
  have hdeq := deathClockX_eq_of_lt_top c r l a hd
  by_cases hbad : I.srecX c r l x ξ ∈ launchBadRec c r l a
  · -- a zero lifetime: the death is the stage start
    have hz : candLife c r l a ξ = 0 := (hbadξ j hold).1 hbad
    refine ⟨0, ?_, ?_⟩
    · rw [ENNReal.coe_zero, add_zero, hdeq, ← hSeqz hz, ← hSeq, ENNReal.ofReal_coe_nnreal]
    · exact (stageThresholdN_zero_iff _ (continuous_stgDrv hWc S) (stgDrv_zero Wc S)).2 (hev.1 hbad)
  · -- a positive lifetime: the threshold at the death through the versions
    have hclpos : 0 < candLife c r l a ξ := pos_iff_ne_zero.2 fun hz => hbad ((hbadξ j hold).2 hz)
    have hlt := hSlt hclpos
    set dN := (deathClockX c r l a ξ).toNNReal with hdNdef
    have hdN : (dN : ℝ≥0∞) = deathClockX c r l a ξ := ENNReal.coe_toNNReal hd.ne_top
    have hdNr : (dN : ℝ) = clockX x c.s c.W c.ζ (schedW c r l a) (historyTime c r l +
        (candLife c r l a ξ).toNNReal) ξ := by
      rw [hdNdef, ENNReal.coe_toNNReal_eq_toReal, hdeq, ENNReal.toReal_ofReal (hS0.trans hlt.le)]
    have hSd : S < dN := by
      have h1 : (S : ℝ) < (dN : ℝ) := by rw [hSeq, hdNr]; exact hlt
      exact NNReal.coe_lt_coe.1 h1
    set u := dN - S with hudef
    have hu : 0 < u := tsub_pos_of_lt hSd
    have hSu : S + u = dN := add_tsub_cancel_of_le hSd.le
    have hcapsN : ∀ n, (ver Ω c r l a).V n ξ < (dN : ℝ≥0∞) := fun n => hdN ▸ hcapsξ hgood hold hclpos n
    have hexhN : ∀ q : ℝ≥0, q < dN → ∃ n, (q : ℝ≥0∞) < (ver Ω c r l a).V n ξ := fun q hq =>
      exists_cap_gt c r l a hGT hs hx hGξ hd (hD27ξ hgood hold hd) (hdN ▸ ENNReal.coe_lt_coe.2 hq)
    have hmono : Monotone fun n => (ver Ω c r l a).V n ξ := monotone_nat_of_le_succ fun n => (ver Ω c r l a).mono n ξ
    have hsup : (⨆ n, (ver Ω c r l a).V n ξ) = (dN : ℝ≥0∞) := by
      refine le_antisymm (iSup_le fun n => (hcapsN n).le) (ENNReal.le_of_forall_nnreal_lt fun q hq => ?_)
      obtain ⟨n, hn⟩ := hexhN q (ENNReal.coe_lt_coe.1 hq)
      exact hn.le.trans (le_iSup (fun n => (ver Ω c r l a).V n ξ) n)
    have hprox := stageProxy_eq (R := fun n q => (ver Ω c r l a).R n q ξ) (V := fun n => (ver Ω c r l a).V n ξ)
      (fun n => (hver n).2.1 ξ) (fun n => (hver n).2.2.1 ξ) hmono (fun n t ht => (hver n).2.2.2.1 ξ t ht)
      hcapsN hexhN hWc hWc0 hagree hSu hu
    have hP := hev.2 hbad
    change ProxThr c.κ (I.β (I.srecX c r l x ξ)) (fun n q => (ver Ω c r l a).R n q ξ) S
      ((⨆ n, (ver Ω c r l a).V n ξ).toNNReal - S) at hP
    rw [hsup, ENNReal.toNNReal_coe, ← hudef] at hP
    refine ⟨u, ?_, ?_⟩
    · rw [← ENNReal.coe_add, hSu, hdN]
    · unfold ProxThr at hP
      rw [hprox.1] at hP
      simp only [hprox.2.1, hprox.2.2] at hP
      exact hP

end InteractingSLE.Theorem14.GW2Nv
