/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NyDth
import InteractingSLE.Spec.Supplement.GW2NxDth
import InteractingSLE.Spec.Supplement.GW2PvDthF
import InteractingSLE.Spec.Supplement.GW2SdtLife

/-!
# BUF's death threshold from the positive-lifetime death clause (decision D72)

Packet PROVE-GW2-NOTHR (round 9, D72). STAGEMEAN's death clause in the datum form is proved for a POSITIVE candidate
lifetime (`GW2Pv.StageDeathExportXDP`, `deathExportFamilyDP0_stop`). The zero-lifetime branch of the death threshold
needs no clause: after a successful strictly ordered history the candidate's lifetime is positive almost surely (the
last history piece stops at an interior point, so the launch word's one-sided limits at the tip are the piece's sides
and no candidate angle puts the seed at a threshold; SDE's D45 tools), so a launch-bad stage record does not occur.

* **`ae_candLife_pos_succ`**: SDE's `GW2Sdt.ae_candLife_pos` with J32's alive event replaced by the history's success
  and its strict order;
* **`ae_kernel_deathEvent_finDP`**: the kernel step with the positive-lifetime clause;
* **`deathThrX_hist`** (one history), `DeathExportFamilyDP`, **`deathThrX_of_exportDP_fin`**;
* `DeathThrXStatementS0` (root `0`), **`deathThrX_stop_root0`**, **`deathThrX_stop_root0_canon`**: BUF's death
  threshold at the top's family (stop-capped, GEOM2's word map), root `0`, with NO open input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Nz

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Supp8.Q3Stop
  MartChar.RealFlow GW2Nu GW2Nv GW2Ny Sec5.Prop513Schedule Sec5.CrossCond.StagedRepLater

section Life

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

open GW2Sdt in
/-- **Every candidate launched after a successful strictly ordered history has a positive lifetime**, almost surely
(SDE's `GW2Sdt.ae_candLife_pos` with J32's alive event replaced by the history's success and its strict order). -/
theorem ae_candLife_pos_succ (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hpw : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < GW2Rd.candLife c r l a ω := by
  classical
  set x := rootPt r.1 with hx
  set Lh := historyProgram c r l with hLh
  set Lf := futureProgram c r l a with hLf
  set n := (entryList l).length with hn
  have hk : GW2Olm.curIdx c r l = n + 1 := GW2Ru.length_historyProgram c r l
  have hLhn : Lh.length = n + 1 := hk
  have hLfn : Lf.length = n + 2 := by
    simp only [hLf, futureProgram, List.length_append, List.length_singleton, ← hLh, hLhn]
  have hn1 : n + 1 < (scheduleProgram 0 Lf).length := by
    rw [GW2Schedule.length_scheduleProgram, hLfn]; omega
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 Lf⟩ with hspec
  set θ := specAngle spec with hθ
  set Δ := specDelta spec with hΔ
  set C := canonFam c.hκ c.h12p c.βA c.c₀ θ Δ x c.h with hC
  have hprog : IsFlowProg spec.2.2 θ Δ := isFlowProg_spec x true Lf
  have hΔt : ∀ j, Δ j ≠ ⊤ := specDelta_ne_top spec
  filter_upwards [GW2Rd.ae_life_pos_of_launch_good h13 c r l a,
    ae_canonWord_fn_eq_stopWord c.hκ c.h12p h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh x Lf n hn1,
    GW2Omx.ae_switchTips_cur h13 c r l a hpw, Gm.ae_launched_rdrv_trace h13 c x Lf]
    with ω hlife hexpl hsw htr hold
  -- the pieces of the future schedule succeed up to the candidate
  have hs : AllSucc Δ (fun j => C j ω) (n + 1) := by
    have h := Gm.allSucc_future_of_oldSuccess c r l a ω hold
    rw [← hLh, hLhn] at h
    exact h
  have hsn : Δ n < (C n ω).2 := hs n (Nat.lt_succ_self n)
  refine hlife hold ?_
  show GW2Rd.badDist c.κ (specAngle spec (GW2Olm.curIdx c r l))
    (canonWord c.hκ c.h12p c.βA c.c₀ θ Δ c.κ c.b c.jumps spec c.h (GW2Olm.curIdx c r l) ω) 0 ≠ 0
  rw [hk]
  -- the record of the last history piece
  set rn := pastMap c.κ c.b c.jumps spec C (n + 1) ω (Fin.last n) with hrn
  have hrn' : rn = recOf (Δ n) (C n ω) := by
    have h := congrFun (GW2Schedule.pastMap_of_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl hprog hΔt C
      (k := n + 1) (by rw [GW2Schedule.length_scheduleProgram, hLfn]; omega) hs) (Fin.last n)
    rw [hrn, h]
    simp only [Fin.val_last]
  set Δn : ℝ≥0 := (Δ n).toNNReal with hΔn
  have hΔe : (Δn : ℝ≥0∞) = Δ n := ENNReal.coe_toNNReal (hΔt n)
  rw [← hΔe] at hrn' hsn
  -- the last piece's stop is interior
  have hfs : AllSucc (schedDelta 0 Lf) (fun i => GW2Olm.futFam c r l a i ω) (GW2Olm.curIdx c r l) := by
    intro i hi
    have h1 := hs i (by rw [hk] at hi; exact hi)
    have h2 : Δ i = schedDelta 0 Lf i := Gm.specDelta_schedSpec x (by rw [hk] at hi; omega)
    rw [h2] at h1
    exact h1
  have hint := hsw hfs n (by rw [hk]; exact Nat.lt_succ_self n)
  have hinstr : instrTime (GW2Olm.futSpec c r l a) n = Δ n :=
    GW2Schedule.instrTime_eq (θ := θ) (Δ := Δ) hprog (by show n < (scheduleProgram 0 Lf).length; omega)
  have hstop : GW2aMulti.pieceStop (GW2Olm.futSpec c r l a) (fun i => GW2Olm.futFam c r l a i ω) n =
      (Δn : ℝ≥0∞) := by
    unfold GW2aMulti.pieceStop
    rw [hinstr, ← hΔe]
    show min (Δn : ℝ≥0∞) (C n ω).2 = Δn
    exact min_eq_left hsn.le
  change GW2Later.IsInteriorStop (C n ω).1
    (GW2aMulti.pieceStop (GW2Olm.futSpec c r l a) (fun i => GW2Olm.futFam c r l a i ω) n) at hint
  rw [hstop] at hint
  obtain ⟨-, η, hη⟩ := htr n (by rw [hLfn]; omega) (hs.mono (Nat.le_succ n))
  have hreg := isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ θ Δ x c.h n ω
  have hη' : IsGeneratingTrace (fun t : ℝ≥0 => rdrv (recOf (Δn : ℝ≥0∞) (C n ω)) t) ⊤ η := by
    rw [hΔe]; exact hη
  obtain ⟨hjL, hjR⟩ := junctions_strict_of_interiorStop hreg hsn hη' hint
  rw [← hrn'] at hjL hjR
  -- the launch word's one-sided limits at the tip
  have hlims0 := lims_stopWord_zero c.hκ
    (canonWord c.hκ c.h12p c.βA c.c₀ θ Δ c.κ c.b c.jumps spec c.h n ω) (instrAngle spec n) rn hjL hjR
  have hoff := hexpl hs
  have hlims := GW1.lims_eq_of_eq_off_finset _ hoff 0
  -- the angles
  have hθn : instrAngle spec n ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [show spec = schedSpec x Lf from rfl, instrAngle_schedSpec x (by rw [hLfn]; omega)]
    exact GW2Later.schedAngle_mem_Icc (GW2Olm.mem_Icc_futureProgram c r l a) (by rw [hLfn]; omega)
  have hθa : specAngle spec (n + 1) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [show specAngle spec (n + 1) = instrAngle (schedSpec x Lf) (n + 1) from rfl,
      instrAngle_schedSpec x (by rw [hLfn]; omega)]
    exact GW2Later.schedAngle_mem_Icc (GW2Olm.mem_Icc_futureProgram c r l a) (by rw [hLfn]; omega)
  exact badDist_ne_zero_of_lims c.hκ c.hκ4 _ hθa hθn (hlims.1.trans hlims0.1) (hlims.2.trans hlims0.2)

end Life

section Ker

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The death event of every root-`x` instance holds under the launch kernel** of a launched candidate, from
D46's death clause in the datum form, D27's exhaustion below a FINITE death clock and the caps below the death. -/
theorem ae_kernel_deathEvent_finDP (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
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
    (hpos : ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω)
    (hexp : GW2Pv.StageDeathExportXDP c r l a (instX h13 ver ch Ω c r l a j hx) (ver Ω c r l a).R (ver Ω c r l a).V
      (rootPt r.1)) :
    ∀ᵐ ω₀ ∂c.P, AllSucc (specDelta (GW2Olm.futSpec c r l a)) (fun i => GW2Olm.futFam c r l a i ω₀)
        (GW2Olm.curIdx c r l) →
      HasLaunchPairEq c.κ c.b c.jumps c.P c.h c.W (GW2Olm.futSpec c r l a) (GW2Olm.futFam c r l a)
        (GW2Olm.curIdx c r l) ω₀ →
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
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_srecX_mem_launchBadRec_iff h13 c r l a I x),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hpos]
    with ω₀ hX hD27₀ hcaps₀ hGT₀ hbad₀ hpos₀ hL₀ hdat
  have hlaunch := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _) (fun i => E i ω₀) (show k < spec.2.2.length by omega)).1 hL₀
  obtain ⟨b, J, h, Wα, ζα, α, b', J', h', cw, W, ζ, γ, t₀, lam, F, hb, hb', hT, hfl, hα, hcf, hγ, hcwJ, hcwb,
    hcl⟩ := hX hdat _ _ hlaunch
  have hG := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb hfl
  have hthr := ae_stage_threshold_at_death c.hκ c.hκ4 hb hG hb' hT hfl hα hcf hγ cw hcwJ hcwb
  filter_upwards [hcl, hthr, hD27₀, hcaps₀, hGT₀, hbad₀, hpos₀]
    with ξ hclξ hposξ hD27ξ hcapsξ hGTξ hbadξ hlifeξ hGξ holdξ hSV hfin
  have hgood : cfRec c.s c.W c.ζ ξ ∈ goodX x c.s := hGTξ.1 hGξ
  have hd : deathClockX c r l a ξ < ⊤ := (mem_deathFin_iff c r l a hGT I rfl rfl rfl hGξ).1 hfin
  set S := stgStartX x c.s c.W c.ζ I.W I.GT I.V I.T ξ with hSdef
  refine ⟨fun hbadrec => ?_, fun hnotbad => ?_⟩
  · -- a zero lifetime does not occur after a successful history (almost surely)
    exact absurd ((hbadξ holdξ).1 hbadrec) (hlifeξ holdξ).ne'
  · -- a positive lifetime: the threshold at the death, read through the versions
    have hclpos : 0 < candLife c r l a ξ := pos_iff_ne_zero.2 fun hz => hnotbad ((hbadξ holdξ).2 hz)
    obtain ⟨hγH, hlam, hFfin, hdat, hζα, hposcl⟩ := hclξ hGξ holdξ hSV hd hclpos
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

end Ker

/-- **BUF's death threshold at one history** (admissible root, strictly ordered history) from the positive-lifetime
death clause (STAGEMEAN's `GW2Pv.StageDeathExportXDP`): a zero lifetime does not occur after a successful history
(`ae_candLife_pos_succ`), so only the positive-lifetime branch is read. -/
theorem deathThrX_hist (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) {Ω : Type u} [mΩ' : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (h : GoodRoot c r)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord' : (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2))
    (hβ : Measurable (ch Ω c r l a).β ∧ (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧
      ∀ y, ((ch Ω c r l a).β y).IsSorted)
    (hD27 : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        deathClockX c r l a ω < ⊤ → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
          (ver Ω c r l a).V n ω)
    (hcaps : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        0 < candLife c r l a ω → ∀ n, (ver Ω c r l a).V n ω < deathClockX c r l a ω)
    (hexp : ∀ j : ℕ, GW2Pv.StageDeathExportXDP c r l a (instX h13 ver ch Ω c r l a j h.1) (ver Ω c r l a).R
      (ver Ω c r l a).V (rootPt r.1)) :
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∀ Wc : ℝ≥0 → ℝ, IsCanonXN c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc →
      deathClockX c r l a ξ < ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)
        (schedW c r l a · ξ) (schedTr c r l a ξ) (c.α ξ)) →
      ∀ j : ℕ, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V j ξ →
        ∃ u : ℝ≥0, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) + u = deathClockX c r l a ξ ∧
          StageThresholdN c.κ ((ch Ω c r l a).β ((instX h13 ver ch Ω c r l a j h.1).srecX c r l (rootPt r.1) ξ))
            (stgDrv Wc (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
              ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ)) u
 := by
  have hord : GW2Sdx.HistOrdered c r l := Gm.timeOrdered_of_pairwise_lt hord'
  have hord : GW2Sdx.HistOrdered c r l := Gm.timeOrdered_of_pairwise_lt hord'
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
      (measurable_augRec (measurable_stageEncRec c r l) hpre) hβ.1 hβ.2.1
      (fun n => (hver n).1) (fun n => (hver n).2.1) (fun n => (hver n).2.2.2.2.1)
    exact ae_succ_of_kernel_curS h12 h13 h12₀ h13₀ c r l a hroot hord' hmeas
      (ae_kernel_deathEvent_finDP h13 ver ch c r l a j hx hs hD27 hcaps (ae_candLife_pos_succ h13 c r l a hord')
        (hexp j))
  filter_upwards [ae_all_iff.2 hZ, hD27, hcaps, hGTs.2.2,
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

/-- **D46's death clause in the datum form, positive lifetime, at every admissible root** (strictly ordered
histories) of a version family and a choice family. -/
def DeathExportFamilyDP (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    (h : GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) → ∀ a j : ℕ,
      GW2Pv.StageDeathExportXDP c r l a (instX h13 ver ch Ω c r l a j h.1) (ver Ω c r l a).R (ver Ω c r l a).V
        (rootPt r.1)

/-- **BUF's `DeathThrXStatement` at roots `0` and strictly ordered histories** (`GW2Ny.DeathThrXStatementS` with the
root guard `rootPt r.1 = 0`). -/
def DeathThrXStatementS0 (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (h : GoodRoot c r), rootPt r.1 = 0 →
    (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∀ Wc : ℝ≥0 → ℝ, IsCanonXN c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc →
      deathClockX c r l a ξ < ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)
        (schedW c r l a · ξ) (schedTr c r l a ξ) (c.α ξ)) →
      ∀ j : ℕ, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V j ξ →
        ∃ u : ℝ≥0, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) + u = deathClockX c r l a ξ ∧
          StageThresholdN c.κ ((ch Ω c r l a).β ((instX h13 ver ch Ω c r l a j h.1).srecX c r l (rootPt r.1) ξ))
            (stgDrv Wc (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
              ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ)) u

/-- The guarded statement gives the root-`0` one. -/
theorem DeathThrXStatementS.toS0 {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}}
    {ch : SchedChoiceFamily.{u}} (hS : GW2Ny.DeathThrXStatementS h13 ver ch) : DeathThrXStatementS0 h13 ver ch :=
  fun Ω _ _ c r l a h hr0 hord => hS Ω c r l a h (Or.inl hr0) hord

/-- **BUF's `DeathThrXStatement` (admissible roots, strictly ordered histories) from the positive-lifetime death
clause** (`DeathExportFamilyDP`; D72). -/
theorem deathThrX_of_exportDP_fin (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (ver : SchedVerXFamily.{u})
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
    (hexp : DeathExportFamilyDP h13 ver ch) : GW2Ny.DeathThrXStatementS h13 ver ch := by
  intro Ω _ _ c r l a h hroot hord'
  have hord : GW2Sdx.HistOrdered c r l := Gm.timeOrdered_of_pairwise_lt hord'
  exact deathThrX_hist h12 h13 h12₀ h13₀ ver ch c r l a h hroot hord' (hword Ω c r l hord h a)
    (hD27 Ω c r l a h hord) (hcaps Ω c r l a h hord) fun j => hexp Ω c r l hord' h hroot a j

/-- **BUF's `DeathThrXStatement` at the top's family, root `0`, with NO open input** (D72): the stop-capped family,
GEOM2's word map, STAGEMEAN's landed positive-lifetime death clause `GW2Pv.deathExportFamilyDP0_stop`. -/
theorem deathThrX_stop_root0 (cw : Wire.T14Cur.CfWord.{u})
    (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r)) :
    DeathThrXStatementS0 Wire.T14Asm7.h13 (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13)
      (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw)) := by
  intro Ω _ _ c r l a h hr0 hord'
  have hTO : GW2Sdx.HistOrdered c r l := Gm.timeOrdered_of_pairwise_lt hord'
  have hβ := Wire.T14Cur.hword_baseWm cw Ω c r l hTO h a
  rw [← GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a] at hβ
  exact deathThrX_hist Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ _ _ c r l a h
    (Or.inl hr0) hord' hβ (GW2Nx.hD27_stop Wire.T14Asm7.h13 Ω c r l a h hTO)
    (GW2Nx.hcaps_stop Wire.T14Asm7.h13 Ω c r l a h hTO)
    fun j => GW2Pv.deathExportFamilyDP0_stop cw hcw Ω c r l hord' h hr0 a j

/-- **`deathThrX_stop_root0` at GEOM2's canonical counterflow word.** -/
theorem deathThrX_stop_root0_canon :
    DeathThrXStatementS0 Wire.T14Asm7.h13 (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13)
      (Wire.T14Cur.chL (Wire.T14Cur.baseWm GW2Nw.cfWordCanon)) :=
  deathThrX_stop_root0 GW2Nw.cfWordCanon GW2Nw.isCfWordOf_cfWordCanon

end InteractingSLE.Theorem14.GW2Nz
