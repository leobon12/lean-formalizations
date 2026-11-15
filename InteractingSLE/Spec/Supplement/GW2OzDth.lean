/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OwDth
import InteractingSLE.Spec.Supplement.GW2BxDth
import InteractingSLE.Spec.Supplement.GW2RePkg

/-!
# BUF's restated death threshold `DeathThrXStatementS3` at the top's family (decision D82 item 1)

Packet PROVE-GW2-NOTHR (round 12, D82 item 1). BUF restated the guarded death threshold with the driver premises its
proof reads (`GW2Bh.DeathThrXStatementS3`: continuity, `Wc 0 = 0`, the agreement with the versions for a positive
lifetime, a finite death clock) and proved it from the datum-form clause `GW2Ny.DeathExportFamilyD`, which is not
proved. Here it is proved from STAGEMEAN's PROVED positive-lifetime clause (`GW2Pu.deathExportFamilyDP_stop`), by the
route of `GW2Ow.deathThrX_oneVerS`:

* **`deathThrX3_hist`**: `GW2Nz.deathThrX_hist` (one history, positive-lifetime clause; a zero lifetime does not occur
  after a successful history, `GW2Nz.ae_candLife_pos_succ`) with S3's driver premises; the agreement is read only at
  a positive lifetime;
* **`deathThrX3_of_exportDP_fin`**: the family form (`GW2Nz.deathThrX_of_exportDP_fin` for S3);
* **`deathExportFamilyDP_stop_guard`**: STAGEMEAN's clause at the stop family on ASSEMBLE7's guarded base;
* **`deathThrX3_stop_guard`**, **`deathThrX3_chG`**: S3 at the stop family on the guarded base, and exactly BUF's
  consumed form `DeathThrXStatementS3 T14Asm7.h13 (schedVerXStopFamily T14Asm7.h13) T14Re.chG` (`GW2BxTop`'s
  `hdeath`), with NO hypotheses;
* **`deathThrX3_stopReindex_guard`**, **`deathThrX3_oneVerS`**, **`deathThrX3_stopPkgVer`**: S3 at the re-indexed
  forms (ROOTX's `oneVerS`, ASSEMBLE7's `stopPkgVer`), also with NO hypotheses.

R48: Theorems 1.2–1.3 appear only as the project's `T14Asm7` instances, as in `GW2OwDth`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Oz

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Supp8.Q3Stop
  MartChar.RealFlow GW2Nu GW2Nv GW2Ny GW2Nz Sec5.Prop513Schedule Sec5.CrossCond.StagedRepLater

/-- **BUF's restated death threshold at one history** (admissible root, strictly ordered history; the driver premises
of `GW2Bh.DeathThrXStatementS3`) from the positive-lifetime death clause (STAGEMEAN's `GW2Pv.StageDeathExportXDP`).
`GW2Nz.deathThrX_hist`'s proof, which reads the driver only through continuity, `Wc 0 = 0`, the agreement with the
versions at a positive lifetime and a finite death clock. -/
theorem deathThrX3_hist (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
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
      ∀ Wc : ℝ≥0 → ℝ, Continuous Wc → Wc 0 = 0 →
      (0 < candLife c r l a ξ → ∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < (ver Ω c r l a).V n ξ →
        (ver Ω c r l a).R n q ξ = Wc q) →
      deathClockX c r l a ξ < ⊤ →
      ∀ j : ℕ, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V j ξ →
        ∃ u : ℝ≥0, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) + u = deathClockX c r l a ξ ∧
          StageThresholdN c.κ ((ch Ω c r l a).β ((instX h13 ver ch Ω c r l a j h.1).srecX c r l (rootPt r.1) ξ))
            (stgDrv Wc (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
              ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ)) u
 := by
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
    with ξ hZξ hD27ξ hcapsξ hGTξ hbadξ hGξ hold Wc hWc hWc0 hagree' hd j hSV
  set I := instX h13 ver ch Ω c r l a j hx with hI
  have hgood : cfRec c.s c.W c.ζ ξ ∈ goodX x c.s := hGTξ.1 hGξ
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
    have hagree := hagree' hclpos
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

/-- **`DeathThrXStatementS3` (admissible roots, strictly ordered histories) from the positive-lifetime death clause**
(`GW2Nz.DeathExportFamilyDP`). -/
theorem deathThrX3_of_exportDP_fin (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
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
    (hexp : DeathExportFamilyDP h13 ver ch) : GW2Bh.DeathThrXStatementS3 h13 ver ch := by
  intro Ω _ _ c r l a h hroot hord'
  have hord : GW2Sdx.HistOrdered c r l := Gm.timeOrdered_of_pairwise_lt hord'
  exact deathThrX3_hist h12 h13 h12₀ h13₀ ver ch c r l a h hroot hord' (hword Ω c r l hord h a)
    (hD27 Ω c r l a h hord) (hcaps Ω c r l a h hord) fun j => hexp Ω c r l hord' h hroot a j

section Family

variable (cw : Wire.T14Cur.CfWord.{u})
  (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r))
  (φ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ)
  (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a))

include hcw in
/-- **STAGEMEAN's positive-lifetime death clause at the stop family, ASSEMBLE7's guarded base.** -/
theorem deathExportFamilyDP_stop_guard :
    DeathExportFamilyDP Wire.T14Asm7.h13 (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw))) := by
  intro Ω _ _ c r l hord h hroot a j
  have hg : Wire.T14Gd.Guard c r l := ⟨hord, hroot⟩
  have e := Wire.T14Gd.instC_guardBase_of_guard (Wire.T14Cur.baseWm cw) a
    (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) j h hg
  change GW2Pv.StageDeathExportXDP c r l a
    (Wire.T14Cur.instC (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13)
      (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw)) Ω c r l a j h) _ _ _
  rw [e]
  exact GW2Pu.deathExportFamilyDP_stop cw hcw Ω c r l hord h hroot a j

include hcw in
/-- **`DeathThrXStatementS3` at the stop family, ASSEMBLE7's guarded base**, every admissible root, strictly ordered
histories, with no open input. -/
theorem deathThrX3_stop_guard :
    GW2Bh.DeathThrXStatementS3 Wire.T14Asm7.h13 (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw))) :=
  deathThrX3_of_exportDP_fin Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ _ _
    (GW2Ow.hword_chL_guard cw) (GW2Nx.hD27_stop Wire.T14Asm7.h13) (GW2Nx.hcaps_stop Wire.T14Asm7.h13)
    (deathExportFamilyDP_stop_guard cw hcw)

include hcw in
/-- **`DeathThrXStatementS3` at every re-indexing of the stop family, ASSEMBLE7's guarded base**, with no open
input. -/
theorem deathThrX3_stopReindex_guard :
    GW2Bh.DeathThrXStatementS3 Wire.T14Asm7.h13
      (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw))) :=
  deathThrX3_of_exportDP_fin Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ _ _
    (GW2Ow.hword_chL_guard cw) (GW2Ow.hD27_reindex φ hφ) (GW2Ow.hcaps_reindex φ hφ)
    (GW2Ow.deathExportFamilyDP_reindex_guard cw hcw φ hφ)

end Family

/-- **BUF's consumed death threshold (`GW2BxTop`'s `hdeath`), with NO hypotheses**: `DeathThrXStatementS3` at the
stop family and the guarded base at `cwSrc` (`T14Re.chG`). -/
theorem deathThrX3_chG :
    GW2Bh.DeathThrXStatementS3 Wire.T14Asm7.h13 (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) Wire.T14Re.chG :=
  deathThrX3_stop_guard GW2Bh.cwSrc GW2Kt.isCfWordOf_cwSrc

/-- **`DeathThrXStatementS3` at the top's family (D68/D75)**: ROOTX's `T14Rp.oneVerS ψx` on the guarded base at
`cwSrc`, with NO hypotheses. -/
theorem deathThrX3_oneVerS (ψx : GW2Bh.PsiFam.{u}) :
    GW2Bh.DeathThrXStatementS3 Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx) Wire.T14Re.chG := by
  unfold Wire.T14Rp.oneVerS GW2Rl.verU
  exact deathThrX3_stopReindex_guard GW2Bh.cwSrc GW2Kt.isCfWordOf_cwSrc _ _

/-- **`DeathThrXStatementS3` at ASSEMBLE7's `GW2Kt.stopPkgVer ψx`** on the guarded base at `cwSrc`, with NO
hypotheses. -/
theorem deathThrX3_stopPkgVer (ψx : GW2Bh.PsiFam.{u}) :
    GW2Bh.DeathThrXStatementS3 Wire.T14Asm7.h13 (GW2Kt.stopPkgVer ψx) Wire.T14Re.chG := by
  unfold GW2Kt.stopPkgVer
  exact deathThrX3_stopReindex_guard GW2Bh.cwSrc GW2Kt.isCfWordOf_cwSrc _ _

end InteractingSLE.Theorem14.GW2Oz
