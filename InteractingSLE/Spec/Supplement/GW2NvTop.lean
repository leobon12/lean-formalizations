/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NvKer

/-!
# BUF's `DeathThrXStatement` from D46's death clause (the kernel-to-`P` step)

Packet PROVE-GW2-NOTHR (round 4, decision D46). The measurable death event of every instance (`deathEvent`) holds under
the launch kernel (`ae_kernel_deathEvent`), so it holds `P`-almost surely. On the event, every canonical driver is the
versions' limit up to the death (`stageProxy_eq`), and the stage start and the death are read on the clock
(`stage_start_death`). This gives BUF's conclusion: an `u` with `S + u = deathClockX` and the stage threshold at `u`.

* **`measurableSet_deathFin`**;
* **`deathThrX_of_export`**: `DeathThrXStatementN h13 ver ch` (BUF's `GW2Bh.DeathThrXStatement`, verbatim) from D46's
  clause (`DeathExportFamily`) for every version family with D27's exhaustion below the death and caps below the
  death (RELDET's death family has both), and every choice family whose word map is measurable with countably many
  types;
* **`deathThrX_deathFamily`**: the same at RELDET's death family `schedVerXDeathFamily`, where both version
  conditions are RELDET's landed lemmas.

As stated, without the two version conditions, BUF's statement is false. If the caps do not reach the death, a
canonical driver is free after the last cap. It can continue, for instance, as a vertical slit, whose stage path has
no threshold at the death (an interior tip, `GW2Nt.not_threshold_of_tip_mem_H`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nv

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Supp8.Q3Stop
  MartChar.RealFlow GW2Nu Sec5.Prop513Schedule

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The finite-death event is measurable** (the candidate's lifetime and ROOTX's local events are measurable). -/
theorem measurableSet_deathFin (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (I : StageInst Ω) (hIW : I.W = schedW c r l a)
    (hIGT : I.GT = schedGTX h13 c r l a) : MeasurableSet (deathFin c r l a I (rootPt r.1)) := by
  set spec := GW2Olm.futSpec c r l a with hspec
  set k := GW2Olm.curIdx c r l with hkdef
  have hCm : Measurable (GW2Olm.futFam c r l a k) :=
    measurable_canonFam c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec) spec.1 c.hβA.1 c.hh.1 k
  have hζm : Measurable (candLife c r l a) := measurable_snd.comp hCm
  have hGTs := schedGTX_spec h13 c r l a
  unfold deathFin
  rw [hIW, hIGT]
  refine (measurableSet_le hζm measurable_const).inter (MeasurableSet.iUnion fun q => ?_)
  refine (measurableSet_lt (measurable_const.add (ENNReal.measurable_toNNReal.comp hζm)).coe_nnreal_ennreal
    measurable_const).inter ?_
  exact measurableSet_locEvX hGTs.1 (measurable_gb6Rec_src c) (fun r' _ => measurable_schedW c r l a r')
    hGTs.2.1 le_rfl

/-- **BUF's `DeathThrXStatement` from D46's death clause** (any version family with D27's exhaustion below the
death and caps below the death; any choice family with a measurable word map of countably many types). -/
theorem deathThrX_of_export (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (ch Ω c r l a).β ∧
        (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧ ∀ y, ((ch Ω c r l a).β y).IsSorted)
    (hD27 : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → ∀ t : ℝ≥0,
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
      (ae_kernel_deathEvent h13 ver ch c r l a j hx hs (hD27 Ω c r l a h hord) (hcaps Ω c r l a h hord)
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
      exists_cap_gt c r l a hGT hs hx hGξ hd (hD27ξ hgood hold) (hdN ▸ ENNReal.coe_lt_coe.2 hq)
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

/-- **BUF's `DeathThrXStatement` at RELDET's death family** from D46's death clause (any choice family with a
measurable word map of countably many types). -/
theorem deathThrX_deathFamily (h13 : Exist.Theorem13Statement.{u}) (ch : SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (ch Ω c r l a).β ∧
        (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧ ∀ y, ((ch Ω c r l a).β y).IsSorted)
    (hexp : DeathExportFamily h13 (schedVerXDeathFamily h13) ch) :
    DeathThrXStatementN h13 (schedVerXDeathFamily h13) ch :=
  deathThrX_of_export h13 (schedVerXDeathFamily h13) ch hword
    (fun _ _ _ c r l a h hord => schedVerXDeath_exhausts_death h13 c r l a h.1 h.2 hord)
    (fun _ _ _ c r l a h hord => schedVerXDeath_lt_deathClockX h13 c r l a h.1 h.2 hord) hexp

end InteractingSLE.Theorem14.GW2Nv
