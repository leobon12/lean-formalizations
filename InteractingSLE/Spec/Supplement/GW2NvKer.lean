/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NvPhys

/-!
# The death event under the launch kernel, from D46's death clause

Packet PROVE-GW2-NOTHR (round 4). Under the launch kernel of a launched candidate, D46's death clause gives the
measurable death event (`deathEvent`) of every root-`x` instance almost surely:

* for a zero-lifetime candidate (record in `launchBadRec`), SAFE's converse at the seed
  (`GW2Nv.ae_stage_seed_at_death`) gives the seed threshold of the stage word;
* for a positive lifetime, SAFE's converse at the death (`GW2Nu.ae_stage_threshold_at_death`) gives the threshold of
  the stage word along the clause's driver `Wd` at the death. The version limits (`stageProxy_eq`) read it through
  the versions, given D27's exhaustion and the caps below the death.

* **`stageThresholdN_zero_iff`**: at stage time `0` the stage threshold is the seed threshold;
* **`ae_kernel_deathEvent`**.
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
  GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip Supp8 MartChar.RealFlow GW2Nu Sec5.Prop513Schedule

/-- **At stage time `0` the stage threshold is the seed threshold** (any stage path from `0`). -/
theorem stageThresholdN_zero_iff {κ : ℝ} (β : BoundaryWord) {D : ℝ≥0 → ℝ} (hD : Continuous D) (hD0 : D 0 = 0) :
    StageThresholdN κ β D 0 ↔ SeedThr κ β := by
  have hDr : Continuous fun v : ℝ => D v.toNNReal := hD.comp continuous_real_toNNReal
  have hDr0 : (fun v : ℝ => D v.toNNReal) 0 = 0 := by simp [hD0]
  have hR : ∀ j, rightImg (fun v : ℝ => D v.toNNReal) (flowLineXR β.fn β.jumps 0 j) ((0 : ℝ≥0) : ℝ) =
      flowLineXR β.fn β.jumps 0 j := fun j => by
    rw [NNReal.coe_zero]
    exact rightImg_zero hDr hDr0 (Restart.FlowStopIdentCMI.flowLineXR_nonneg' _ _ 0 j)
  have hL : ∀ i, -rightImg (fun v : ℝ => -D v.toNNReal) (-flowLineXL β.fn β.jumps 0 i) ((0 : ℝ≥0) : ℝ) =
      flowLineXL β.fn β.jumps 0 i := fun i => by
    rw [NNReal.coe_zero]
    have h := rightImg_zero (w := fun v : ℝ => -D v.toNNReal) hDr.neg (by simp [hD0])
      (neg_nonneg.2 (Restart.FlowStopIdentCMI.flowLineXL_nonpos' β.fn β.jumps 0 i))
    rw [h, neg_neg]
  unfold StageThresholdN SeedThr
  simp only [hR, hL, hD0]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The death event of every root-`x` instance holds under the launch kernel** of a launched candidate, from
D46's death clause, D27's exhaustion below the death and the caps below the death. -/
theorem ae_kernel_deathEvent (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a j : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hD27 : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → ∀ t : ℝ≥0,
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
      exists_cap_gt c r l a hGT hs hx hGξ hd (hD27ξ hgood holdξ) (hdN ▸ ENNReal.coe_lt_coe.2 hq)
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

end InteractingSLE.Theorem14.GW2Nv
