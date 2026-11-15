/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PwExp
import InteractingSLE.Spec.Supplement.GW2PsmPairP
import InteractingSLE.Spec.Supplement.GW2OmxChain2
import InteractingSLE.Spec.Supplement.GW2NxMean

/-!
# `noThreshold` from STAGEMEAN's export in the datum form (decision D60)

Packet PROVE-GW2-NOTHR (round 7, decision D60 (A)). STAGEMEAN's export `GW2Pw.StageKernelExportLD` carries GB6's
launch datum `HasLaunchPairEq … ω₀` as a premise (the datum exists only inside the kernel chain). The consumers switch
from the one-level kernel-to-`P` step (`GW2Nt.ae_noThr_of_kernel`) to the kernel chain `GW2Omx.ae_of_kernel_curS`,
which supplies the datum on success. The chain needs a root `0` or of the first low right arc and a strictly ordered
history; the top reads only alive histories, which have both (`aliveS_root_cases`, `GW2Nx.aliveS_pairwise_lt`).

* **`ae_succ_of_kernel_curS`**: the chain on the success event (off success the kernel stays off success);
* **`noThresholdX_of_exportLD`**: `GW2Rz.NoThresholdX` of ROOTX's instance from `StageKernelExportLD` (round 3's
  `GW2Nu.noThresholdX_of_exportL` with the chain);
* `ExportFamilyLD`, **`hno_of_exportLD`**, **`hno_baseWm_of_exportLD`**: the top's `hno` at admissible roots and
  strictly ordered histories;
* **`aliveS_root_cases`**: the top's alive histories have admissible roots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Ny

open Restart Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 GW2Rd GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip MartChar.RealFlow
  Sec5.CrossCond.StagedRepLater Sec5.Prop513Schedule Supp8.GB6.RelDrv Supp8.RelSafe GW2Nt GW2Nu

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The kernel chain on the success event.** If, at `P`-almost every successful `ω₀` carrying GB6's datum, a
measurable event is almost sure under the conditional kernel of the earlier pieces, it holds `P`-almost surely on the
success event (admissible root, strictly ordered history). Off success the kernel stays off success. -/
theorem ae_succ_of_kernel_curS (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) {A : Set Ω} (hA : MeasurableSet A)
    (hker : ∀ᵐ ω₀ ∂c.P, AllSucc (specDelta (GW2Olm.futSpec c r l a)) (fun j => GW2Olm.futFam c r l a j ω₀)
        (GW2Olm.curIdx c r l) →
      HasLaunchPairEq c.κ c.b c.jumps c.P c.h c.W (GW2Olm.futSpec c r l a) (GW2Olm.futFam c r l a)
        (GW2Olm.curIdx c r l) ω₀ →
      ∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), ω ∈ A) :
    ∀ᵐ ω ∂c.P, AllSucc (specDelta (GW2Olm.futSpec c r l a)) (fun j => GW2Olm.futFam c r l a j ω)
      (GW2Olm.curIdx c r l) → ω ∈ A := by
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
  have hLS : MeasurableSet[GW2Olm.pastG c r l a] {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    measurableSet_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl (isFlowProg_spec x true L)
      (specDelta_ne_top _) E (by rw [hlen]; omega)
  have hA' : MeasurableSet {ω | ω ∈ {ω | AllSucc (specDelta spec) (fun j => E j ω) k} → ω ∈ A} := by
    have e : {ω | ω ∈ {ω | AllSucc (specDelta spec) (fun j => E j ω) k} → ω ∈ A} =
        {ω | AllSucc (specDelta spec) (fun j => E j ω) k}ᶜ ∪ A := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    exact (h𝒢 _ hLS).compl.union hA
  refine GW2Omx.ae_of_kernel_curS h12 h13 h12₀ h13₀ c r l a hroot hord hA' ?_
  filter_upwards [hker, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := c.P) h𝒢 hLS.compl] with ω₀ h1 h2 hcase
  by_cases hs : AllSucc (specDelta spec) (fun j => E j ω₀) k
  · have hdat := hcase ((GW2Psm.allSucc_futSpec_iff c r l a ω₀).2 hs)
    exact (h1 hs hdat).mono fun ω hω _ => hω
  · exact (h2 hs).mono fun ω (hω : ω ∈ {ω | AllSucc (specDelta spec) (fun j => E j ω) k}ᶜ) hωL => absurd hωL hω

theorem noThresholdX_of_exportLD (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord' : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => Supp8.Q3Stop.wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀)
    (hexp : GW2Pw.StageKernelExportLD c r l a (schedInstSX c r l a GT hA ch) (rootPt r.1)) :
    NoThresholdX (schedInstSX c r l a GT hA ch) c r l (rootPt r.1) := by
  have hord : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord'
  set I := schedInstSX c r l a GT hA ch with hI
  set x := rootPt r.1 with hxdef
  have hWm : ∀ t, Measurable (I.W t) := measurable_schedW c r l a
  have hver : IsRelVersionXR x c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1
  have hv : IsRelVersionX x c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hpre : Measurable (stgPreRecX x c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
    (measurable_stgPreRecX hGT.1 hs hx (measurable_gb6Rec_src c) hWm
      (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2) hver I.T).mono
      ((physFilt (measurable_gb6Rec_src c) hWm c.P).le I.T) le_rfl
  have hE : MeasurableSet I.E :=
    (hE₀.inter (measurableSet_succRec c r l)).inter (measurableSet_aliveRecX _ _ c.s hρ.1)
  have hrec : Measurable (I.srecX c r l x) := measurable_augRec (measurable_stageEncRec c r l) hpre
  have hDm : ∀ t, Measurable (I.drvX c x t) := measurable_stgRX hv.1 hv.2.1 hpre
  have hDc : ∀ ω, Continuous fun t => I.drvX c x t ω := fun ω => continuous_stgDrv (hv.2.1 ω) _
  have hcap : Measurable (I.capX c x) := measurable_stgVX hv.2.2.2.2.1 hpre
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
  have hLS : MeasurableSet[GW2Olm.pastG c r l a] {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    measurableSet_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl (isFlowProg_spec x true L)
      (specDelta_ne_top _) E (by rw [hlen]; omega)
  have hcov : ∀ᵐ ω ∂c.P, I.srecX c r l x ω ∈ I.E → ω ∈ {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    Eventually.of_forall fun ω hEω =>
      Gm.allSucc_future_of_oldSuccess c r l a ω ((augRec_mem_succRec_iff c r l _ ω).1 hEω.1.2)
  have hACk := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_not_threshold_afterCapX c r l a hx hs hord hGT hA hV ch)
  have hsucc := ae_succ_of_kernel_curS h12 h13 h12₀ h13₀ c r l a hroot hord'
    (measurableSet_noThr hrec hE hβ.1 hβ.2.1 hDm hDc hcap) ?_
  · filter_upwards [hsucc, hcov] with ω h1 h2 hEω
    exact h1 (h2 hEω) hEω
  filter_upwards [hexp, hACk] with ω₀ hX hAC₀ hL₀ hdat
  have hlaunch := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _) (fun j => E j ω₀) (show k < spec.2.2.length by omega)).1 hL₀
  obtain ⟨b, J, h, Wα, ζα, α, b', J', h', cw, W, ζ, γ, t₀, lam, F, hb, hb', hT, hfl, hα, hcf, hγ, hcwJ, hcwb,
    hid⟩ := hX hdat _ _ hlaunch
  have hG := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb hfl
  have hsafe := ae_no_threshold_gw2_at c.hκ c.hκ4 hb hG hb' hT hfl hα hcf hγ cw hcwJ hcwb
  filter_upwards [hsafe, hid, hAC₀] with ω hs1 hid1 hac hEω u hu
  by_cases hwin : ((I.T + candidateCap c r a : ℝ≥0) : ℝ≥0∞) < contactX x c.s I.γ c.α ω ∧
      clockX x c.s c.W c.ζ I.W (I.T + candidateCap c r a) ω <
        ((stgStartX x c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0) : ℝ) + u
  · exact hac hEω u hu hwin.1 hwin.2 (Restart.FlowStopIdentCMI.flowLineXL_nonpos' _ _ 0)
      (Restart.FlowStopIdentCMI.flowLineXR_nonneg' _ _ 0)
  · obtain ⟨hγH, hlam, hFfin, hdata, hw⟩ := hid1 hEω
    obtain ⟨hcof, hhull⟩ := hw u hu fun hc => le_of_not_gt fun hlt => hwin ⟨hc, hlt⟩
    set D : ℝ → ℝ := fun q : ℝ => I.drvX c x q.toNNReal ω with hDdef
    have hDc' : Continuous D := (hDc ω).comp continuous_real_toNNReal
    have hD0 : D 0 = 0 := by
      simp only [hDdef, Real.toNNReal_zero]
      exact GW2Rd.stgDrv_zero _ _
    set Rr : ℝ≥0 → ℝ := fun v => scD (lam ω) D v with hRrdef
    have hRrc : Continuous Rr := (GW2Nu.continuous_scD hDc').comp NNReal.continuous_coe
    have hRr0 : Rr 0 = 0 := by simp [hRrdef, scD, hD0]
    have hpos : (0 : ℝ) ≤ lam ω ^ 2 * u := mul_nonneg (sq_nonneg _) u.coe_nonneg
    have hcoe : (((lam ω ^ 2 * u).toNNReal : ℝ≥0) : ℝ) = lam ω ^ 2 * u := Real.coe_toNNReal _ hpos
    have hRrW : ∀ v ∈ Icc (0 : ℝ) (lam ω ^ 2 * u), Rr v.toNNReal = scD (lam ω) D v := fun v hv => by
      simp only [hRrdef, Real.coe_toNNReal _ hv.1]
    have hn := hs1 (t₀ ω) hγH Rr hRrc hRr0 (lam ω ^ 2 * u).toNNReal (by
      obtain ⟨t, ht, hlt⟩ := hcof
      exact ⟨t, ht, by rw [hcoe]; exact hlt⟩) (fun t ht hle => by
      have hle' : gb6Clock (t₀ ω) (regW (t₀ ω) Wα ζα) W ω t ≤ lam ω ^ 2 * u := by
        change ENNReal.ofReal _ ≤ ENNReal.ofReal _ at hle
        exact (ENNReal.ofReal_le_ofReal_iff hpos).1 hle
      rw [← hhull t ht hle']
      refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hRrc.comp continuous_real_toNNReal) (GW2Nu.continuous_scD hDc')
        (gb6Clock_nonneg _ _ _ _ _) fun v hv => ?_
      show scD (lam ω) D ((v.toNNReal : ℝ≥0) : ℝ) = scD (lam ω) D v
      rw [Real.coe_toNNReal _ hv.1])
    have h1 := not_threshold_stage_of_joint c.hκ hlam hFfin hdata (D := D) hDc' (Rr := Rr) hRrW hn
    simp only [hDdef, Real.toNNReal_coe] at h1
    exact h1


/-- **The datum-form export at every admissible root and strictly ordered history** of a version family and a base
family. -/
def ExportFamilyLD (ver : SchedVerXFamily.{u}) (base : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) → (h : GoodRoot c r) →
    (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) → ∀ a n : ℕ,
      GW2Pw.StageKernelExportLD c r l a (Wire.T14Cur.instC ver base Ω c r l a n h) (rootPt r.1)

/-- **The binder `hno` of Theorem 1.4's current top from the datum-form export**, at admissible roots and strictly
ordered histories (the histories and roots the top reads: `GW2Nx.aliveS_pairwise_lt`, `aliveS_root_cases`). -/
theorem hno_of_exportLD {ver : SchedVerXFamily.{u}} {base : SchedChoiceFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hexp : ExportFamilyLD ver base) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
      ∀ a n : ℕ, NoThresholdX (Wire.T14Cur.instC ver base Ω c r l a n h) c r l (rootPt r.1) := by
  intro Ω _ _ c r l hord h hroot a n
  have hTO : GW2Sdx.HistOrdered c r l := Gm.timeOrdered_of_pairwise_lt hord
  have hβ := hword Ω c r l hTO h a
  have hE := hE₀ Ω c r l hTO h a
  rw [← GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 base c r l a] at hβ
  rw [← GW2Rd.schedChoiceLinesX_E₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 base c r l a] at hE
  exact noThresholdX_of_exportLD Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ c r l a h.1
    h.2 hroot hord (schedGTX_spec Wire.T14Asm7.h13 c r l a) ((ver Ω c r l a).isA h.1 n) ((ver Ω c r l a).fin n)
    (Wire.T14Cur.chL base Ω c r l a) hβ hE (hexp Ω c r l hord h hroot a n)

/-- **`hno` for GEOM2's word-map family** `T14Cur.baseWm cw` from the datum-form export. -/
theorem hno_baseWm_of_exportLD {ver : SchedVerXFamily.{u}} (cw : Wire.T14Cur.CfWord.{u})
    (hexp : ExportFamilyLD ver (Wire.T14Cur.baseWm cw)) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
      ∀ a n : ℕ, NoThresholdX (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h) c r l (rootPt r.1) :=
  hno_of_exportLD (Wire.T14Cur.hword_baseWm cw) (Wire.T14Cur.hE₀_baseWm cw) hexp

/-- **The top's alive histories have admissible roots**: on J32's alive event over the scaled cover the sample lies
in the cover event, whose root is admissible (`GW2Omx.rootPt_cases_of_seedOK`). -/
theorem aliveS_root_cases (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) {ω : Ω}
    (h : ω ∈ Wire.T14Cur.aliveS gap Ω c r l) : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps :=
  GW2Omx.rootPt_cases_of_seedOK c r
    (RootJ32.alive_spec c r l ω (GW2Sdz.alive_scaled_subset gap Ω c r l h)).1.1

end InteractingSLE.Theorem14.GW2Ny
