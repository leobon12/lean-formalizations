/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TlWord
import InteractingSLE.Spec.Supplement.GW2ScheduleLaw

/-!
# N4 item 1 in launch coordinates, part 6: the candidate's death with the canonical launch word

Packet PROVE-GW2-RELDET (decision D20). `GW2Rd.ae_candidate_life_badEntrance` reads the death against the bad set of
the launch word that the frozen `StageOK` provides EXISTENTIALLY. The death gauge reads the canonical word
(`GW2Schedule.canonWord`). Here the same statements with that word named:

* **`stageOK_canonWord`**: `GW2Schedule.stageOK_canon` with its witness word exhibited — at a launch, under the
  conditional law of the past, the canonical piece is the flow-line driver of the field read in the launch chart, for
  the boundary data of the canonical word at the conditioning sample (the proof of `stageOK_canon`, unchanged);
* **`ae_candidate_life_canonWord`**: for `P`-a.e. `ω₀`, at a launch of the candidate, under `ν = condExpKernel P pastG
  ω₀`, almost every sample's candidate has a generating trace on its lifetime that, at a positive lifetime, stays off
  the closed bad set of the canonical word of `ω₀` before the lifetime and is at a bad point at a finite lifetime.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart LQGMetric GW2Schedule

section Law

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (c₀ : BoundaryWord) (θ : ℕ → ℝ) (Δ : ℕ → ℝ≥0∞)
variable {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **`stageOK_canon` with the witness word named**: at a launch, under the conditional law of the past, the canonical
piece is the flow-line driver of the field read in the launch chart, for the data of the canonical word at the
conditioning sample. (The proof is that of `GW2Schedule.stageOK_canon`.) -/
theorem stageOK_canonWord (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {k : ℕ}
    (hW : IsStageWitness κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k
      (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k) (canonField hκ h12p βA c₀ θ Δ spec.1 h k)) :
    ∀ᵐ ω₀ ∂P, ∀ (cL : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps spec (fun j => canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω₀) (k + 1)).2.2.2.1 k =
        some (cL, θ') →
      ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport cL 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsFlowLineDriver κ (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k ω₀).fn
          (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k ω₀).jumps θ'
          (condExpKernel P (pastSigma κ b jumps spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k) ω₀) h'
          (fun t ω => (canonFam hκ h12p βA c₀ θ Δ spec.1 h k ω).1 t)
          (fun ω => (canonFam hκ h12p βA c₀ θ Δ spec.1 h k ω).2) := by
  classical
  set C := canonFam hκ h12p βA c₀ θ Δ spec.1 h with hCdef
  have hCm : ∀ j, Measurable (C j) := fun j => measurable_canonFam hκ h12p βA c₀ θ Δ spec.1 hβA.1 hh.1 j
  have hCreg : ∀ j ω, IsRegularDriver (C j ω) := fun j ω => isRegularDriver_canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω
  have hpm : Measurable (pastMap κ b jumps spec C k) :=
    measurable_pastMap runMeasStatement hb spec (fun j _ => hCm j) (fun j _ => hCreg j) k le_rfl
  have h𝒢 : pastSigma κ b jumps spec C k ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  rcases lt_or_ge k spec.2.2.length with hk | hk
  swap
  · refine Eventually.of_forall fun ω₀ cL θ' hl => ?_
    rw [launch_eq_none_of_le _ hk] at hl
    exact absurd hl (by simp)
  have hL := measurableSet_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ C hk.le
  have : StandardBorelSpace (PastData k) := inferInstance
  have : MeasurableSpace.CountablySeparated (PastData k) := inferInstance
  have hatom0 := ae_ae_eq_of_comap (P := P) hpm
  rw [← pastSigma_eq_comap] at hatom0
  filter_upwards [hW.2.2.1, hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL, hatom0,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1] with ω₀ hpath hgff hmem hatom hpathK cL θ' hl
  have hne : (ExplState.run κ b jumps spec (fun j => C j ω₀) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  have hs₀ : AllSucc Δ (fun j => C j ω₀) k := (launch_ne_none_iff θ Δ hgw hprog hΔ _ hk).1 hne
  have hl' := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun j => C j ω₀) hk).1 hs₀
  rw [hl'] at hl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
  obtain ⟨hconf, hlift, -⟩ := hpath hne
  rw [chart_run_eq θ Δ hgw hprog hΔ _ hk.le hs₀] at hconf hlift
  set cc := succChart spec.1 Δ (fun j => C j ω₀) k with hccdef
  set ν := condExpKernel P (pastSigma κ b jumps spec C k) ω₀ with hν
  set h' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω)
    with hh'def
  have hT' : ∀ ω, IsChartTransport cc 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'm : Measurable h' := (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hmem' := hmem hs₀
  have hYh' : ∀ᵐ ω ∂ν, canonField hκ h12p βA c₀ θ Δ spec.1 h k ω = h' ω := by
    filter_upwards [hmem', hatom, hpathK] with ω hω hpω hpathω
    have hrun : ExplState.run κ b jumps spec (fun j => C j ω) k = ExplState.run κ b jumps spec (fun j => C j ω₀) k :=
      run_eq_of_readRec_eq spec (fun j _ => hCreg j ω) (fun j _ => hCreg j ω₀) fun i hi => congrFun hpω ⟨i, hi⟩
    have hneω := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => C j ω) hk).2 hω
    obtain ⟨-, -, hTω⟩ := hpathω hneω
    rw [hrun, chart_run_eq θ Δ hgw hprog hΔ _ hk.le hs₀] at hTω
    exact hTω.unique hconf (hT' ω)
  have hgff' := isGFFWithBoundaryData_congr_ae (hgff hne) hh'm hYh'
  set w := canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k ω₀ with hw
  have hPC : IsPiecewiseConstantBoundaryData w.fn w.jumps := w.isPiecewiseConstantBoundaryData
  have hgff'' := isGFFWithBoundaryData_flowField hκ hPC 0 (θ k) hgff'
  have hCeq : ∀ᵐ ω ∂ν, C k ω = drvOf (detCode (paramΦ h12p hκ (flowLineNL w.fn w.jumps 0) (flowLineNR w.fn w.jumps 0))
      (((flowLineXL w.fn w.jumps 0, flowLineXR w.fn w.jumps 0),
        (flowLineRhoL κ w.fn w.jumps 0 (θ k), flowLineRhoR κ w.fn w.jumps 0 (θ k))),
        flowField 0 (θ k * QuantumZipper.chiC κ) (h' ω))) := by
    filter_upwards [hmem', hatom, hYh'] with ω hω hpω hYω
    have hword : (canonState hκ h12p βA c₀ spec.1 θ Δ (h ω) k).1 = w := by
      rw [← canonWord_eq hκ h12p βA c₀ θ Δ hgw hprog hΔ hk.le hω, hw, canonWord, canonWord, hpω]
    change wordDrv hκ h12p (θ k) (canonState hκ h12p βA c₀ spec.1 θ Δ (h ω) k).1
      (canonField hκ h12p βA c₀ θ Δ spec.1 h k ω) = _
    rw [hword, hYω]
    simp only [wordDrv, stagedDrv, wNL, wNR, wPad, truncWord_padFL]
  obtain ⟨𝓕, VL, VR, B, hcoup⟩ := isOptionalHullCoupling_drv h12p h13 hκ
    (Theorem15.isOrderedForceWord_flowLine _ _ 0) hgff'' (hCm k) hCeq
  exact ⟨h', hT', fun ω => flowField 0 (θ k * QuantumZipper.chiC κ) (h' ω), 𝓕, VL, VR, B,
    fun ω => isTranslateAddConst_flowField 0 _ (h' ω), hcoup⟩

end Law

/-! ### The candidate's death with the canonical word -/

section Death

open GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec7.StripSysPath

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The candidate's canonical launch word at a sample. -/
abbrev candWord (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    BoundaryWord :=
  canonWord c.hκ c.h12p c.βA c.c₀ (GW2Tip.specAngle (GW2Olm.futSpec c r l a))
    (GW2Tip.specDelta (GW2Olm.futSpec c r l a)) c.κ c.b c.jumps (GW2Olm.futSpec c r l a) c.h (GW2Olm.curIdx c r l) ω

/-- **The candidate's death against the bad set of its canonical launch word** (D10's argument under the conditional
law of the earlier pieces, Theorem 1.3; `ae_candidate_life_badEntrance` with the word named). -/
theorem ae_candidate_life_canonWord (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
      ∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀),
        ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 t)
            (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 η ∧
          (0 < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
            (∀ t : ℝ≥0, (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
              η t ∉ closure (SB.Vr.badSet (flowLineXL (candWord c r l a ω₀).fn (candWord c r l a ω₀).jumps 0)
                (flowLineXR (candWord c r l a ω₀).fn (candWord c r l a ω₀).jumps 0)
                (flowLineRhoL c.κ (candWord c r l a ω₀).fn (candWord c r l a ω₀).jumps 0 θ)
                (flowLineRhoR c.κ (candWord c r l a ω₀).fn (candWord c r l a ω₀).jumps 0 θ))) ∧
            ((GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 ≠ ⊤ →
              SB.Vq.IsBadPoint (flowLineXL (candWord c r l a ω₀).fn (candWord c r l a ω₀).jumps 0)
                (flowLineXR (candWord c r l a ω₀).fn (candWord c r l a ω₀).jumps 0)
                (flowLineRhoL c.κ (candWord c r l a ω₀).fn (candWord c r l a ω₀).jumps 0 θ)
                (flowLineRhoR c.κ (candWord c r l a ω₀).fn (candWord c r l a ω₀).jumps 0 θ)
                (η (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2.toNNReal))) := by
  classical
  set x := rootPt r.1 with hx
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (GW2Tip.specAngle spec) (GW2Tip.specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (GW2Tip.isFlowProg_spec x true L) (GW2Tip.specDelta_ne_top _)
  have hW := (canon_stageLaw c.hκ c.h12p c.βA c.c₀ (GW2Tip.specAngle spec) (GW2Tip.specDelta spec) h13 c.hβA c.hb
    c.hc₀J c.hc₀ c.hh (spec := spec) rfl (GW2Tip.isFlowProg_spec x true L) (GW2Tip.specDelta_ne_top _) k).1
  filter_upwards [stageOK_canonWord c.hκ c.h12p c.βA c.c₀ (GW2Tip.specAngle spec) (GW2Tip.specDelta spec) h13 c.hβA
      c.hb c.hh rfl (GW2Tip.isFlowProg_spec x true L) (GW2Tip.specDelta_ne_top _) hW,
    IsStagedHistory.ae_ae_hasTrace (theorem13LowStatement_of_theorem13 h13) c.hκ c.hκ4 hS k]
    with ω₀ hst htr cL θ hl
  obtain ⟨h', -, hWd⟩ := hst cL θ hl
  have hb' := (candWord c r l a ω₀).isPiecewiseConstantBoundaryData
  have hfl := isFlowLine_of_isFlowLineDriver hWd (htr cL θ hl)
  have hgff := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb' hWd
  filter_upwards [htr cL θ hl, SB.Vr.ae_notMem_closure_badSet c.hκ c.hκ4 hb' hgff hfl,
    SB.Vr.ae_tip_bad_of_isFlowLine hfl] with ω hω h1 h2
  refine ⟨hω.choose, hω.choose_spec.1, fun hζ0 => ⟨fun t ht => ?_, fun hζt => ?_⟩⟩
  · have := h1 hζ0 t ht
    simp only [Complex.ofReal_zero, sub_zero] at this
    split_ifs at this with hT
    · exact this
    · exact absurd hω hT
  · have := h2 hζ0 hζt
    simp only [Complex.ofReal_zero, sub_zero] at this
    split_ifs at this with hT
    · exact this
    · exact absurd hω hT

end Death

end InteractingSLE.Theorem14.GW2Rd
