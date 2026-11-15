/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1VerTip
import InteractingSLE.Spec.Supplement.BW1VerClock
import InteractingSLE.Spec.Supplement.BW1VerGauge
import InteractingSLE.Spec.Supplement.BW1InMain

/-!
# Proposition BW1's samples are good samples

Packet PROVE-BW1-INPUTS2. In BW1's setting (`BW1Life.IsBW1Setting`, Theorem 1.3 allowed: BW1 serves Theorem 1.4, R48),
the record of the regularized first piece, a measurable continuous version of the physical counterflow driver with a
measurable trace version, and a measurable continuous version of the retained trace give, on a measurable set `M`
which contains almost all of the threshold event, good samples (`IsGoodSample`) whose record chart is BW1's state
chart and whose contact time is BW1's (`exists_bw1_data`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Ver

open Exist Exist.StagedLaw Exist.Staged Restart BW1Life Supp8.GB6 Supp8.GB6.ReadD Sec7.PocketTraversal

/-- **The record driver of the regularized piece is the stopped piece driver on the whole line.** -/
theorem rdrv_recOf_regularize_eq {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular e.1 (min t e.2))
    (hle : e.2 ≤ t) (hfin : e.2 ≠ ⊤) : rdrv (recOf t (StagedReg.regularize t e)) = BW1Prop.pieceDrv e := by
  funext x
  have hmin : min t e.2 = e.2 := min_eq_right hle
  have hsnd := StagedReg.regularize_snd t e
  have he' := StagedReg.isRegularDriver_regularize t e
  have hfin' : min t (StagedReg.regularize t e).2 ≠ ⊤ := by rw [hsnd, hmin]; exact hfin
  have heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min t e.2 → (StagedReg.regularize t e).1 s = e.1 s := fun s hs =>
    StagedReg.regularize_eq_of_le hP.1 hP.2.1 hs
  have hc' : ContinuousOn (StagedReg.regularize t e).1
      {s | (s : ℝ≥0∞) ≤ min t (StagedReg.regularize t e).2} := by
    rw [hsnd]
    exact hP.2.1.congr fun s hs => heq s hs
  have hg := isDrvGood_of_continuousOn_le he' hfin' hc'
  change LocalExt.histDrv (recHist (recOf t (StagedReg.regularize t e))) x.toNNReal = _
  rw [histDrv_recHist he' hg]
  change (StagedReg.regularize t e).1
      (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min t (StagedReg.regularize t e).2)).toNNReal =
    e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) e.2).toNNReal
  rw [hsnd, hmin]
  apply heq
  rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top hfin (min_le_right _ _)), hmin]
  exact min_le_right _ _

/-- The own time of the record of a regularized threshold piece is its lifetime. -/
theorem recS_recOf_regularize {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular e.1 (min t e.2))
    (hle : e.2 ≤ t) (hfin : e.2 ≠ ⊤) : recS (recOf t (StagedReg.regularize t e)) = e.2.toNNReal :=
  NNReal.coe_injective ((rtime_eq_recS _).symm.trans (BW1In.rdrv_recOf_regularize hP hle hfin).1)

/-- **The per-sample geometry of a threshold sample** (deterministic): the record is a good sample record with
retained trace the global trace of the stopped piece driver, BW1's state chart inverts to the record's Loewner map
and has a proper boundary extension, and BW1's contact time is the contact with the retained trace. -/
theorem bw1_sample {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {r : Bool}
    (hthr : BW1.EndsAtThresholdSide (ExplState.run κ b jumps (bwSpec gw2 θ t rest) D 1) r)
    (hP : GW1P.PieceRegular (D 0).1 (min t (D 0).2))
    (hNR : ∀ α : ℝ≥0 → ℂ, IsGeneratingTrace (D 0).1 (D 0).2 α → ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < (D 0).2 →
      α v ≠ 0)
    {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsGeneratingTrace w ⊤ γ)
    (htr : Tendsto (fun s => ‖γ s‖) atTop atTop) :
    IsGoodSample (recOf t (StagedReg.regularize t (D 0)))
        (fun s => LP.traceAt s (fun u => rdrv (recOf t (StagedReg.regularize t (D 0))) u)) w γ ∧
      (BW1.stateChart (ExplState.run κ b jumps (bwSpec gw2 θ t rest) D 1)).2.1 =
        QuantumZipper.fwdMapInv (rdrv (recOf t (StagedReg.regularize t (D 0))))
          (recS (recOf t (StagedReg.regularize t (D 0)))) ∧
      GW1P.HasProperBdryExt (BW1.stateChart (ExplState.run κ b jumps (bwSpec gw2 θ t rest) D 1)) ∧
      firstTipTime infinitySourceChart w (SB.prefixPhysSet κ b jumps (bwSpec gw2 θ t rest) D 1) =
        contactT γ (fun s => LP.traceAt s (fun u => rdrv (recOf t (StagedReg.regularize t (D 0))) u))
          (recS (recOf t (StagedReg.regularize t (D 0)))) := by
  have hthr' : BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 (D 0) θ t) r := hthr
  have hle := BW1Prop.le_of_endsAtThresholdSide (s := ExplState.init 0) (k := 0) hthr'
  have hfin := BW1Prop.ne_top_of_endsAtThresholdSide (s := ExplState.init 0) (k := 0) hthr'
  have hmin : min t (D 0).2 = (D 0).2 := min_eq_right hle
  obtain ⟨α, hα, -⟩ := hP.2.2
  have hα₂ : IsGeneratingTrace (D 0).1 (D 0).2 α := by rwa [hmin] at hα
  obtain ⟨-, hS0, hUc, hU0, hchart, -, -, αr, hαr, hαeq, -, hret⟩ :=
    BW1Prop.bw1_piece_geometry hP hα (hNR α hα₂) hthr'
  set e := D 0 with he
  set ζ : ℝ≥0 := e.2.toNNReal with hζ
  set rc := recOf t (StagedReg.regularize t e) with hrc
  have hrd : rdrv rc = BW1Prop.pieceDrv e := rdrv_recOf_regularize_eq hP hle hfin
  have hrs : recS rc = ζ := recS_recOf_regularize hP hle hfin
  have hUnn : ∀ x : ℝ, BW1Prop.pieceDrv e (x.toNNReal : ℝ) = BW1Prop.pieceDrv e x := fun x => by
    simp only [BW1Prop.pieceDrv, Real.toNNReal_coe]
  have hΓg := BW1In.isGeneratingTrace_of_isLoewnerTrace hUnn hαr
  have hpath : (fun u : ℝ≥0 => rdrv rc u) = fun s : ℝ≥0 => BW1Prop.pieceDrv e s := by rw [hrd]
  have hA : (fun s => LP.traceAt s (fun u => rdrv rc u)) = fun s : ℝ≥0 => αr s := by
    funext s
    rw [hpath]
    exact LP.traceAt_eq_of_isGeneratingTrace hΓg (hUc.comp NNReal.continuous_coe).continuousOn hU0
      ENNReal.coe_lt_top
  have hAα : ∀ s : ℝ≥0, s ≤ ζ → αr s = α s := fun s hs => by
    rw [hαeq s ⟨s.coe_nonneg, by exact_mod_cast hs⟩, Real.toNNReal_coe]
  refine ⟨⟨by rw [hrs]; exact hS0, by rw [hrd, hrs]; exact hret, by rw [hA, hpath]; exact hΓg, hw, hw0, hγ, htr⟩,
    by rw [hrd, hrs]; exact hchart, ?_, ?_⟩
  · have hS : min t e.2 ≠ ⊤ := by rw [hmin]; exact hfin
    have hceq : BW1.stateChart (ExplState.run κ b jumps (bwSpec gw2 θ t rest) D 1) =
        (Chart.id.recenter 0).loewner
          (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal)
          (((min t e.2).toNNReal : ℝ≥0) : ℝ) := chart_launch (ExplState.init 0) 0 e θ t hS
    rw [hceq]
    exact (GW1P.hasProperBdryExt_recenter_id 0).loewner_stopped hP hS
  · have hWα : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ e.2} := by
      have h := (show GW1P.PieceRegular e.1 (min t e.2) from hP).2.1
      rwa [hmin] at h
    rw [BW1Prop.firstTipTime_prefixPhysSet_eq hle hfin hα₂ hWα (show GW1P.PieceRegular e.1 (min t e.2)
      from hP).1 hγ hw hw0, hrs, hA]
    unfold contactT
    congr 1
    refine image_congr fun s hs => ?_
    show ((α s : ℂ) : OnePoint ℂ) = ((αr s : ℂ) : OnePoint ℂ)
    rw [hAα s hs.2]

/-- **BW1's data for the relative coordinates.** In BW1's setting (with Theorem 1.3 for the traces): the record, a
measurable record event `TS` of the threshold event, a measurable continuous version `Wd` of the counterflow driver, a
measurable continuous version `Γ` of its trace, a measurable continuous version `A` of the retained trace, and a
measurable set `M ⊆ rec⁻¹ TS` containing almost all of `rec⁻¹ TS`, on which every sample is good, the record chart is
BW1's state chart (with a proper boundary extension) and the contact time is BW1's. -/
theorem exists_bw1_data (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool}
    {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) (r : Bool) :
    ∃ (TS : Set RecData) (Wd : ℝ≥0 → Ω → ℝ) (Γ A : Ω → ℝ≥0 → ℂ) (M : Set Ω),
      Measurable (bwRec κ b jumps (bwSpec gw2 θ t rest) E) ∧ MeasurableSet TS ∧
      (∀ ω, Continuous (Γ ω)) ∧ (∀ ω, Continuous (A ω)) ∧ (∀ s, Measurable fun ω => Γ ω s) ∧
      (∀ s, Measurable fun ω => A ω s) ∧ MeasurableSet M ∧
      (∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔
        bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) ∧
      (∀ᵐ ω ∂P, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS → ω ∈ M) ∧
      ∀ ω ∈ M, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS ∧
        IsGoodSample (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω) (A ω) (Wd · ω) (Γ ω) ∧
        (∀ s, W' s ω = Wd s ω) ∧
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E ω).2.1 = QuantumZipper.fwdMapInv
          (rdrv (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) (recS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) ∧
        GW1P.HasProperBdryExt (bwChart κ b jumps (bwSpec gw2 θ t rest) E ω) ∧
        bwContact κ b jumps (bwSpec gw2 θ t rest) W' E ω =
          contactT (Γ ω) (A ω) (recS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) := by
  classical
  obtain ⟨hκ, hκ4, hb, hh, hcfW, hζ', -, hS⟩ := hset
  have hrec : Measurable (bwRec κ b jumps (bwSpec gw2 θ t rest) E) :=
    measurable_pastMap_one_last hb (StagedReg.measurable_regHist hS.1) fun j ω =>
      StagedReg.isRegularDriver_regHist j ω
  obtain ⟨TS, hTS, hFTS⟩ := exists_recordEvent h13 hκ hb hh hS r
  have hpiece := BW1Prop.ae_bw1_piece_hyps h13 hκ hκ4 hb hh hS
  have hW'tr := Sec7.StripSysPath.IsCenteredCounterflowDriver.ae_hasTrace h13 hκ hcfW
  obtain ⟨_, _, _, -, -, hflW⟩ := hcfW
  have hW'reg := ae_driver_zero_continuousOn hflW
  obtain ⟨_, 𝓕, _, _, _, _, hC⟩ := hflW
  have hcreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous (W' · ω) := by
    filter_upwards [hW'reg, hζ'] with ω hr hz
    refine ⟨hz, hr.1, continuousOn_univ.1 (hr.2.mono fun s _ => ?_)⟩
    rw [mem_ofPred_eq, hz]
    exact ENNReal.coe_lt_top
  obtain ⟨Wd, hWdm, hWdc, hWd0, hWdW⟩ := SourceC.exists_top_driver_version hC.1.2.1 hcreg
  let γ : Ω → ℝ≥0 → ℂ := fun ω => if hω : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (Wd · ω) ⊤ η ∧
    Tendsto (fun s => ‖η s‖) atTop atTop then hω.choose else 0
  have hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (Wd · ω) ⊤ (γ ω) ∧ Tendsto (fun s => ‖γ ω s‖) atTop atTop := by
    filter_upwards [hW'tr, hWdW, hζ'] with ω htr hw hz
    have hex : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (Wd · ω) ⊤ η ∧ Tendsto (fun s => ‖η s‖) atTop atTop := by
      obtain ⟨η, hη, hη'⟩ := htr
      rw [hz] at hη hη'
      have he : (Wd · ω) = (W' · ω) := funext hw
      exact ⟨η, he ▸ hη, hη' rfl⟩
    simp only [γ, hex, ↓reduceDIte]
    exact hex.choose_spec
  obtain ⟨Γ, hΓc, -, hΓm, hΓγ⟩ := SourceC.exists_top_trace_version hWdm hWdc hWd0 (hγ.mono fun _ h => h.1)
  let Good : Ω → Prop := fun ω => bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS →
    ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ∧ GW1P.PieceRegular (E 0 ω).1 (min t (E 0 ω).2) ∧
      (∀ α : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 (E 0 ω).2 α → ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < (E 0 ω).2 →
        α v ≠ 0) ∧
      (∀ s, W' s ω = Wd s ω) ∧ IsGeneratingTrace (Wd · ω) ⊤ (Γ ω) ∧ Tendsto (fun s => ‖Γ ω s‖) atTop atTop
  have hGood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hFTS, hpiece, hWdW, hγ, hΓγ] with ω hF hp hw hg hΓ hT
    refine ⟨hF.2 hT, hp.1, hp.2, fun s => (hw s).symm, ?_, ?_⟩
    · rw [hΓ]; exact hg.1
    · rw [hΓ]; exact hg.2
  obtain ⟨G, hGm, hGae, hG⟩ := SourceC.exists_measurable_good hGood
  let M : Set Ω := G ∩ bwRec κ b jumps (bwSpec gw2 θ t rest) E ⁻¹' TS
  have hMm : MeasurableSet M := hGm.inter (hrec hTS)
  let A : Ω → ℝ≥0 → ℂ := fun ω s =>
    if ω ∈ M then LP.traceAt s (fun u => rdrv (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω) u) else 0
  have hsam : ∀ ω ∈ M, IsGoodSample (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω) (A ω) (Wd · ω) (Γ ω) ∧
      (∀ s, W' s ω = Wd s ω) ∧
      (bwChart κ b jumps (bwSpec gw2 θ t rest) E ω).2.1 = QuantumZipper.fwdMapInv
        (rdrv (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) (recS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) ∧
      GW1P.HasProperBdryExt (bwChart κ b jumps (bwSpec gw2 θ t rest) E ω) ∧
      bwContact κ b jumps (bwSpec gw2 θ t rest) W' E ω =
        contactT (Γ ω) (A ω) (recS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) := by
    intro ω hω
    obtain ⟨hF, hP, hNR, hw, hgen, htr⟩ := hG ω hω.1 hω.2
    have hAω : A ω = fun s => LP.traceAt s (fun u => rdrv (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω) u) := by
      funext s
      simp only [A, hω, ↓reduceIte]
    have hW'e : (fun s => W' s ω) = (Wd · ω) := funext hw
    obtain ⟨hg, hch, hbd, hct⟩ := bw1_sample (D := fun j => E j ω) hF hP hNR (hWdc ω) (hWd0 ω) hgen htr
    rw [hAω, BW1In.bwRec_eq_recOf]
    refine ⟨hg, hw, hch, hbd, ?_⟩
    rw [← hct, ← hW'e]
    rfl
  refine ⟨TS, Wd, Γ, A, M, hrec, hTS, hΓc, fun ω => ?_, hΓm, fun s => ?_, hMm, hFTS, ?_, fun ω hω => ⟨hω.2, hsam ω hω⟩⟩
  · by_cases hω : ω ∈ M
    · exact (hsam ω hω).1.continuous_A
    · have he : A ω = fun _ => 0 := funext fun s => by simp only [A, hω, ↓reduceIte]
      rw [he]
      exact continuous_const
  · exact Measurable.ite hMm ((LP.measurable_traceAt s).comp
      (measurable_pi_iff.2 fun u => (measurable_rdrv_apply u).comp hrec)) measurable_const
  · filter_upwards [hGae] with ω hω hT
    exact ⟨hω, hT⟩

end InteractingSLE.Theorem14.BW1Ver
