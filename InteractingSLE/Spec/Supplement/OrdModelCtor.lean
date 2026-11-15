/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdModelCarrier
import InteractingSLE.Spec.Supplement.OrdModelFrz
import InteractingSLE.Spec.Supplement.OrdAStopModel
import InteractingSLE.Spec.Supplement.OrdModelRule

/-!
# A-stopped models from source processes

Packet PROVE-T15-ASTOP2. **`nonempty_stoppedModelTransferJ_of_aStop`** builds the A-stopped model with an initial code
(`OrdAStop.StoppedModelTransferJ`, PROVE-T15-ASTOP) of a stopped process on an arbitrary source `Ω : Type v`, on an
event `M` with `P M ≠ 0`, from:

* the source processes in a filtration `𝓗`: a word `c` and the four chart end points `E` of the A-set (both known at
  time `0`), the field `Hc`, a continuous driver `W` from `0`, a stop `V`, a path `γ` continuous on `[0, V]` from `0`;
* the stopped-K2 laws (S), (L) of the typed word on `M` (field `flowField 0 (θχ) Hc`), integrable pairings, the type;
* the pathwise A-stop facts on `M`, almost surely: `γ` generates `W` up to `V`, `0 < V ≤ thr`, `γ t ∉ aStopSet E` at
  positive times before `V`, and a finite `V` is the threshold of the word or `γ V ∈ aStopSet E`.

The model is the conditional law of `M` pushed to `OrdCanonSpace = RetCanonSpace × Ends` (PROVE-RETPLUMB's canonical
reader plus the end points) with the image filtration; its code is `ordCode = codeEquiv (word, end points)`. Unlike
PROVE-T15-RET's `RetLeaf.stoppedModelTransfer_of_traceInputs` (A ∪ ℝ stop: the trace is interior before its lifetime),
the trace may touch the real line before the stop; the stop is announced in the killed driving filtration enlarged by
the code (`OrdAStop.exists_isAnnouncingSeq_aStop`, blowup of `1 / dist(γ, I_A)`), with the original end announced by
the threshold of the frozen driver (`exists_isAnnouncingSeq_thr_frzDrv`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdModel

open LQGMetric (DistOn TestOn)
open Restart Restart.RetAux79 Restart.RetLeaf Sec7.PocketTraversal Restart.DomainMarkov
  Restart.DomainMarkov.K2 Restart.FCDet OrdAStop

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem measurable_of_le_stopping {𝓗 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞}
    (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t}) : Measurable V := by
  refine measurable_of_Iic fun t => ?_
  induction t using ENNReal.recTopCoe with
  | top => simp only [Iic_top, preimage_univ, MeasurableSet.univ]
  | coe t => exact 𝓗.le t _ (hVs t)

/-- **An A-stopped model with an initial code from source processes**, whose lifetime is the A-stop rule of its killed
history given its code (`HasCodeHistoryRule`, the R79-safe form). -/
theorem exists_stoppedModelTransferJ_rule_of_aStop {κ θ : ℝ} (a : ForceWordType)
    {𝓗 : Filtration ℝ≥0 mΩ} {M : Set Ω} (hM : MeasurableSet[𝓗 0] M) (hPM : P M ≠ 0)
    {c : Ω → BoundaryWord} (hc : Measurable[𝓗 0] c)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0) (hWa : StronglyAdapted 𝓗 W)
    {V : Ω → ℝ≥0∞} (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t})
    {γ : Ω → ℝ≥0 → ℂ} (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω}) (hγ0 : ∀ ω, γ ω 0 = 0)
    {E : Ω → Ends} (hE : Measurable[𝓗 0] E) {Sd : Ω → ℝ} (hSd : Measurable[𝓗 0] Sd)
    (htype : ∀ᵐ ω ∂P, ω ∈ M → c ω ∈ typeSet κ θ a.nL a.nR a.rhoL a.rhoR)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω) φ) (P.restrict M))
    (hS : HasSafeLaw κ a.rhoL a.rhoR P 𝓗 M V W
      (geomLW W fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω))
      (geomRW W fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω))
      fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω))
    (hL : HasSafeMembers P 𝓗 M V W fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω))
    (hg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (V ω) (γ ω))
    (hVpos : ∀ᵐ ω ∂P, ω ∈ M → 0 < V ω)
    (hthr : ∀ᵐ ω ∂P, ω ∈ M → V ω ≤ thr a.rhoL a.rhoR W
      (fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) (fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) ω)
    (hoff : ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → γ ω t ∉ aStopSet (E ω))
    (hend : ∀ᵐ ω ∂P, ω ∈ M → V ω ≠ ⊤ → V ω = thr a.rhoL a.rhoR W
      (fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) (fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) ω ∨
        γ ω (V ω).toNNReal ∈ aStopSet (E ω)) :
    ∃ T : StoppedModelTransferJ κ θ P M c Hc V γ, HasCodeHistoryRule T.model ∧
      ∃ seed : T.model.space → ℝ, Measurable[T.model.data.filt 0] seed ∧ ∀ ω, seed (T.read ω) = Sd ω := by
  classical
  set xL : Ω → Fin a.nL → ℝ := fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω) with hxLdef
  set xR : Ω → Fin a.nR → ℝ := fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω) with hxRdef
  set X : Ω → DistOn upperHalfPlaneOpens := fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω)
    with hXdef
  have hMm := 𝓗.le 0 _ hM
  have hVm : Measurable V := measurable_of_le_stopping hVs
  obtain ⟨Y, hY, hYsp⟩ := exists_retCanonicalReader (c := c) (Hc := Hc) (W := W) (V := V) (γ := γ)
    (hc.mono (𝓗.le 0) le_rfl) hHc (fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl) hWc hW0 hVm hγm hγc hγ0
  let Y' : Ω → OrdCanonSpace := fun ω => (Y ω, E ω, Sd ω)
  have hY' : Measurable Y' := hY.prodMk ((hE.mono (𝓗.le 0) le_rfl).prodMk (hSd.mono (𝓗.le 0) le_rfl))
  let Q := (P[|M]).map Y'
  have hQ : IsProbabilityMeasure Q := by
    let _ : IsProbabilityMeasure (P[|M]) := cond_isProbabilityMeasure hPM
    exact (Measure.isProbabilityMeasure_map_iff hY'.aemeasurable).2 inferInstance
  let 𝓕 := retImageFiltration Y' 𝓗
  have hWY : ∀ ω t, ordDrv t (Y' ω) = W t ω := fun ω t => (hYsp ω).2.2.2.1 t
  have hVY : ∀ ω, RetCanonSpace.life (Y' ω).1 = V ω := fun ω => (hYsp ω).2.2.1
  have hcY : ∀ ω, RetCanonSpace.word (Y' ω).1 = c ω := fun ω => (hYsp ω).1
  have hLY : ∀ ω, ordXL κ θ a (Y' ω) = xL ω := fun ω => by
    show typeXL κ θ a.nL a.nR a.rhoL a.rhoR (RetCanonSpace.word (Y ω)) = _
    rw [(hYsp ω).1]
  have hRY : ∀ ω, ordXR κ θ a (Y' ω) = xR ω := fun ω => by
    show typeXR κ θ a.nL a.nR a.rhoL a.rhoR (RetCanonSpace.word (Y ω)) = _
    rw [(hYsp ω).1]
  have hthrY : ∀ ω, ordThr κ θ a (Y' ω) = thr a.rhoL a.rhoR W xL xR ω := fun ω =>
    FCDet.thr_congr (hWY ω) (hLY ω) (hRY ω)
  -- coordinates on the carrier
  have hcw : Measurable[𝓕 0] fun s : OrdCanonSpace => RetCanonSpace.word s.1 := by
    apply measurable_from_retImageFiltration (RetCanonSpace.measurable_word.comp measurable_fst)
    convert hc using 1
    funext ω
    exact hcY ω
  have hxLm : Measurable[𝓕 0] (ordXL κ θ a) := (measurable_typeXL κ θ a.nL a.nR a.rhoL a.rhoR).comp hcw
  have hxRm : Measurable[𝓕 0] (ordXR κ θ a) := (measurable_typeXR κ θ a.nL a.nR a.rhoL a.rhoR).comp hcw
  have hWap : StronglyAdapted 𝓕 ordDrv := fun t => by
    apply Measurable.stronglyMeasurable
    apply measurable_from_retImageFiltration ((RetCanonSpace.measurable_driver t).comp measurable_fst)
    convert (hWa t).measurable using 1
    funext ω
    exact hWY ω t
  have hVsp : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {s : OrdCanonSpace | RetCanonSpace.life s.1 ≤ t} := by
    apply isStoppingTime_retImageFiltration (RetCanonSpace.measurable_life.comp measurable_fst)
    intro t
    have e : {ω | (RetCanonSpace.life ∘ Prod.fst) (Y' ω) ≤ (t : ℝ≥0∞)} = {ω | V ω ≤ t} := Set.ext fun ω => by
      simp only [mem_ofPred_eq, Function.comp_apply, Y', (hYsp ω).2.2.1]
    exact e ▸ hVs t
  have hcode : Measurable[𝓕 0] ordCode := by
    apply measurable_from_retImageFiltration measurable_ordCode
    convert codeEquiv.measurable.comp (hc.prodMk hE) using 1
    funext ω
    simp only [Function.comp_apply, ordCode, hcY, Y']
  let Z : OrdCanonSpace → DistOn upperHalfPlaneOpens := fun s =>
    Exist.flowField 0 (θ * QuantumZipper.chiC κ) (RetCanonSpace.field s.1)
  have hZm : Measurable Z :=
    (Exist.measurable_flowField 0 _).comp (RetCanonSpace.measurable_field.comp measurable_fst)
  have hZY : ∀ ω, Z (Y' ω) = X ω := fun ω => by
    show Exist.flowField 0 _ (RetCanonSpace.field (Y ω)) = _
    rw [(hYsp ω).2.1]
  -- the type, the pairings, the good event on the model law
  have htyp : ∀ᵐ s ∂Q, IsFlowType κ θ (RetCanonSpace.word s.1) (ordXL κ θ a s) (ordXR κ θ a s) a.rhoL a.rhoR := by
    have hp : ∀ᵐ s ∂Q, RetCanonSpace.word s.1 ∈ typeSet κ θ a.nL a.nR a.rhoL a.rhoR := by
      apply (ae_map_iff hY'.aemeasurable ((RetCanonSpace.measurable_word.comp measurable_fst)
        (measurableSet_typeSet κ θ a.nL a.nR a.rhoL a.rhoR))).2
      apply ae_cond_of_ae_imp hMm
      filter_upwards [htype] with ω h hωM
      simpa only [Function.comp_apply, Y', (hYsp ω).1] using h hωM
    filter_upwards [hp] with s hs
    exact isFlowType_of_mem_typeSet hs
  have hi : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun s => Z s φ) Q := by
    intro φ
    have hm : Measurable fun s => Z s φ :=
      ((measurable_pi_apply φ).comp (Measurable.of_comap_le le_rfl)).comp hZm
    rw [integrable_map_measure hm.aestronglyMeasurable hY'.aemeasurable]
    have he : (fun ω => Z (Y' ω) φ) = fun ω => X ω φ :=
      funext fun ω => congrArg (fun H : DistOn upperHalfPlaneOpens => H φ) (hZY ω)
    change Integrable (fun ω => Z (Y' ω) φ) (P[|M])
    rw [he, ProbabilityTheory.cond]
    exact (hint φ).smul_measure (ENNReal.inv_ne_top.2 hPM)
  have hgood : ∀ᵐ s ∂Q, s ∈ ordGood κ θ a := by
    apply (ae_map_iff hY'.aemeasurable (measurableSet_ordGood κ θ a)).2
    apply ae_cond_of_ae_imp hMm
    filter_upwards [hg, hVpos, hthr, hoff, hend] with ω hgω hpω hthω hoffω hendω hωM
    have hWf : (fun t => ordDrv t (Y' ω)) = (W · ω) := funext (hWY ω)
    have htr : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → RetCanonSpace.trace (Y' ω).1 t = γ ω t :=
      (hYsp ω).2.2.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show IsGeneratingTrace (fun t => ordDrv t (Y' ω)) (RetCanonSpace.life (Y' ω).1) _
      rw [hWf, hVY]
      exact isGeneratingTrace_congr_le (hgω hωM) htr
    · rw [hVY]
      exact hpω hωM
    · rw [hVY, hthrY]
      exact hthω hωM
    · intro t ht0 ht
      rw [hVY] at ht
      rw [htr t ht.le]
      exact ((isClosed_aStopSet _).notMem_iff_infDist_pos (aStopSet_nonempty _)).1 (hoffω hωM t ht0 ht)
    · intro htop
      rw [hVY] at htop ⊢
      rw [hthrY, htr _ ENNReal.coe_toNNReal_le_self]
      rcases hendω hωM htop with h | h
      · exact Or.inl h
      · exact Or.inr (((isClosed_aStopSet _).mem_iff_infDist_zero (aStopSet_nonempty _)).1 h)
  -- the announcement of the A-stop in the enlarged killed driving filtration
  have hXP := isMeasurableKilledDriving_geom hWap continuous_ordDrv hxLm hxRm hVsp
  set gL : ℝ → Fin a.nL → ℝ := fun e => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (codeWord e) with hgLdef
  set gR : ℝ → Fin a.nR → ℝ := fun e => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (codeWord e) with hgRdef
  have hgL : Measurable gL := (measurable_typeXL κ θ a.nL a.nR a.rhoL a.rhoR).comp measurable_codeWord
  have hgR : Measurable gR := (measurable_typeXR κ θ a.nL a.nR a.rhoL a.rhoR).comp measurable_codeWord
  have hgLe : (fun s => gL (ordCode s)) = ordXL κ θ a := funext fun s => by
    simp only [hgLdef, codeWord_ordCode]
    rfl
  have hgRe : (fun s => gR (ordCode s)) = ordXR κ θ a := funext fun s => by
    simp only [hgRdef, codeWord_ordCode]
    rfl
  have hord := fun e : ℝ => isOrderedForceWord_typeXL (κ := κ) (θ := θ) (nL := a.nL) (nR := a.nR)
    (ρL := a.rhoL) (ρR := a.rhoR) (codeWord e)
  obtain ⟨b, hb⟩ := exists_isAnnouncingSeq_thr_frzDrv (ρL := a.rhoL) (ρR := a.rhoR) (Q := Q) hXP
    measurable_ordCode continuous_ordDrv hgL hgR (fun e => (hord e).1) (fun e => (hord e).2.2.1)
    (by
      rw [hgLe, hgRe]
      exact hgood.mono fun s hs => ⟨hs.2.1, hs.2.2.1⟩)
  rw [hgLe, hgRe] at hb
  obtain ⟨T, hT⟩ := exists_isAnnouncingSeq_aStop (Q := Q) hXP measurable_ordCode continuous_ordDrv
    (fun s => RetCanonSpace.driver_zero s.1) isClosed_codeJ measurable_infDist_codeJ
    (γ := fun s => RetCanonSpace.trace s.1) (fun s => RetCanonSpace.continuous_trace s.1) hb (by
      filter_upwards [hgood] with s hs
      obtain ⟨hgs, hps, hts, hos, hes⟩ := hs
      refine ⟨hgs, hps, le_thr_frzDrv (V := fun s : OrdCanonSpace => RetCanonSpace.life s.1)
        (ρL := a.rhoL) (ρR := a.rhoR) (fun s => continuous_ordDrv s) (ordXL κ θ a) (ordXR κ θ a) hps hts, ?_, ?_⟩
      · intro t ht0 ht
        rw [codeJ_ordCode]
        exact ((isClosed_aStopSet _).notMem_iff_infDist_pos (aStopSet_nonempty _)).2 (hos t ht0 ht)
      · intro htop
        rcases hes htop with h | h
        · exact Or.inl (thr_frzDrv_eq (V := fun s : OrdCanonSpace => RetCanonSpace.life s.1)
            (ρL := a.rhoL) (ρR := a.rhoR) (fun s => continuous_ordDrv s) (ordXL κ θ a) (ordXR κ θ a) hps h).symm
        · refine Or.inr ?_
          rw [codeJ_ordCode]
          exact ((isClosed_aStopSet _).mem_iff_infDist_zero (aStopSet_nonempty _)).2 h)
  obtain ⟨T', hT', hσ, hσm, hσlt, hσlim⟩ := exists_stoppedK2_sequences_sup (P := Q) hWap continuous_ordDrv
    hxLm hxRm hVsp hcode ⟨T, hT⟩
  have hpos : ∀ᵐ s ∂Q, 0 < RetCanonSpace.life s.1 := ae_pos_of_isAnnouncingSeq hT'
  have hord' := fun s : OrdCanonSpace => isOrderedForceWord_typeXL (κ := κ) (θ := θ) (nL := a.nL)
    (nR := a.nR) (ρL := a.rhoL) (ρR := a.rhoR) (RetCanonSpace.word s.1)
  let D : StoppedTypeDataJ OrdCanonSpace Q κ θ := {
    nL := a.nL, nR := a.nR, rhoL := a.rhoL, rhoR := a.rhoR, filt := 𝓕
    word := fun s => RetCanonSpace.word s.1, wordMeas := hcw
    xL := ordXL κ θ a, xR := ordXR κ θ a, xLMeas := hxLm, xRMeas := hxRm
    xLNonpos := fun s => (hord' s).2.1, xRNonneg := fun s => (hord' s).2.2.2
    xLAnti := fun s => (hord' s).1, xRMono := fun s => (hord' s).2.2.1
    typed := htyp
    driver := ordDrv, driverZero := fun s => RetCanonSpace.driver_zero s.1
    driverCont := continuous_ordDrv, driverAdapted := hWap
    field := fun s => RetCanonSpace.field s.1, shiftedField := Z
    fieldMeas := RetCanonSpace.measurable_field.comp measurable_fst, shiftedMeas := hZm
    shifted := fun s => Exist.isTranslateAddConst_flowField 0 _ _
    integrable := hi
    life := fun s => RetCanonSpace.life s.1, lifeStop := hVsp, lifePos := hpos
    lifeThreshold := hgood.mono fun s hs => hs.2.2.1
    announce := T', announcing := hT', killedMeas := hXP
    driveStops := fun n s => (T' n s : WithTop ℝ≥0)
    code := ordCode, codeMeas := hcode
    driveStopping := hσ, driveMono := hσm, driveLt := hσlt, driveLimit := hσlim
    safeLaw := hasSafeLaw_map_retImage hM hY' hZm hZY hWY hVY hLY hRY
      (fun s => RetCanonSpace.driver_zero s.1) continuous_ordDrv hWap hxLm hxRm hVsp hS
    safeMembers := hasSafeMembers_map_retImage hM hY' hZm hZY hWY hVY hL
    trace := fun s => RetCanonSpace.trace s.1
    traceMeas := fun t => (RetCanonSpace.measurable_trace t).comp measurable_fst
    traceCont := fun s => (RetCanonSpace.continuous_trace s.1).continuousOn
    generates := hgood.mono fun s hs => hs.1 }
  refine ⟨{
    model := { space := OrdCanonSpace
               sigma := inferInstance
               borel := inferInstance
               law := Q
               probability := hQ
               data := D }
    read := Y', readMeas := hY', mapLaw := rfl
    agrees := Eventually.of_forall fun ω _ => ⟨hcY ω, (hYsp ω).2.1, hVY ω, (hYsp ω).2.2.2.2⟩ },
    ⟨aStopRule a.rhoL a.rhoR, fun e => measurable_aStopRule _ _ e, fun e => isHistGalmarino_aStopRule _ _ e, ?_⟩,
    ordSeed, ?_, fun ω => rfl⟩
  swap
  · apply measurable_from_retImageFiltration measurable_ordSeed
    convert hSd using 1
    rfl
  filter_upwards [hgood] with s hs
  obtain ⟨hgs, hps, hts, hos, hes⟩ := hs
  refine (aStopRule_killedHistory (ρL := a.rhoL) (ρR := a.rhoR) (W := ordDrv) (fun s => continuous_ordDrv s)
    (xL := ordXL κ θ a) (xR := ordXR κ θ a) (V := fun s : OrdCanonSpace => RetCanonSpace.life s.1)
    (RetCanonSpace.driver_zero s.1) hgs hps hts ?_ ?_).symm
  · intro t ht0 ht
    rw [codeJ_ordCode]
    exact ((isClosed_aStopSet _).notMem_iff_infDist_pos (aStopSet_nonempty _)).2 (hos t ht0 ht)
  · intro htop
    rcases hes htop with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [codeJ_ordCode]
      exact ((isClosed_aStopSet _).mem_iff_infDist_zero (aStopSet_nonempty _)).2 h

/-- **An A-stopped model with an initial code from source processes** (without the rule). -/
theorem nonempty_stoppedModelTransferJ_of_aStop {κ θ : ℝ} (a : ForceWordType)
    {𝓗 : Filtration ℝ≥0 mΩ} {M : Set Ω} (hM : MeasurableSet[𝓗 0] M) (hPM : P M ≠ 0)
    {c : Ω → BoundaryWord} (hc : Measurable[𝓗 0] c)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0) (hWa : StronglyAdapted 𝓗 W)
    {V : Ω → ℝ≥0∞} (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t})
    {γ : Ω → ℝ≥0 → ℂ} (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω}) (hγ0 : ∀ ω, γ ω 0 = 0)
    {E : Ω → Ends} (hE : Measurable[𝓗 0] E) {Sd : Ω → ℝ} (hSd : Measurable[𝓗 0] Sd)
    (htype : ∀ᵐ ω ∂P, ω ∈ M → c ω ∈ typeSet κ θ a.nL a.nR a.rhoL a.rhoR)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω) φ) (P.restrict M))
    (hS : HasSafeLaw κ a.rhoL a.rhoR P 𝓗 M V W
      (geomLW W fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω))
      (geomRW W fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω))
      fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω))
    (hL : HasSafeMembers P 𝓗 M V W fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω))
    (hg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (V ω) (γ ω))
    (hVpos : ∀ᵐ ω ∂P, ω ∈ M → 0 < V ω)
    (hthr : ∀ᵐ ω ∂P, ω ∈ M → V ω ≤ thr a.rhoL a.rhoR W
      (fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) (fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) ω)
    (hoff : ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → γ ω t ∉ aStopSet (E ω))
    (hend : ∀ᵐ ω ∂P, ω ∈ M → V ω ≠ ⊤ → V ω = thr a.rhoL a.rhoR W
      (fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) (fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) ω ∨
        γ ω (V ω).toNNReal ∈ aStopSet (E ω)) :
    Nonempty (StoppedModelTransferJ κ θ P M c Hc V γ) :=
  let ⟨T, _⟩ := exists_stoppedModelTransferJ_rule_of_aStop a hM hPM hc hHc hWc hW0 hWa hVs hγm hγc hγ0 hE hSd htype
    hint hS hL hg hVpos hthr hoff hend
  ⟨T⟩

end InteractingSLE.RLC.OrdModel
