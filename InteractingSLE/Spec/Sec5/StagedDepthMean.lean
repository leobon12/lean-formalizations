/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedDepthSample
import InteractingSLE.Spec.Sec5.StagedDepthJoin
import InteractingSLE.Spec.Sec5.CrossCondStagedCandMean
import InteractingSLE.Spec.Sec5.StagedDepthSide

/-!
# Proposition 5.9 at depth `ℓ`: the staged mean identification on the glued space (S2)

Packet PROVE-STAGED-DEPTH (S2, assembly). For a fixed extreme-angle schedule `sc` whose staged history `E` is of the
coupling's field, on the θ-glued space of CROSSCOND-THETA, the staged path is the flow trace of WangWu's image word for
the joined driver `joinProc sc E` (`seedLine ⊤ (joinProc sc E)`, a simple proper arc a.s., `StagedDepthJoin`). Its
image in the counterflow chart is the killed arc `gCurve s ⊤ (joinProc sc E) Eg p` on the good set
`Eg = glueGood μ s ⊤ (joinProc sc E)`. At the end `t = cumT (schedD sc) n` of piece `n`:

* `IsGoodSched.mem_stageGood`: on the good event of the schedule, the success event `stageGood` of the stage holds;
* `IsGoodSched.joinW_eq_catN_stageDrv`: the joined driver is the concatenated record driver on `[0, t]`;
* **`ae_isGood49_joinProc`**: almost surely the glued sample is good for the joined driver;
* **`ae_stage_meanIdent`** (S2): almost surely, when the staged prefix is pre-contact at `t` and the test function is
  supported off the union `recHull ∪ G_s`, the conditional mean of the centred field given the germs of the union
  and the marks (staged records, stopped counterflow history) is the integral against the image stage word's
  candidate in the chart `Ψ`, the image chain being the canonical one of `gCurve` up to `capClock γ t` and the switch
  image times `capClock γ (startT m)`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only named input is
`Theorem12ParamCond44Statement` (R74), through PROVE-STAGED7's `ae_stage_meanSide` and `ae_schedule_goodPath`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedDepth

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar MartChar.RealFlow Restart.RetAux79 Sec7.StripSysField GlueImg Word49 Theta StagedFinal
open Restart Exist.StagedLaw Exist.Staged Theorem14.GW2Schedule
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue StagedCand
open Sec7.Lemma71C (capClock)
open CrossCond.Staged (stageGood stageDrv catN cumT)

/-! ### The success event and the record driver on the good event of the schedule -/

section Good

variable {κ : ℝ} {c₀ : BoundaryWord} {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

/-- **On the good event of the schedule the stage succeeds**: every piece `0, …, n` runs its own time and its record
driver is good. -/
theorem IsGoodSched.mem_stageGood {sc : Schedule} (hg : IsGoodSched sc E ω) (hreg : ∀ j, IsRegularDriver (E j ω))
    {n : ℕ} (hn : n + 1 ≤ schedL sc) :
    ω ∈ stageGood κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc)) E n := by
  have hs := hg.allSucc (n + 1) hn
  refine ⟨hs, ?_⟩
  have hpm := pastMap_of_allSucc (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) (spec := scheduleSpec sc) rfl
    (isFlowProg_scheduleProgram 0 (scheduleList sc)) (schedDelta_ne_top _ _) E hn hs
  intro i
  rw [hpm]
  have htime : (((schedDelta 0 (scheduleList sc) i).toNNReal : ℝ≥0) : ℝ≥0∞) < (E i ω).2 := by
    rw [(hg i (by omega)).1]
    exact ENNReal.coe_lt_top
  have h := isDrvGood_recOf_of_lt (hreg i) htime
  rwa [ENNReal.coe_toNNReal (schedDelta_ne_top _ _ _)] at h

/-- **On the good event the joined driver is the concatenated record driver** up to the end of piece `n`. -/
theorem IsGoodSched.joinW_eq_catN_stageDrv {sc : Schedule} (hg : IsGoodSched sc E ω)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {n : ℕ} (hn : n + 1 ≤ schedL sc) {r : ℝ≥0}
    (hr : r ≤ cumT (schedD sc) n) :
    joinW sc E ω r = catN (stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω) (schedD sc) n r := by
  have h1 : joinW sc E ω r = catN (pieceW sc E ω) (schedD sc) n r :=
    catN_of_le_cumT (by omega) hr
  have h2 : catN (stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω) (schedD sc) n =
      catN (StagedGlue.stopW sc E ω) (schedD sc) n := by
    refine catN_congr_le _ _ _ n fun j hj => ?_
    funext x
    have e := hg.recDrvOf_eq (κ := κ) (c₀ := c₀) hreg hn (j := j) (by omega) x
    simp only [StagedGlue.stopW, pieceW_of_lt sc E ω (show j < schedL sc by omega)]
    exact e
  rw [h1, h2, catN_stopW_eq n hr]

end Good

/-! ### The counterflow side is good almost surely -/

section CfGood

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **Almost surely the glued counterflow history is good** (the counterflow halves of CROSSCOND-THETA's
`cfGlueAE_mem_goodHitSetT` and `cfGlueAE_isGood49T`, which need no hypothesis on the coupling's flow line). -/
theorem ae_cfGood_glueT (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p.2 ∈ goodHitSet ∧ p.2 ∈ goodSet49 s := by
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hk' : 0 < 16 / κ := by positivity
  have hΩ₁ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodHitSet := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
      exists_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
    filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
      hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw]
      with ω ⟨hζ, _, η, hη⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodHitSet hζ hw hp.1 hη fun t _ x hx => hne η hη t x hx
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodSet49 s := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm', hE, ⟨iL, hiL⟩, ⟨iR, hiR⟩⟩ :=
      exists_seed_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
    filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm' hE,
      hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw]
      with ω ⟨hζ, hsep, η, hη⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodSet49 hp hζ hw hsep hiL hiR hη (fun t _ x hx => hne η hη t x hx) hs
  have h1 := ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodHitSet hΩ₁
  have h2 := ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    (measurableSet_goodSet49 s) hΩ₂
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

end CfGood

/-! ### S2: the staged mean identification on the glued space -/

section Main

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {hs : Ω → DistOn upperHalfPlaneOpens} {us : ℂ → ℝ}

include h44 hκ hκ4 in
/-- **S2: the staged mean identification on the glued space** (Prop. 5.9 at depth `n`, Astra follow-up 4 §3.4 Steps
1–3, (SW2) for the image of the staged prefix). In the θ-glued setting of the coupling field `h`, let `E` be the
staged history of a fixed extreme-angle schedule `sc` for a field `h_s` with the same centred field
(`h_s − 𝔥_s = h − 𝔥₀`, `𝔥₀ = 𝔥_s + θ₀ χ`, `θ₀` the first angle of `sc`). For a fixed test function `φ`, almost surely:
if the glued sample is good for the joined staged driver, the staged path is pre-contact at the end
`t = cumT (schedD sc) n` of piece `n`, and `φ` is supported off the union `U = recHull ∪ G_s`, then for the canonical
image chain `W'` of the image curve `γ = gCurve s ⊤ (joinProc sc E) Eg p` up to `T = capClock γ t` and every bounded
harmonic extension `u_I` of the image stage word (angles `θ_j − θ₀`, switch image times `capClock γ (startT m)`), the
conditional mean of the centred field given the germs of `U` and the marks (staged records, stopped counterflow
history), plus `∫ 𝔥₀ φ`, is `∫ (u_I ∘ f′_T ∘ Ψ − (θ_n − θ₀) χ − χ (arg f′_T′ ∘ Ψ + arg Ψ′)) φ`. -/
theorem ae_stage_meanIdent (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hcs : ∀ ω, WholeField.centredField hs us ω = WholeField.centredField h u₀ ω)
    (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀) (hh : IsGFFWithBoundaryData P hs c₀.fn c₀.jumps)
    (hus : IsBoundedHarmonicExtension c₀.fn c₀.jumps us) (sc : Schedule)
    (hu₀s : ∀ z, u₀ z = us z + schedAngle (scheduleList sc) 0 * chiC κ)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P hs (scheduleSpec sc) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {n : ℕ} (hn : n + 1 ≤ schedL sc) {s : ℝ≥0} (hs0 : 0 < s) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s
        (fun _ => ⊤) (joinProc sc E) →
      ((cumT (schedD sc) n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (joinProc sc E)
        (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s
          (fun _ => ⊤) (joinProc sc E)) p →
      tsupport φ ⊆ H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2) →
      ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧
        EqOn W' (chainDrv (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
            (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) p)
          (gPre s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
            (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) p))
          (Icc 0 (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
            (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) p)
            ((cumT (schedD sc) n : ℝ≥0) : ℝ))) ∧
        ∀ uI : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ
            (imgStageRhoL κ θ ρL (fun j => schedAngle (scheduleList sc) j - schedAngle (scheduleList sc) 0) n)
            (imgStageRhoR κ θ ρR (fun j => schedAngle (scheduleList sc) j - schedAngle (scheduleList sc) 0) n)
            (imgStageVL xL (cfDrv0 s p.2) s W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood
              (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ))
              (fun m => capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
                (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                  (joinProc sc E)) p)
                (startT (recSeqT (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) m)) n)
            (imgStageVR xR (cfDrv0 s p.2) s W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood
              (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ))
              (fun m => capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
                (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                  (joinProc sc E)) p)
                (startT (recSeqT (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) m)) n))
          (forceJumpSet
            (imgStageVL xL (cfDrv0 s p.2) s W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood
              (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ))
              (fun m => capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
                (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                  (joinProc sc E)) p)
                (startT (recSeqT (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) m)) n)
            (imgStageVR xR (cfDrv0 s p.2) s W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood
              (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ))
              (fun m => capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
                (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                  (joinProc sc E)) p)
                (startT (recSeqT (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) m)) n)) uI →
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
            fun p' => cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ |
            germSigma (fun p : Ω × HistorySpace 0 0 =>
                recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
              (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            ((inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s)).comap
              (fun p : Ω × HistorySpace 0 0 => (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2))] p +
            ∫ z, u₀ z * φ z =
          ∫ z, ((uI (fwdMap W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
              (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ)) (revChart (cfDrv0 s p.2) s z)) -
              (schedAngle (scheduleList sc) n - schedAngle (scheduleList sc) 0) * chiC κ) -
            chiC κ * ((logDerivFwd W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
              (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ)) (revChart (cfDrv0 s p.2) s z)).im +
              (logDerivPsi (cfDrv0 s p.2) s z).im)) * φ z := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set Eg := glueGood μ s (fun _ => ⊤) (joinProc sc E) with hEgdef
  set ang := schedAngle (scheduleList sc) with hang
  set t : ℝ := ((cumT (schedD sc) n : ℝ≥0) : ℝ) with htdef
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hGg := ae_glue_fst (μ := P) k hXm ((ae_isGoodSched h44 hκ hκ4 c₀ hc₀ hh sc hE hreg).and
    (ae_schedule_goodPath h44 hκ hκ4 c₀ hc₀ hh sc hE hreg))
  have hcfg := ae_cfGood_glueT hκ hC hθb hcf hlaw k hk hs0
  have hside := ae_stage_sideS h44 hκ hκ4 hC hθb hcf hlaw hk hu₀ hcs c₀ hc₀ hh hus sc hE hreg hn s hu' φ
  filter_upwards [hGg, hcfg, hside] with p ⟨hgs, hgp⟩ ⟨hy, _⟩ ⟨w, hwce, _, hwh, hwFl, hwG, hwInf, huniq⟩ hpE htP hφ
  -- the staged trace on this sample
  obtain ⟨hjc, hj0, hαp, hα⟩ := properArc_seedLine_joinProc sc (fun j => hreg j p.1) hgp
  have hgood := StagedDepth.IsGoodSched.mem_stageGood (κ := κ) (c₀ := c₀) hgs (fun j => hreg j p.1) hn
  set u := pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1 with hudef
  set Wα : ℝ → ℝ := fun r => joinW sc E p.1 r.toNNReal with hWαdef
  set Wcat : ℝ → ℝ := Ito.rpath (catN (stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n p.1) (schedD sc) n)
    with hWcatdef
  have hWα : Continuous Wα := hjc.comp continuous_real_toNNReal
  have hWα0 : Wα 0 = 0 := by simp only [hWαdef, Real.toNNReal_zero, hj0]
  have hWcat : Continuous Wcat := CrossCond.Staged.continuous_rpath_of
    (CrossCond.Staged.continuous_catN (CrossCond.Staged.continuous_stageDrv n p.1)
      (CrossCond.Staged.stageDrv_zero n p.1) n)
  have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg _
  have hagree : EqOn Wα Wcat (Icc 0 t) := fun r hr => by
    simp only [hWαdef, hWcatdef, Ito.rpath]
    exact StagedDepth.IsGoodSched.joinW_eq_catN_stageDrv hgs hreg hn (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hHull : recHull sc n u = fwdHull Wα t := by
    rw [hudef, recHull_pastMap_eq_fwdHull]
    exact (YuanCorollary13.fwdHull_eq_of_eqOn_Icc hWα hWcat ht0 fun r hr => hagree hr).symm
  rw [hHull] at hφ hwh hwG hwInf huniq
  -- the records
  have hprog := isFlowProg_scheduleProgram 0 (scheduleList sc)
  have hpos : ∀ i ≤ n, 0 < recSeqT u i := fun i hi => by
    rw [(StagedFinal.stage_records (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) (spec := scheduleSpec sc) rfl hprog
      (schedDelta_ne_top 0 _) hn hgood hi).1]
    exact NNReal.coe_pos.2 (schedD_pos sc (by omega))
  have htS : startT (recSeqT u) (n + 1) = t :=
    StagedFinal.stage_total (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) (spec := scheduleSpec sc) rfl hprog
      (schedDelta_ne_top 0 _) hn hgood
  have hw : ∀ i, EqOn (recSeqW u i) (shiftDrive Wα (startT (recSeqT u) i)) (Icc 0 (recSeqT u i)) := by
    intro i r hr
    rw [StagedFinal.stage_hw (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) (spec := scheduleSpec sc) rfl hprog
      (schedDelta_ne_top 0 _) hn hgood i hr]
    have hT := StagedFinal.recSeqT_nonneg u
    have hS0 : 0 ≤ startT (recSeqT u) i := by
      have := startT_mono hT (Nat.zero_le i)
      rwa [startT_zero] at this
    by_cases hi : i ≤ n
    · have h1 : startT (recSeqT u) i + r ≤ t := by
        rw [← htS]
        have h2 := startT_mono hT (show i + 1 ≤ n + 1 by omega)
        rw [startT_succ] at h2
        linarith [hr.2]
      simp only [shiftDrive]
      rw [hagree ⟨by linarith [hr.1], h1⟩, hagree ⟨hS0, by linarith [hr.1]⟩]
      rfl
    · have h0 : recSeqT u i = 0 := by
        simp only [recSeqT, show ¬ i < n + 1 by omega, ↓reduceDIte]
      rw [h0] at hr
      obtain rfl : r = 0 := le_antisymm hr.2 hr.1
      simp only [shiftDrive, add_zero, sub_self]
  -- the flow-side limit in the literal form
  have hFl0 := tendsto_hFl_of_stageMeanW (θ := 0) c₀ sc n p.1 (cfHullQ s p.2) (M := fun z => w z + us z)
    (w := w) (u₀ := us) (fun z => by ring) (hwFl hgood)
  have hcatHull : fwdHull Wcat t = fwdHull Wα t :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc hWcat hWα ht0 fun r hr => (hagree hr).symm
  have hEg : ∀ p ∈ Eg, IsGood49 s (fun _ => ⊤) (joinProc sc E) p := isGood49_of_mem_glueGood
  obtain ⟨-, hGc, -, -, hGeq⟩ := hEg p hpE
  have hpre : t ∈ preContact (WangWu.seedLine (fun _ => ⊤) (joinProc sc E) p.1) (cfHullQ s p.2) :=
    gPre_of_mem hpE ▸ htP
  have hwFl' : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => w z + u₀ z -
      ((pastWord (stopWord κ) c₀ 0 ang (n + 1) u).mean (fwdMap Wα t z) + ang 0 * chiC κ -
        chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ cfHullQ s p.2)] (WangWu.seedLine (fun _ => ⊤) (joinProc sc E) p.1 v)) (𝓝 0) := by
    intro v hv0 hvt
    have hαv : WangWu.seedLine (fun _ => ⊤) (joinProc sc E) p.1 v ∈ fwdHull Wα t := by
      rw [fwdHull_eq_image_Ioc hα hαp ht0]
      exact ⟨v, ⟨hv0, hvt.le⟩, rfl⟩
    have hαvG : WangWu.seedLine (fun _ => ⊤) (joinProc sc E) p.1 v ∉ cfHullQ s p.2 :=
      hpre.2 v ⟨hv0.le, hvt.le⟩
    have hGc' : IsClosed (cfHullQ s p.2) := hGeq ▸ hGc
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hGc'.isOpen_compl _ hαvG
    have h1 := hFl0 _ (Or.inl (hcatHull ▸ hαv)) ⟨r, hr, fun z hz => absurd hz.1 (hball hz.2)⟩
    rw [hcatHull] at h1
    refine h1.congr fun z => ?_
    rw [Ito.fwdMap_congr_of_eqOn (W := Wcat) (W' := Wα) fun r hr => (hagree hr).symm,
      Ito.logDerivFwd_congr_of_eqOn (W := Wcat) (W' := Wα) (fun r hr => (hagree hr).symm) ht0 le_rfl, hu₀s z]
    ring
  -- the end of piece `n` is a positive time
  have htpos : 0 < t := by
    have h1 := hpos 0 (Nat.zero_le n)
    have h2 := startT_mono (StagedFinal.recSeqT_nonneg u) (show 1 ≤ n + 1 by omega)
    rw [startT_succ, startT_zero, zero_add, htS] at h2
    exact lt_of_lt_of_le h1 h2
  -- the per-sample identification
  obtain ⟨W', hW', hW'0, hEq, hmain⟩ := stage_imgChart_sample (θ := θ) (ρL := ρL) (ρR := ρR) hκ hxL hxR hEg hpE
    htpos htP hα hWα hWα0 hy c₀ 0 u hpos htS hw hu₀ hu' hwFl' hwG hwInf huniq
  refine ⟨W', hW', hW'0, hEq, fun uI hu => ?_⟩
  rw [hwce (hHull ▸ hφ)]
  have hwc : ContinuousOn w (H \ (fwdHull Wα t ∪ cfHullQ s p.2)) :=
    fun z hz => (hwh z hz).1.continuousAt.continuousWithinAt
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hi1 := WholeField.integrable_mul_testOn hwc φ hφ
  have hi2 := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
  rw [← integral_add hi1 hi2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero, add_zero]
  have hzU := hφ (subset_tsupport _ hz)
  beta_reduce
  rw [← add_mul, hmain uI hu z hzU]

end Main

end InteractingSLE.Sec5.CrossCond.StagedDepth
