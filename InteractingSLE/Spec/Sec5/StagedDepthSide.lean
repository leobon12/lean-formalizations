/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedCandMean

/-!
# Proposition 5.9 at depth `ℓ`: the mean side of S2 with a staged field shifted from the coupling field

Packet PROVE-STAGED-DEPTH (S2). PROVE-STAGED7's `ae_stage_meanSide` takes the staged history to be of the coupling's
own field `h`; then the first piece of an extreme-angle schedule has angle `±π/2` relative to `h`, while the per-sample
identification of PROVE-CROSSCOND-STAGED4 is written for a first piece of angle `0` relative to the coupling field
(the coupling's own flow line). For Prop. 5.9 the coupling field is the root field `h = h_s + θ₀ χ` (the root piece is
its angle-`0` line, PROVE-STAGED-REP2's `exists_rootCoupling`) and the staged history is of `h_s` (PIECES' code
paths). Both fields have the same centred field `h − 𝔥₀ = h_s − 𝔥_s`, which is all the local-set argument sees.

* **`ae_stage_sideS`**: STAGED7's mean side (with STAGED6's flow-side limit) for a staged history of any field `h_s`
  whose centred field equals the coupling field's: for a fixed test function `φ`, almost surely the conditional mean
  of the centred field given the germs of `U = recHull ∪ G_s` and the marks is `∫ w φ` when `φ` is supported off `U`,
  for one harmonic `w` with the flow-side limit `w − (stageMeanW − 𝔥_s) → 0` (stage mean of `h_s`), the
  counterflow-side and cobounded limits of the counterflow mean, and Aux. 28's uniqueness.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only named input is
`Theorem12ParamCond44Statement` (R74), through PROVE-STAGED5's `exists_flowSide_schedule`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedDepth

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets Theta StagedAdapt
open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue StagedCand
open Theorem14.GW2Schedule (schedDelta schedAngle isFlowProg_scheduleProgram schedDelta_ne_top pastWord)
open Restart (BoundaryWord)
open CrossCond.Staged (stageChart stageGood)
open CrossCond.StagedFinal (stageMeanW)
open SupercriticalConformalCovariance (IsConformalBijection)

section Side

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
/-- **The mean side of S2 for a staged history of a shifted field** (STAGED7's `ae_stage_meanSide` and STAGED6's
flow-side limit, with the staged history of a field `h_s` whose centred field `h_s − 𝔥_s` is the coupling field's
`h − 𝔥₀`). For a fixed test function `φ`: almost surely there is a harmonic `w` off `U = recHull ∪ G_s` such that the
conditional mean of the centred field given the germs of `U` and the marks (staged records, stopped counterflow
history) is `∫ w φ` when `φ` is supported off `U`; on the success event `w − (stageMeanW − 𝔥_s) → 0` at the points of
the prefix hull or of `ℝ` near which `G_s` lies inside the prefix hull; `w − cfMeanQ → 0` at the points of `G_s ∪ ℝ`
near which the prefix hull lies inside `G_s`, and at infinity; and Aux. 28's uniqueness holds on every component. -/
theorem ae_stage_sideS (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hcs : ∀ ω, WholeField.centredField hs us ω = WholeField.centredField h u₀ ω)
    (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀) (hh : IsGFFWithBoundaryData P hs c₀.fn c₀.jumps)
    (hus : IsBoundedHarmonicExtension c₀.fn c₀.jumps us) (sc : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P hs (scheduleSpec sc) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {n : ℕ} (hn : n + 1 ≤ schedL sc) (s : ℝ≥0) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      ∃ w : ℂ → ℝ,
        (tsupport φ ⊆
            H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2) →
          (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
            fun p' => cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ |
            germSigma (fun p : Ω × HistorySpace 0 0 =>
                recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
              (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            ((inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s)).comap
              (fun p : Ω × HistorySpace 0 0 => (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2))] p =
            ∫ z, w z * φ z) ∧
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
            fun p' => Complex.exp (Complex.I * (cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ : ℂ)) |
            germSigma (fun p : Ω × HistorySpace 0 0 =>
                recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
              (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            ((inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s)).comap
              (fun p : Ω × HistorySpace 0 0 => (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2))] p =
          Complex.exp (Complex.I * (((glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1))[fun p' => cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ |
            germSigma (fun p : Ω × HistorySpace 0 0 =>
                recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
              (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            ((inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s)).comap
              (fun p : Ω × HistorySpace 0 0 => (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2))] p :
              ℝ) : ℂ)) *
            ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (H \ relClosureH
              (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) φ φ) :
              ℝ) : ℂ) ∧
        InnerProductSpace.HarmonicOnNhd w
          (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) ∧
        (p.1 ∈ stageGood κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc)) E n →
          ∀ z₀ ∈ recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ {z : ℂ | z.im = 0},
            (∃ r > 0, cfHullQ s p.2 ∩ ball z₀ r ⊆
              recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) →
            Tendsto (fun z => w z - (stageMeanW κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc))
                E (schedAngle (scheduleList sc)) c₀ n p.1 z - us z))
              (𝓝[H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)] z₀)
              (𝓝 0)) ∧
        (∀ z₀ ∈ cfHullQ s p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∩ ball z₀ r ⊆
            cfHullQ s p.2) →
          Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
              (forceJumpFinset xL xR) u' s p.2 z)
            (𝓝[H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)] z₀)
            (𝓝 0)) ∧
        Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
            (forceJumpFinset xL xR) u' s p.2 z)
          (Bornology.cobounded ℂ ⊓
            𝓟 (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)))
          (𝓝 0) ∧
        (∀ z₀ ∈ H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2),
          ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E' : Set ℂ),
          IsConformalBijection f (ball 0 1) (connectedComponentIn
            (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) z₀) →
          IsConformalBijection φc (connectedComponentIn
            (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) z₀)
            {w : ℂ | 0 < w.im} →
          InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
          (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
          ContinuousOn L (connectedComponentIn
            (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) z₀) →
          (∀ z ∈ connectedComponentIn
            (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) z₀,
            deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
          E'.Finite →
          (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E' →
            Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) →
          ∀ z ∈ connectedComponentIn
            (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) z₀,
            w z + u₀ z = G (φc z) - chiC κ * L z) := by
  have hcen0 : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
    funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
  have hcen : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField hs us :=
    hcen0.trans (funext fun ω => (hcs ω).symm)
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨h𝔄, hAloc, hAl⟩ := exists_flowSide_schedule h44 hκ hκ4 c₀ hc₀ hh sc hE hreg hus hn
  have hpm : Measurable (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1)) :=
    measurable_pastMap runMeasStatement c₀.isPiecewiseConstantBoundaryData (scheduleSpec sc) (k := n + 1)
      (fun j _ => hE.1 j) (fun j _ => hreg j) (n + 1) le_rfl
  have hAm := h𝔄.comp hpm
  -- the flow-side representative: the stage mean of the staged field
  have hFgs : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField hs us) P := by
    rw [← hcen, hcen0]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  obtain ⟨gA, hgA⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hFgs hAm hAl
  have hℓ : n < (scheduleSpec sc).2.2.length := hn
  have hADpt : ∀ ω, H \ recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) ω) =
      ((stageChart κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc)) E n ω).dom : Set ℂ) := by
    intro ω
    rw [recHull_eq, Set.sdiff_sdiff_right_self, inter_eq_right.2 (dom_stageChart_subset c₀ sc n ω)]
  obtain ⟨wA, hwA, hwAeq⟩ := StagedFinal.exists_rep_stageMeanW c₀ hκ c₀.isPiecewiseConstantBoundaryData rfl
    (fun _ _ => rfl) hh hE hreg rfl (isFlowProg_scheduleProgram 0 _) (schedDelta_ne_top 0 _) hℓ hus hAm hAl hAloc
    (Eventually.of_forall fun ω _ => hADpt ω) hgA
  rw [← hcen] at hAl hgA hAloc
  -- the union local set on the glued space
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
    rw [hcen0]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hFg := isZeroBoundaryGFF_cenTT_glue (θ := θ) (k := k) hC hu₀
  have hreg₂ := ae_cfRegT hκ hθb hC hcf hlaw
  have hAg := IsLocalSet.glue_fst hXm₀ k (T := cenTT κ θ u₀) hAl
  have hGg := IsLocalSet.glue_snd hXm₀ k (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)
    (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw hk
    (measurable_cenTT κ θ u₀) (measurable_cfHullQ s) MeasurableSet.univ (fun y _ => cfHullQ_relClosed s y)
    (Eventually.of_forall fun _ => mem_univ _) (isLocalSet_cfHullQ_cenTT hcf hreg₂ hu₀.1 s)
  have hloc := IsLocalSet.glue_union hXm₀ k (measurable_cenTT κ θ u₀) (measurable_cenTT' κ θ u₀)
    (cenTT'_cenTT κ θ u₀) hF hAm (measurable_cfHullQ s) hAg hGg
  have hUm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2 :=
    measurable_union_hitting (hAm.comp measurable_fst) ((measurable_cfHullQ s).comp measurable_snd)
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hFg hUm hloc
  have hmark := Staged.isHistoryAvoidanceLocal_union_cfGlueT hC hκ hθb hcf hlaw hk hu₀ hpm le_rfl h𝔄 hAloc s
  have hpair : Measurable fun p : Ω × HistorySpace 0 0 =>
      (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2) :=
    (hpm.comp measurable_fst).prodMk measurable_snd
  have h𝔐 : (inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s) ≤
      (inferInstance : MeasurableSpace (PastData (n + 1) × HistorySpace 0 0)) :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (stopSigma_le s))
  have hℋ := (MeasurableSpace.comap_mono h𝔐).trans hpair.comap_le
  have hce := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hFg hUm hloc hℋ hmark hg φ
  have hAc : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) hXm₀),
      recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2 ⊆ H ∧
        IsOpen (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) :=
    Eventually.of_forall fun p => by
      have h1 := isHPHull_recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)
      have h2 := cfHullQ_relClosed s p.2
      refine ⟨union_subset h1.1 h2.1, ?_⟩
      rw [← Set.sdiff_inter_sdiff]
      exact h1.2.2.1.inter h2.2
  obtain ⟨Mc, -, hMc1, hMc2⟩ := exists_condExp_germSigma_history hFg hUm hℋ hmark hAc φ
  obtain ⟨gG, hgG, hidG⟩ := exists_isLocalSetMean_cfHullQ_pathT hC hκ hcf hreg₂ hlaw hk hu₀ s hu'
  have hU := ae_union_mean_cfGlueT_flowSide hC hκ hθb hcf hlaw hk hu₀ hpm h𝔄 hAl
    (Eventually.of_forall fun ω => not_isBounded_lowerUnion_recHull sc n _) hgA hwA s hu' hg
  have hInf := ae_tendsto_union_sub_cfMean_coboundedT_flowSide hC hκ hθb hcf hlaw hk hu₀ hpm h𝔄
    (fun y => ⟨(isHPHull_recHull sc n y).1, (isHPHull_recHull sc n y).2.2.1⟩)
    (fun y => (isHPHull_recHull sc n y).2.1) hAl s hg hgG
  have huniq := Sec6.ae_eqOn_component_of_tendsto_global hFg hUm hloc hg hu₀.1 hu₀.2.1 (chiC κ)
  filter_upwards [hce, hU, hInf, huniq, hidG, hMc1, hMc2] with p hcep ⟨w, h1, h2, h3, h4⟩ hInfp huniqp hidGp
    hc1 hc2
  refine ⟨w, fun hφ => hcep.symm.trans (h2 φ hφ), by rw [← hc2, hc1], h1, fun hgood z₀ hz₀ hr => ?_, h4,
    hInfp w _ h1 h2 (harmonicOnNhd_cfMeanQ _ _ _ hu'.1 s p.2) hidGp, fun z₀ hz₀ => huniqp z₀ hz₀ w h1 h2⟩
  have e := hwAeq p.1 hgood (hADpt p.1)
  have hl := h3 z₀ hz₀ hr
  rw [e] at hl
  exact hl

end Side

end InteractingSLE.Sec5.CrossCond.StagedDepth
