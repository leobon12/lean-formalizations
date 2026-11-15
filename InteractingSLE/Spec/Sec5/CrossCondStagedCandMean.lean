/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedCandInf
import InteractingSLE.Spec.Sec5.CrossCondStagedAdaptStage

/-!
# Proposition 5.9, S2 on the glued space: the mean side for the staged prefix of a fixed schedule

Packet PROVE-STAGED7 (PROVE-STAGED6 §5.2 items 2–3 and the mean half of item 5). For a fixed extreme-angle schedule
`sc`, the staged prefix hull `A = recHull sc n (pastMap … (n + 1))` of the coupling's field, and the counterflow hull
`G_s` on the θ-glued space, this file assembles everything the per-sample identification
(`StagedFinal.eqOn_imgChart_pastWord`) needs from the probabilistic side, for ONE representative `w` of the union
mean (the staged analogue of the first half of `Theta.meanIdentThetaStatement`'s proof):

* the union `A ∪ G_s` is a local set of the centred field on the glued space, with a local-set mean `g`;
* `g φ` is the conditional mean of the centred field given the germs of the union and the marks
  `σ(staged records) ⊗ σ(stopped counterflow history)` (Lemma 3.6 with history marks);
* almost surely `w` is harmonic off the union, represents `g`, has the flow-side limit `w − (stageMeanW − 𝔥₀) → 0`
  (on the success event), the counterflow-side limit `w − cfMeanQ → 0`, the **cobounded limit** `w − cfMeanQ → 0`
  (`hInf`, `CrossCondStagedCandInf`), and satisfies Aux. 28's uniqueness on every component (`huniq`,
  `Sec6.ae_eqOn_component_of_tendsto_global`).

Main result: **`ae_stage_meanSide`**. Conditional helpers with distinct names; they replace no source theorem. R48:
nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only
named input is `Theorem12ParamCond44Statement` (R74), through PROVE-STAGED5's `exists_flowSide_schedule`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedCand

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets Theta StagedAdapt
open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue
open Theorem14.GW2Schedule (schedDelta schedAngle isFlowProg_scheduleProgram schedDelta_ne_top pastWord)
open Restart (BoundaryWord)
open CrossCond.Staged (stageChart stageGood)
open CrossCond.StagedFinal (stageMeanW)
open SupercriticalConformalCovariance (IsConformalBijection)

section Stage

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4 in
/-- **The mean side of S2 for the staged prefix on the θ-glued space.** In the θ-glued setting, for a fixed
extreme-angle schedule `sc` whose staged history `E` is of the coupling's field (root word `c₀`, `u₀` the bounded
harmonic extension of both the force data and `c₀`'s data), the union `U = recHull sc n (pastMap … (n + 1)) ∪ G_s`
has a local-set mean `g` that is the conditional mean of the centred field given the germs of `U` and the marks
(staged records, stopped counterflow history), and almost surely a harmonic representative `w` of `g` with the
flow-side limit (on the success event), the counterflow-side limit, the cobounded limit to `cfMeanQ`, and Aux. 28's
uniqueness on every component of `ℍ ∖ U`. -/
theorem ae_stage_meanSide (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀) (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps)
    (hu₀c : IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀) (sc : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec sc) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {n : ℕ} (hn : n + 1 ≤ schedL sc) (s : ℝ≥0) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u') :
    ∃ g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × HistorySpace 0 0 =>
          recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
        (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g ∧
      (∀ φ : TestOn upperHalfPlaneOpens, (fun p => g p φ) =ᵐ[glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)]
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ |
          germSigma (fun p : Ω × HistorySpace 0 0 =>
              recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
            (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
          ((inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s)).comap
            (fun p : Ω × HistorySpace 0 0 => (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2))]) ∧
      ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
        ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w
            (H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) ∧
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆
            H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2) →
              g p φ = ∫ z, w z * φ z) ∧
          (p.1 ∈ stageGood κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc)) E n →
            ∀ z₀ ∈ recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ {z : ℂ | z.im = 0},
              (∃ r > 0, cfHullQ s p.2 ∩ ball z₀ r ⊆
                recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) →
              Tendsto (fun z => w z - (stageMeanW κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc))
                  E (schedAngle (scheduleList sc)) c₀ n p.1 z - u₀ z))
                (𝓝[H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)]
                  z₀) (𝓝 0)) ∧
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
  have hcen : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
    funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨h𝔄, hAloc, hAl⟩ := exists_flowSide_schedule h44 hκ hκ4 c₀ hc₀ hh sc hE hreg hu₀c hn
  rw [← hcen] at hAloc hAl
  have hpm : Measurable (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1)) :=
    measurable_pastMap runMeasStatement c₀.isPiecewiseConstantBoundaryData (scheduleSpec sc) (k := n + 1)
      (fun j _ => hE.1 j) (fun j _ => hreg j) (n + 1) le_rfl
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
    rw [hcen]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hFg := isZeroBoundaryGFF_cenTT_glue (θ := θ) (k := k) hC hu₀
  have hreg₂ := ae_cfRegT hκ hθb hC hcf hlaw
  have hAg := IsLocalSet.glue_fst hXm₀ k (T := cenTT κ θ u₀) hAl
  have hGg := IsLocalSet.glue_snd hXm₀ k (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)
    (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw hk
    (measurable_cenTT κ θ u₀) (measurable_cfHullQ s) MeasurableSet.univ (fun y _ => cfHullQ_relClosed s y)
    (Eventually.of_forall fun _ => mem_univ _) (isLocalSet_cfHullQ_cenTT hcf hreg₂ hu₀.1 s)
  have hloc := IsLocalSet.glue_union hXm₀ k (measurable_cenTT κ θ u₀) (measurable_cenTT' κ θ u₀)
    (cenTT'_cenTT κ θ u₀) hF (h𝔄.comp hpm) (measurable_cfHullQ s) hAg hGg
  have hUm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2 :=
    measurable_union_hitting (((h𝔄.comp hpm)).comp measurable_fst) ((measurable_cfHullQ s).comp measurable_snd)
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hFg hUm hloc
  have hmark := Staged.isHistoryAvoidanceLocal_union_cfGlueT hC hκ hθb hcf hlaw hk hu₀ hpm le_rfl h𝔄 hAloc s
  have hpair : Measurable fun p : Ω × HistorySpace 0 0 =>
      (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2) :=
    (hpm.comp measurable_fst).prodMk measurable_snd
  have h𝔐 : (inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s) ≤
      (inferInstance : MeasurableSpace (PastData (n + 1) × HistorySpace 0 0)) :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (stopSigma_le s))
  have hℋ := (MeasurableSpace.comap_mono h𝔐).trans hpair.comap_le
  refine ⟨g, hg, fun φ => WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hFg hUm hloc hℋ hmark hg φ, ?_⟩
  obtain ⟨gG, hgG, hidG⟩ := exists_isLocalSetMean_cfHullQ_pathT hC hκ hcf hreg₂ hlaw hk hu₀ s hu'
  have hwA := ae_union_mean_cfGlueT_stage h44 hκ hκ4 hC hθb hcf hlaw hk hu₀ c₀ hc₀ hh hu₀c sc hE hreg hn s hu' hg
  have hInf := ae_tendsto_union_sub_cfMean_coboundedT_flowSide hC hκ hθb hcf hlaw hk hu₀ hpm h𝔄
    (fun y => ⟨(isHPHull_recHull sc n y).1, (isHPHull_recHull sc n y).2.2.1⟩)
    (fun y => (isHPHull_recHull sc n y).2.1) hAl s hg hgG
  have huniq := Sec6.ae_eqOn_component_of_tendsto_global hFg hUm hloc hg hu₀.1 hu₀.2.1 (chiC κ)
  filter_upwards [hwA, hInf, huniq, hidG] with p ⟨w, h1, h2, h3, h4⟩ hInfp huniqp hidGp
  exact ⟨w, h1, h2, h3, h4, hInfp w _ h1 h2 (harmonicOnNhd_cfMeanQ _ _ _ hu'.1 s p.2) hidGp,
    fun z₀ hz₀ => huniqp z₀ hz₀ w h1 h2⟩

end Stage

/-! ### The flow-side limit in the literal form of `eqOn_imgChart_pastWord` -/

section Literal

variable {κ θ : ℝ} {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The prefix hull of the records is the forward hull of the concatenated record driver at the total time. -/
theorem recHull_pastMap_eq_fwdHull (c₀ : BoundaryWord) (sc : Schedule) (n : ℕ) (ω : Ω) :
    recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) ω) =
      QuantumZipper.fwdHull (Ito.rpath (Staged.catN (Staged.stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω)
        (schedD sc) n)) (Staged.cumT (schedD sc) n) :=
  recHull_eq_fwdHull sc n _

/-- **The explicit own mean in the chart of the concatenated record driver** (`StagedFinal.stageMeanW_eq` for a
schedule: `spec.1 = 0`, the word is the canonical word of the records). -/
theorem stageMeanW_schedule_eq (c₀ : BoundaryWord) (sc : Schedule) (n : ℕ) (ω : Ω) (z : ℂ) :
    stageMeanW κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc)) E (schedAngle (scheduleList sc))
        c₀ n ω z =
      (pastWord (stopWord κ) c₀ 0 (schedAngle (scheduleList sc)) (n + 1)
          (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) ω)).mean
          (QuantumZipper.fwdMap (Ito.rpath (Staged.catN (Staged.stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω)
            (schedD sc) n)) (Staged.cumT (schedD sc) n) z) -
        chiC κ * (QuantumZipper.logDerivFwd (Ito.rpath (Staged.catN
          (Staged.stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω) (schedD sc) n))
            (Staged.cumT (schedD sc) n) z).im := by
  rw [StagedFinal.stageMeanW_eq, add_zero]
  have e : z - (scheduleSpec sc).1 = z := sub_zero z
  rw [e]
  rfl

/-- **The flow side's limit `hFl` in the literal form** of `StagedFinal.eqOn_imgChart_pastWord` (PROVE-STAGED6 §5.2
item 1): if `w − (stageMeanW − 𝔥₀) → 0` at the points of the prefix hull or of `ℝ` near which `G` lies inside the
prefix hull (the flow-side clause of `ae_stage_meanSide` on the success event), then for every `M` with
`M + θχ = w + 𝔥₀`, at those points `M + θχ − (β.mean ∘ f_t − χ arg f_t′) → 0`, with `β` the canonical word of the
records, `f_t` the forward map of the concatenated record driver `Wα` at the total time `t`, and the prefix hull
written as `fwdHull Wα t`. -/
theorem tendsto_hFl_of_stageMeanW (c₀ : BoundaryWord) (sc : Schedule) (n : ℕ) (ω : Ω) (G : Set ℂ)
    {w u₀ M : ℂ → ℝ} (hMw : ∀ z, M z + θ * chiC κ = w z + u₀ z)
    (hFl : ∀ z₀ ∈ recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) ω) ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, G ∩ ball z₀ r ⊆ recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) ω)) →
      Tendsto (fun z => w z - (stageMeanW κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc)) E
          (schedAngle (scheduleList sc)) c₀ n ω z - u₀ z))
        (𝓝[H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) ω) ∪ G)] z₀) (𝓝 0)) :
    ∀ z₀ ∈ QuantumZipper.fwdHull (Ito.rpath (Staged.catN (Staged.stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω)
        (schedD sc) n)) (Staged.cumT (schedD sc) n) ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, G ∩ ball z₀ r ⊆ QuantumZipper.fwdHull (Ito.rpath (Staged.catN
        (Staged.stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω) (schedD sc) n)) (Staged.cumT (schedD sc) n)) →
      Tendsto (fun z => M z + θ * chiC κ -
          ((pastWord (stopWord κ) c₀ 0 (schedAngle (scheduleList sc)) (n + 1)
            (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) ω)).mean
            (QuantumZipper.fwdMap (Ito.rpath (Staged.catN (Staged.stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω)
              (schedD sc) n)) (Staged.cumT (schedD sc) n) z) -
          chiC κ * (QuantumZipper.logDerivFwd (Ito.rpath (Staged.catN
            (Staged.stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω) (schedD sc) n))
              (Staged.cumT (schedD sc) n) z).im))
        (𝓝[H \ (QuantumZipper.fwdHull (Ito.rpath (Staged.catN
          (Staged.stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E n ω) (schedD sc) n))
            (Staged.cumT (schedD sc) n) ∪ G)] z₀) (𝓝 0) := by
  intro z₀ hz₀ hr
  rw [← recHull_pastMap_eq_fwdHull] at hz₀ hr ⊢
  refine (hFl z₀ hz₀ hr).congr fun z => ?_
  rw [hMw z, stageMeanW_schedule_eq]
  ring

end Literal

end InteractingSLE.Sec5.CrossCond.StagedCand
