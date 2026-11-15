/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedAdaptUnion
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueJoint
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalExplicit

/-!
# Proposition 5.9, S2: the flow-side limit `hFl` for the staged prefix of a fixed extreme-angle schedule

Packet PROVE-STAGED6. For a fixed extreme-angle schedule `sc` (PROVE-STAGED5's setting: a staged history `E` of the
field `h` along `scheduleSpec sc`, R48-safe through `Theorem12ParamCond44Statement`, R74) and the θ-glued counterflow
(PROVE-CROSSCOND-THETA's setting), the union of the staged prefix hull `recHull sc n (pastMap … (n + 1))` with the
counterflow hull `G_s` has a local-set mean represented by a harmonic `w` such that, on the success event
`stageGood`, `w − (stageMeanW − 𝔥₀) → 0` at every point of the prefix hull or of `ℝ` near which `G_s` lies inside the
prefix hull. Here `stageMeanW` is PROVE-CROSSCOND-STAGED4's explicit own mean of the prefix (the iterated stop word's
mean read in the stage chart), so this is the flow-side limit `hFl` of `StagedFinal.eqOn_imgChart_pastWord` (after
`StagedFinal.stageMeanW_eq`), at the prefix points away from the counterflow hull. The counterflow side
`w − cfMeanQ → 0`
is delivered as well.

Main result: **`ae_union_mean_cfGlueT_stage`**, assembled from `ae_union_mean_cfGlueT_flowSide`,
`StagedGlue.exists_flowSide_schedule` (locality of the staged prefix), `StagedGlue.not_isBounded_lowerUnion_recHull`
and `StagedFinal.exists_rep_stageMeanW` (the explicit own mean).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only named input is
`Theorem12ParamCond44Statement` (R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedAdapt

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets Theta
open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue
open Theorem14.GW2Schedule (schedDelta schedAngle isFlowProg_scheduleProgram schedDelta_ne_top)
open Restart (BoundaryWord)
open CrossCond.Staged (stageChart stageGood continuous_catN catN_zero rpath_zero_of_zero continuous_rpath_of cumT
  isConformal_recenter_loewner)
open CrossCond.StagedFinal (stageMeanW)

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

omit mΩ [StandardBorelSpace Ω] in
/-- The domain of the stage chart of a schedule lies in `ℍ` (the chart is a recentred Loewner chart of a continuous
driver started at `0`). -/
theorem dom_stageChart_subset (c₀ : BoundaryWord) (sc : Schedule) (n : ℕ) (ω : Ω) :
    ((stageChart κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc)) E n ω).dom : Set ℂ) ⊆ H := by
  have hc := CrossCond.Staged.continuous_stageDrv (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) (spec := scheduleSpec sc)
    (E := E) n ω
  have h0 := CrossCond.Staged.stageDrv_zero (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) (spec := scheduleSpec sc)
    (E := E) n ω
  have hW := continuous_rpath_of (continuous_catN (T := fun j => (schedDelta 0 (scheduleList sc) j).toNNReal) hc h0 n)
  have hW0 := rpath_zero_of_zero (catN_zero (T := fun j => (schedDelta 0 (scheduleList sc) j).toNNReal) h0 n)
  exact (isConformal_recenter_loewner (scheduleSpec sc).1 hW hW0 (cumT _ n).coe_nonneg).dom_subset

include h44 hκ hκ4 in
/-- **The flow-side limit of the union mean for the staged prefix** (S2's `hFl` source). In the θ-glued setting,
for a fixed extreme-angle schedule `sc` whose staged history `E` is of the coupling's field `h` (with root word `c₀`,
`u₀` the bounded harmonic extension of both the force data and `c₀`'s data), almost surely the local-set mean `g`
of `recHull sc n (pastMap … (n + 1)) ∪ G_s` has a harmonic representative `w` such that, on the success event,
`w − (stageMeanW − 𝔥₀) → 0` at every point of the prefix hull or of `ℝ` near which `G_s` lies inside the prefix
hull, and `w − cfMeanQ → 0` at every point of `G_s ∪ ℝ` near which the prefix hull lies inside `G_s`. -/
theorem ae_union_mean_cfGlueT_stage (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
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
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    {g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 =>
        recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g) :
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
              (𝓝[H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)] z₀)
              (𝓝 0)) ∧
        (∀ z₀ ∈ cfHullQ s p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∩ ball z₀ r ⊆
            cfHullQ s p.2) →
          Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
              (forceJumpFinset xL xR) u' s p.2 z)
            (𝓝[H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)] z₀)
            (𝓝 0)) := by
  have hcen : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
    funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
  obtain ⟨h𝔄, hAloc, hAl⟩ := exists_flowSide_schedule h44 hκ hκ4 c₀ hc₀ hh sc hE hreg hu₀c hn
  have hpm : Measurable (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1)) :=
    measurable_pastMap runMeasStatement c₀.isPiecewiseConstantBoundaryData (scheduleSpec sc) (k := n + 1)
      (fun j _ => hE.1 j) (fun j _ => hreg j) (n + 1) le_rfl
  have hAm := h𝔄.comp hpm
  have hFg := WholeField.isZeroBoundaryGFF_centredField hC hu₀
  obtain ⟨gA, hgA⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hFg hAm hAl
  have hℓ : n < (scheduleSpec sc).2.2.length := hn
  have hADpt : ∀ ω, H \ recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) ω) =
      ((stageChart κ c₀.fn c₀.jumps (scheduleSpec sc) (schedDelta 0 (scheduleList sc)) E n ω).dom : Set ℂ) := by
    intro ω
    rw [recHull_eq, Set.sdiff_sdiff_right_self, inter_eq_right.2 (dom_stageChart_subset c₀ sc n ω)]
  obtain ⟨wA, hwA, hwAeq⟩ := StagedFinal.exists_rep_stageMeanW c₀ hκ c₀.isPiecewiseConstantBoundaryData rfl
    (fun _ _ => rfl) hh hE hreg rfl (isFlowProg_scheduleProgram 0 _) (schedDelta_ne_top 0 _) hℓ hu₀c hAm hAl hAloc
    (Eventually.of_forall fun ω _ => hADpt ω) hgA
  rw [← hcen] at hAl hgA
  have hU := ae_union_mean_cfGlueT_flowSide hC hκ hθb hcf hlaw hk hu₀ hpm h𝔄 hAl
    (Eventually.of_forall fun ω => not_isBounded_lowerUnion_recHull sc n _) hgA hwA s hu' hg
  filter_upwards [hU] with p ⟨w, h1, h2, h3, h4⟩
  refine ⟨w, h1, h2, fun hgood z₀ hz₀ hr => ?_, h4⟩
  have e := hwAeq p.1 hgood (hADpt p.1)
  have hl := h3 z₀ hz₀ hr
  rw [e] at hl
  exact hl

end Stage

end InteractingSLE.Sec5.CrossCond.StagedAdapt
