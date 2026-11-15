/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StlWord
import InteractingSLE.Spec.Supplement.GW2StlChart
import InteractingSLE.Spec.Supplement.GW2SfMeanCover

/-!
# GW2's stage lines, part 5: the stage mean through a stopped cover, and the line data of a stage

Packet PROVE-GW2-STAGEMEAN, stage-lines round (PROVE-GW2-SDE's `GW2Sde.StageInst.LinesLocal`). The union-mean
target `LinesLocal.mean` asks the stage identity for EVERY local-set mean of the physical union `B t`. As at stage `0`
(PROVE-GW2-SAFE's `gw2RdUnionMeanStatement_of_thm12_thm13`), it suffices to prove it for the means of countably many
STOPPED unions `A n` (marks determined by the field) that agree with a marked version of `B t` on events covering the
live event (`GW2Sf.ae_property_of_marked_stopped_cover`); on the conditional-kernel route the stopped means are
`GW2Stl.exists_chart_mean_stop_random` read through the stage chart.

* `stageMeanAt`: the per-sample stage identity of a distribution (the property inside `LinesLocal.mean`);
* **`StageInst.mean_of_cover`**: `LinesLocal.mean` at time `t` from the stage identity of the means of stopped
  unions covering the live event;
* **`StageInst.linesLocal_of`**: the line data `LinesLocal` of a stage from RELDET's locality fields, the union mean,
  the physical no-threshold statement (`StageInst.lines_thr`) and the conditional GFF law of the stage field
  (`StageInst.lines_int`) — the threshold and integrability fields are discharged.

Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Stl

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24
  LocalSets WholeField Supp8.RelSafeS

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {c : SourceData Ω}
  {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}

/-- **The per-sample stage identity** of a distribution `m` (the property inside `LinesLocal.mean`): on the live
event before the stage cap, for a test function off the stage hull, the chart transport of `m + u₀` by the stage chart
is the integral of the canonical coupling mean of the typed stage word along the stage driver. -/
def stageMeanAt (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (w : WordType) (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens) (ω : Ω) (m : DistOn upperHalfPlaneOpens) : Prop :=
  ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω →
    Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) (I.clock c t ω).toNNReal) →
    ∀ hc : (I.chart c ω).IsConformal, Chart.chartTransport hc 1 I.σa I.kc
        (m + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens I.u₀) ψ =
      ∫ z, couplingMean c.κ (fun s : ℝ => I.drv c s.toNNReal ω) (I.clock c t ω).toNNReal
        (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
          (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
            (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
          (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
            (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
          (I.clock c t ω).toNNReal) z * ψ z

/-- **The stage mean at time `t` through a stopped cover** (`GW2Sf.ae_property_of_marked_stopped_cover`): if the
physical union `B t` is marked local for `ℋ t`, agrees on an `ℋ t`-event `E` (containing the live event before the
cap) with an `ℋ t`-measurable version `C`, and countably many stopped unions `A n` with field-determined marks agree
with `C` on events `En n` covering `E` and satisfy the stage identity for every local-set mean, then every local-set
mean of `B t` satisfies it. -/
theorem StageInst.mean_of_cover [IsProbabilityMeasure c.P] (I : StageInst Ω) (w : WordType) (t : ℝ≥0)
    (ψ : TestOn upperHalfPlaneOpens)
    (hzero : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h I.u₀) c.P)
    (hℋ : I.ℋ t ≤ mΩ) (hN : Ito.nullSets c.P ≤ I.ℋ t) (hBm : Measurable[mΩ, hittingSigma] (I.B t))
    (hBc : ∀ ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hloc : IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P)
    {C : Ω → Set ℂ} (hC : Measurable[I.ℋ t, hittingSigma] C) (hCc : ∀ᵐ ω ∂c.P, C ω ⊆ H ∧ IsOpen (H \ C ω))
    (hBC : ∀ᵐ ω ∂c.P, I.B t ω ⊆ C ω) {E : Set Ω} (hE : MeasurableSet[I.ℋ t] E)
    (heB : ∀ᵐ ω ∂c.P, ω ∈ E → I.B t ω = C ω)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ E)
    {𝓜 : ℕ → MeasurableSpace Ω} {A : ℕ → Ω → Set ℂ} (h𝓜 : ∀ n, 𝓜 n ≤ mΩ)
    (h𝓜N : ∀ n, Ito.nullSets c.P ≤ 𝓜 n)
    (h𝓜d : ∀ n, 𝓜 n ≤ aeSigma (MeasurableSpace.comap (centredField c.h I.u₀) inferInstance) c.P)
    (hA : ∀ n, Measurable[𝓜 n, hittingSigma] (A n)) (hAc : ∀ n, ∀ᵐ ω ∂c.P, A n ω ⊆ H ∧ IsOpen (H \ A n ω))
    (hlA : ∀ n, IsHistoryAvoidanceLocal (𝓜 n) (A n) (centredField c.h I.u₀) c.P)
    (hAC : ∀ n, ∀ᵐ ω ∂c.P, A n ω ⊆ C ω) {En : ℕ → Set Ω} (hEn : ∀ n, MeasurableSet[𝓜 n] (En n))
    (heA : ∀ n, ∀ᵐ ω ∂c.P, ω ∈ En n → A n ω = C ω) (hcover : ∀ᵐ ω ∂c.P, ω ∈ E → ∃ n, ω ∈ En n)
    (hQ : ∀ n (gA : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (A n) (centredField c.h I.u₀) c.P gA →
      ∀ᵐ ω ∂c.P, ω ∈ En n → stageMeanAt I c r l w t ψ ω (gA ω))
    (g : Ω → DistOn upperHalfPlaneOpens) (hg : IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g) :
    ∀ᵐ ω ∂c.P, stageMeanAt I c r l w t ψ ω (g ω) := by
  have h := GW2Sf.ae_property_of_marked_stopped_cover hzero hℋ hN hBm hC (Eventually.of_forall hBc) hCc hloc hBC
    hE heB h𝓜 h𝓜N h𝓜d hA hAc hlA hAC hEn heA hcover hQ hg
  filter_upwards [h, hlive] with ω hω hl hlv hlt
  exact hω (hl hlv hlt) hlv hlt

/-- **The line data of a stage**: RELDET's locality fields, the union mean (in the form of `stageMeanAt`), the
physical no-threshold statement of the stage word along the stage driver and the conditional GFF law of the stage
field give `LinesLocal`; the threshold and integrability fields are discharged by `StageInst.lines_thr` and
`StageInst.lines_int`. -/
theorem StageInst.linesLocal_of [StandardBorelSpace Ω] (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (hβ : Measurable I.β)
    (hE : MeasurableSet I.E) (hHr : Measurable I.Hr) (hWm : ∀ t, Measurable (I.W t)) (w : WordType)
    (htransport : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) →
      ∀ hc : (I.chart c ω).IsConformal, Chart.chartTransport hc 1 I.σa I.kc (c.h ω) = I.Hr ω)
    (hharm : InnerProductSpace.HarmonicOnNhd I.u₀ H)
    (hzbgff : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h I.u₀) c.P)
    (hsets_le : ∀ t, stgFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) I.T (measurable_stageEncRec c r l) t ≤
      I.ℋ t)
    (hsets_amb : ∀ t, I.ℋ t ≤ mΩ) (hsets_meas : ∀ t, Measurable[mΩ, hittingSigma] (I.B t))
    (hsets_open : ∀ t ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P)
    (hshape : ∀ t : ℝ≥0, ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) →
      min (physClock c.s I.W c.W c.ζ I.GT (I.T + t) ω) (I.V ω) < I.V ω →
      H \ I.B t ω = (relChart (gb6Rec c.s c.W c.ζ ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => I.R u ω) (min (physClock c.s I.W c.W c.ζ I.GT (I.T + t) ω) (I.V ω)).toNNReal))
    (hmean : ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, stageMeanAt I c r l w t ψ ω (g ω))
    (hno : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → ∀ u : ℝ≥0, (u : ℝ≥0∞) < I.cap c ω →
      ¬ ForceWord.ThresholdCondition
        (flowLineRhoL c.κ (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 0)
        (flowLineRhoR c.κ (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 0)
        (I.drv c u ω)
        (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -I.drv c v.toNNReal ω)
          (-flowLineXL (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 i) u)
        (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => I.drv c v.toNNReal ω)
          (flowLineXR (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 j) u))
    (h𝒢 : 𝒢 ≤ mΩ) (hrec : Measurable[𝒢] (I.srec c r l)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M)
    (hgff : ∀ᵐ ω₀ ∂c.P, I.srec c r l ω₀ ∈ I.E →
      IsGFFWithBoundaryData (condExpKernel c.P 𝒢 ω₀) I.Hr (I.β (I.srec c r l ω₀)).fn
        (I.β (I.srec c r l ω₀)).jumps) :
    I.LinesLocal c r l hWm w where
  transport := htransport
  harmonic := hharm
  zbgff := hzbgff
  sets_le := hsets_le
  sets_le_ambient := hsets_amb
  sets_meas := hsets_meas
  sets_open := hsets_open
  loc := hloc
  shape := hshape
  mean t g hg ψ := hmean t g hg ψ
  int φ := StageInst.lines_int I hv hpre hβ hE hHr h𝒢 hrec hM0 hM hgff w φ
  thr := StageInst.lines_thr I hv hpre hβ hE hHr hno w

end InteractingSLE.Theorem14.GW2Stl
