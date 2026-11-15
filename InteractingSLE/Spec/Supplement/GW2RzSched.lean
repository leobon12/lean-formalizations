/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzInst
import InteractingSLE.Spec.Supplement.GW2RzShape
import InteractingSLE.Spec.Supplement.GW2SdhInst
import InteractingSLE.Spec.Supplement.GW2RzMono


/-!
# GW2 at a root `x`: the stage instance at the actual schedule (decision D8, layer 5, continued)

Packet PROVE-GW2-ROOTX, round 3. SDE's `GW2Sdh` (`schedInst`, `OpenLines`, `schedInst_good`) and STAGEMEAN's lines
constructor (`GW2Stl.StageInst.linesLocal_of`, `lines_thr`, `lines_int`) at the root point `x₀ = rootPt r.1`:

* `measurable_stgStartX_of_pre`, `measurable_stgRX`, `measurable_stgVX`;
* `stageMeanAtX`, `NoThresholdX`, `StageInst.lines_thrX`, `StageInst.lines_intX`, **`StageInst.linesLocalX_of`**;
* `aliveRecX` (live stage records at the root), `measurableSet_aliveRecX`, **`StageInst.E_good_of_recordX`**;
* `comap_stgPreRecX_le_aeSigma` (part (II) at the root, reduced to the explored path);
* `schedPhysUnionX` (the retained hull and the explored hull translated to the root, D8), `schedChartX`,
  **`schedInstX`**, **`OpenLinesX`** (the owners' open lines inputs at the root), **`schedInstX_good`**:
  `StageInst.GoodX` at the actual schedule from a root-`x` good set, an announced root-`x` version with finite
  stops, the word map's properties, a measurable record event, `u₀` and `OpenLinesX` (the physical union's shape is
  discharged by `GW2Rz.shape_of_unionX`);
* `exists_goodSet_schedX`, `schedGTX`, `schedGTX_spec`, **`schedInstX_good_of_rootx`** (the chosen good set).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Rz

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Rd GW2Sde GW2Sdf GW2Sdh GW2Stl Restart.DomainMarkov Restart.FCDet Sec7.PocketTraversal Supp8.RelSafeS
  GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 LocalSets WholeField

/-! ### Measurability of the root-`x` stage objects -/

section Stage

variable {Ω : Type*} [MeasurableSpace Ω] {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
  {GT : Set Ω} {V : Ω → ℝ≥0∞} {T : ℝ≥0} {R : ℝ≥0 → Ω → ℝ}

/-- The root-`x` stage start is read off the prefix record. -/
theorem measurable_stgStartX_of_pre (hpre : Measurable (stgPreRecX x₀ s Wα ζα W GT V T R)) :
    Measurable (stgStartX x₀ s Wα ζα W GT V T) := by
  have e : stgStartX x₀ s Wα ζα W GT V T = fun ω => (stgPreRecX x₀ s Wα ζα W GT V T R ω).2.1.toNNReal :=
    funext fun ω => (stgPreRec_timeX T R ω).symm
  rw [e]
  exact ENNReal.measurable_toNNReal.comp (measurable_fst.comp (measurable_snd.comp hpre))

/-- The root-`x` stage driver is measurable at every time. -/
theorem measurable_stgRX (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hpre : Measurable (stgPreRecX x₀ s Wα ζα W GT V T R)) (t : ℝ≥0) :
    Measurable (stgRX x₀ s Wα ζα W GT R V T t) :=
  measurable_stgDrv hRm hRc (measurable_stgStartX_of_pre hpre) t

/-- The root-`x` stage cap is measurable. -/
theorem measurable_stgVX (hVm : Measurable V) (hpre : Measurable (stgPreRecX x₀ s Wα ζα W GT V T R)) :
    Measurable (stgVX x₀ s Wα ζα W GT V T) :=
  hVm.sub (measurable_coe_nnreal_ennreal.comp (measurable_stgStartX_of_pre hpre))

end Stage

/-! ### The line data of a root-`x` stage -/

section Lines

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {c : SourceData Ω}
  {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {x₀ : ℝ}

/-- **The per-sample stage identity at the root `x₀`** (STAGEMEAN's `GW2Stl.stageMeanAt` with the root-`x` record,
chart, clock, driver and cap). -/
def stageMeanAtX (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (x₀ : ℝ) (w : WordType) (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens) (ω : Ω) (m : DistOn upperHalfPlaneOpens) :
    Prop :=
  ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l x₀) → I.clockX c x₀ t ω < I.capX c x₀ ω →
    Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) (I.clockX c x₀ t ω).toNNReal) →
    ∀ hc : (I.chartX c x₀ ω).IsConformal, Chart.chartTransport hc 1 I.σa I.kc
        (m + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens I.u₀) ψ =
      ∫ z, couplingMean c.κ (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) (I.clockX c x₀ t ω).toNNReal
        (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c x₀)
          (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
            (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))
          (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
            (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) ω
          (I.clockX c x₀ t ω).toNNReal) z * ψ z

/-- The physical no-threshold statement at the root `x₀` (STAGEMEAN's input of `GW2Stl.StageInst.lines_thr`). -/
def NoThresholdX (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (x₀ : ℝ) : Prop :=
  ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E → ∀ u : ℝ≥0, (u : ℝ≥0∞) < I.capX c x₀ ω →
    ¬ ForceWord.ThresholdCondition
      (flowLineRhoL c.κ (I.β (I.srecX c r l x₀ ω)).fn (I.β (I.srecX c r l x₀ ω)).jumps 0 0)
      (flowLineRhoR c.κ (I.β (I.srecX c r l x₀ ω)).fn (I.β (I.srecX c r l x₀ ω)).jumps 0 0)
      (I.drvX c x₀ u ω)
      (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -I.drvX c x₀ v.toNNReal ω)
        (-flowLineXL (I.β (I.srecX c r l x₀ ω)).fn (I.β (I.srecX c r l x₀ ω)).jumps 0 i) u)
      (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => I.drvX c x₀ v.toNNReal ω)
        (flowLineXR (I.β (I.srecX c r l x₀ ω)).fn (I.β (I.srecX c r l x₀ ω)).jumps 0 j) u)

/-- **`LinesLocalX.thr`** from the physical no-threshold statement (STAGEMEAN's `GW2Stl.StageInst.lines_thr`). -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.lines_thrX (I : StageInst Ω)
    (hv : IsRelVersionX x₀ c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRecX x₀ c.s c.W c.ζ I.W I.GT I.V I.T I.R)) (hβ : Measurable I.β)
    (hE : MeasurableSet I.E) (hHr : Measurable I.Hr) (hno : NoThresholdX I c r l x₀) (w : WordType) :
    ∀ᵐ y ∂((c.P.map fun ω => (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))[|
        typeEvent c.κ w I.β I.E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL c.κ w (I.β y.1))
        (fun y => typedXR c.κ w (I.β y.1)) y :=
  ae_canonStp_le_thr_of_noThreshold (measurable_augRec (measurable_stageEncRec c r l) hpre) hβ hE hHr
    (measurable_stgRX hv.1 hv.2.1 hpre) (fun ω => continuous_stgDrv (hv.2.1 ω) _) (fun _ => stgDrv_zero _ _)
    (measurable_stgVX hv.2.2.2.2.1 hpre) hno w

/-- **`LinesLocalX.int`** from the conditional GFF law of the stage field (STAGEMEAN's
`GW2Stl.StageInst.lines_int`). -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.lines_intX [StandardBorelSpace Ω] (I : StageInst Ω)
    (hv : IsRelVersionX x₀ c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRecX x₀ c.s c.W c.ζ I.W I.GT I.V I.T I.R)) (hβ : Measurable I.β)
    (hE : MeasurableSet I.E) (hHr : Measurable I.Hr) (h𝒢 : 𝒢 ≤ mΩ)
    (hrec : Measurable[𝒢] (I.srecX c r l x₀)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M)
    (hgff : ∀ᵐ ω₀ ∂c.P, I.srecX c r l x₀ ω₀ ∈ I.E →
      IsGFFWithBoundaryData (condExpKernel c.P 𝒢 ω₀) I.Hr (I.β (I.srecX c r l x₀ ω₀)).fn
        (I.β (I.srecX c r l x₀ ω₀)).jumps)
    (w : WordType) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun y => canonFld y φ)
      ((c.P.map fun ω => (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))[|
        typeEvent c.κ w I.β I.E]) :=
  integrable_canonFld_of_condGFF_word h𝒢 hrec hβ hE hHr (measurable_stgRX hv.1 hv.2.1 hpre)
    (measurable_stgVX hv.2.2.2.2.1 hpre) hM0 hM hgff w φ

/-- **The line data of a root-`x` stage** (STAGEMEAN's `GW2Stl.StageInst.linesLocal_of` at the root `x₀`): the
threshold and integrability fields are discharged. -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.linesLocalX_of [StandardBorelSpace Ω] (I : StageInst Ω)
    (hv : IsRelVersionX x₀ c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRecX x₀ c.s c.W c.ζ I.W I.GT I.V I.T I.R)) (hβ : Measurable I.β)
    (hE : MeasurableSet I.E) (hHr : Measurable I.Hr) (hWm : ∀ t, Measurable (I.W t)) (w : WordType)
    (htransport : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l x₀) →
      ∀ hc : (I.chartX c x₀ ω).IsConformal, Chart.chartTransport hc 1 I.σa I.kc (c.h ω) = I.Hr ω)
    (hharm : InnerProductSpace.HarmonicOnNhd I.u₀ H)
    (hzbgff : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h I.u₀) c.P)
    (hsets_le : ∀ t, stgFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) I.T (measurable_stageEncRec c r l) t ≤
      I.ℋ t)
    (hsets_amb : ∀ t, I.ℋ t ≤ mΩ) (hsets_meas : ∀ t, Measurable[mΩ, hittingSigma] (I.B t))
    (hsets_open : ∀ t ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P)
    (hshape : ∀ t : ℝ≥0, ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l x₀) →
      min (physClockX x₀ c.s c.W c.ζ I.W I.GT (I.T + t) ω) (I.V ω) < I.V ω →
      H \ I.B t ω = (relChartX x₀ c.s (cfRec c.s c.W c.ζ ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => I.R u ω)
          (min (physClockX x₀ c.s c.W c.ζ I.W I.GT (I.T + t) ω) (I.V ω)).toNNReal))
    (hmean : ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, stageMeanAtX I c r l x₀ w t ψ ω (g ω))
    (hno : NoThresholdX I c r l x₀)
    (h𝒢 : 𝒢 ≤ mΩ) (hrec : Measurable[𝒢] (I.srecX c r l x₀)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M)
    (hgff : ∀ᵐ ω₀ ∂c.P, I.srecX c r l x₀ ω₀ ∈ I.E →
      IsGFFWithBoundaryData (condExpKernel c.P 𝒢 ω₀) I.Hr (I.β (I.srecX c r l x₀ ω₀)).fn
        (I.β (I.srecX c r l x₀ ω₀)).jumps) :
    I.LinesLocalX c r l x₀ hWm w where
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
  int φ := StageInst.lines_intX I hv hpre hβ hE hHr h𝒢 hrec hM0 hM hgff w φ
  thr := StageInst.lines_thrX I hv hpre hβ hE hHr hno w

end Lines

/-! ### Live stage records at a root -/

/-- **The live stage records at the root `x₀`**: the decoded counterflow record is a good record at `x₀` and the stage
start is before the cap. -/
def aliveRecX (N : ℕ) (x₀ : ℝ) (s : ℝ≥0) (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) : Set RecData :=
  {z | augσ N z ∈ goodX x₀ s ∧ (augA z : ℝ≥0∞) < ρ (augσ N z, augPre z)}

theorem measurableSet_aliveRecX (N : ℕ) (x₀ : ℝ) (s : ℝ≥0) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρ : Measurable ρ) : MeasurableSet (aliveRecX N x₀ s ρ) := by
  have hpre : Measurable fun z => augPre z := measurable_pi_iff.2 fun t => measurable_augPre t
  exact ((measurable_augσ N) (measurableSet_goodX x₀ s)).inter
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_augA)
      (hρ.comp ((measurable_augσ N).prodMk hpre)))

/-- **`GoodX.E_good` from live stage records** (SDE's `GW2Sdf.StageInst.E_good_of_record` at the root `x₀`). -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.E_good_of_recordX {Ω : Type u} [MeasurableSpace Ω]
    {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {x₀ : ℝ} (I : StageInst Ω)
    (hv : IsRelVersionX x₀ c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V) (hρ : IsPathRule I.ρ)
    (hVρ : ∀ᵐ ω ∂c.P, I.V ω = I.ρ (cfRec c.s c.W c.ζ ω, fun u => I.R u ω))
    (hE : I.E ⊆ aliveRecX ((entryList l).length + 1) x₀ c.s I.ρ)
    (hfin : ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E → stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤) :
    ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E →
      cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s ∧ stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω < I.V ω := by
  filter_upwards [hVρ, hfin] with ω hV hf hEω
  obtain ⟨hd1, hd2, hd3⟩ := augDec_specX (x₀ := x₀) (s := c.s) (W := I.W) (Wα := c.W) (ζα := c.ζ) (GT := I.GT)
    (V := I.V) (T := I.T) (stgRecDec_stageEncRec c r l ω) (hv.2.1 ω) (hv.2.2.1 ω)
  obtain ⟨hgood, hlt⟩ := hE hEω
  rw [hd1] at hgood hlt
  refine ⟨hgood, ?_⟩
  have hS : ((stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0) : ℝ≥0∞) =
      stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω := ENNReal.coe_toNNReal (hf hEω)
  rw [← hS]
  by_contra hcon
  have hle : I.V ω ≤ (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞) := not_lt.1 hcon
  have hpr : I.ρ (gb6Rec c.s c.W c.ζ ω, augPre (I.srecX c r l x₀ ω)) =
      I.ρ (cfRec c.s c.W c.ζ ω, fun u => I.R u ω) := by
    refine hρ _ _ _ fun u hu => ?_
    have hu' : (u : ℝ≥0∞) ≤ (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞) := (hV ▸ hu).trans hle
    exact (hd3 u (hd2 ▸ ENNReal.coe_le_coe.1 hu')).symm
  rw [hd2, hpr, ← hV] at hlt
  exact absurd (hlt.trans_le hle) (lt_irrefl _)

/-! ### The prefix record is retained -/

/-- **Part (II) at the root `x₀`, reduced to the explored path** (SDE's `GW2Sde.comap_stgPreRec_le_aeSigma`). -/
theorem comap_stgPreRecX_le_aeSigma {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s)
    (hx₀ : 0 ≤ x₀) (hgb : Measurable (cfRec s Wα ζα)) (hWm : ∀ r, Measurable (W r)) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s Wα ζα ω ∈ goodX x₀ s) (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V)
    (T : ℝ≥0) (hrec𝒢 : MeasurableSpace.comap (cfRec s Wα ζα) inferInstance ≤ LocalSets.aeSigma 𝒢 P)
    (hW𝒢 : ∀ r ≤ T, MeasurableSpace.comap (W r) inferInstance ≤ LocalSets.aeSigma 𝒢 P) :
    MeasurableSpace.comap (stgPreRecX x₀ s Wα ζα W GT V T R) inferInstance ≤ LocalSets.aeSigma 𝒢 P := by
  have h1 := (measurable_stgPreRecX hGT hs₀ hx₀ hgb hWm
    (measurableSet_goodSetX_physFilt hgb hWm hGTm hGTae) hver T).comap_le
  refine h1.trans ?_
  rw [physFilt_apply]
  exact sup_le (sup_le hrec𝒢 (iSup₂_le fun r hr => hW𝒢 r hr)) (Supp8.Q3Chain.nullSets_le_aeSigma 𝒢)

/-! ### The schedule instance at a root -/

section Defs

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The root-`x` physical stage union** at the schedule: the retained counterflow hull and the explored hull at
`T + t` translated to the root point (decision D8). -/
def schedPhysUnionX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  Supp8.Q3Rel.invHull (rdrv (cfRec c.s c.W c.ζ ω)) c.s ∪
    (fun z : ℂ => z + (rootPt r.1 : ℝ)) ''
      fwdHull (fun s : ℝ => schedW c r l a s.toNNReal ω) ((historyTime c r l + t : ℝ≥0) : ℝ)

/-- The root-`x` stage chart of a version at the schedule. -/
def schedChartX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (ω : Ω) : Chart :=
  stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (fun t => R t ω)
    (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω)

/-- **The stage instance at the actual schedule from the root point** for a root-`x` good set `GT` and an announced
root-`x` version `hA` (SDE's `GW2Sdh.schedInst` at the root `rootPt r.1`). -/
def schedInstX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : SchedChoice Ω) : StageInst Ω where
  W := schedW c r l a
  γ := schedTr c r l a
  GT := GT
  R := R
  V := V
  ρ := hA.1.2.choose
  ρs := hA.2.choose
  T := historyTime c r l
  β := ch.β
  E := ch.E₀ ∩ aliveRecX ((entryList l).length + 1) (rootPt r.1) c.s hA.1.2.choose
  Hr := stgField ch.σa ch.kc c.h (schedChartX c r l a GT R V)
  σa := ch.σa
  kc := ch.kc
  u₀ := ch.u₀
  ℋ := ch.ℋ
  B := schedPhysUnionX c r l a

end Defs

/-- **The open lines inputs of a root-`x` instance** (SDE's `GW2Sdh.OpenLines` at the root `x₀`: RELDET's union
marks, measurability, openness and locality; STAGEMEAN's mean, no-threshold and conditional GFF inputs). -/
structure OpenLinesX {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (I : StageInst Ω)
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ)
    (hWm : ∀ t, Measurable (I.W t)) : Prop where
  sets_le : ∀ t, stgFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) I.T (GW2Sde.measurable_stageEncRec c r l) t ≤
    I.ℋ t
  sets_amb : ∀ t, I.ℋ t ≤ mΩ
  sets_meas : ∀ t, Measurable[mΩ, hittingSigma] (I.B t)
  sets_open : ∀ t ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω)
  loc : ∀ t, IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P
  mean : ∀ (w : WordType) (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
    IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
    ∀ᵐ ω ∂c.P, stageMeanAtX I c r l x₀ w t ψ ω (g ω)
  noThreshold : NoThresholdX I c r l x₀
  condGFF : ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : ℝ), Measurable[𝒢.1] (I.srecX c r l x₀) ∧ 0 ≤ M ∧
    (∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M) ∧
    ∀ᵐ ω₀ ∂c.P, I.srecX c r l x₀ ω₀ ∈ I.E →
      IsGFFWithBoundaryData (condExpKernel c.P 𝒢.1 ω₀) I.Hr (I.β (I.srecX c r l x₀ ω₀)).fn
        (I.β (I.srecX c r l x₀ ω₀)).jumps

section Good

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **`StageInst.GoodX` at the actual schedule from the root point** (SDE's `GW2Sdh.schedInst_good` at the root
`rootPt r.1 ≥ 0`): from a root-`x` good set, an announced root-`x` version with finite stops, the word map's three
properties, a measurable record event, a bounded harmonic extension of the boundary data, and the open lines inputs.
The shape of the physical union is discharged (`GW2Rz.shape_of_unionX`). -/
theorem schedInstX_good (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hopen : OpenLinesX (schedInstX c r l a GT hA ch) c r l (rootPt r.1) (measurable_schedW c r l a)) :
    (schedInstX c r l a GT hA ch).GoodX c r l (rootPt r.1) := by
  set I := schedInstX c r l a GT hA ch with hI
  have hWm : ∀ t, Measurable (I.W t) := measurable_schedW c r l a
  have hver : IsRelVersionXR (rootPt r.1) c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1
  have hv : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hρs := hA.2.choose_spec
  have hpre : Measurable (stgPreRecX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
    (measurable_stgPreRecX hGT.1 hs hx (measurable_gb6Rec_src c) hWm
      (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2) hver I.T).mono
      ((physFilt (measurable_gb6Rec_src c) hWm c.P).le I.T) le_rfl
  have hE : MeasurableSet I.E := hE₀.inter (measurableSet_aliveRecX _ _ c.s hρ.1)
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hHr : Measurable I.Hr :=
    measurable_stgField c.hh.1 (isMeasChart_stgChartX (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre)
  have hzb := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  obtain ⟨𝒢, M, hrec, hM0, hM, hgff⟩ := hopen.condGFF
  exact
    { s_pos := hs
      x_nonneg := hx
      physGood := hGT.1
      measurable_W := hWm
      measurableSet_GT := hGT.2.1
      GT_ae := hGT.2.2
      version := hv
      measurable_ρ := hρ.1
      isPathRule_ρ := hρ.2.1
      V_eq := hρ.2.2
      measurable_ρs := hρs.1
      isPathRule_ρs := hρs.2.1
      ρs_ne_top := hρs.2.2.1
      ρs_mono := hρs.2.2.2.1
      announce := hρs.2.2.2.2
      prefix_retained := comap_stgPreRecX_le_aeSigma hGT.1 hs hx (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2
        hver I.T ((GW2Rd.measurable_cfRec_sigma c r l).comap_le.trans (LocalSets.le_aeSigma _ _))
        fun t ht => (comap_schedW_le_sigma c r l a ht).trans (LocalSets.le_aeSigma _ _)
      measurable_β := hβ.1
      measurableSet_E := hE
      countable_wordType := hβ.2.1
      isSorted := fun y _ => hβ.2.2 y
      E_good := hEgood
      measurable_Hr := hHr
      lines := fun w => StageInst.linesLocalX_of I hv hpre hβ.1 hE hHr hWm w
        (Eventually.of_forall fun _ _ hc => chartTransport_eq_stgField hc) hu₀.1 hzb hopen.sets_le
        hopen.sets_amb hopen.sets_meas hopen.sets_open hopen.loc
        (shape_of_unionX hGT.1 hs hx hv hGT.2.2 (F := liveEvRec c.κ w I.β I.E (I.srecX c r l (rootPt r.1)))
          (hEgood.mono fun _ h hm => (h hm.1).1) I.T (fun _ _ => rfl))
        (hopen.mean w) hopen.noThreshold 𝒢.2 hrec hM0 hM hgff }

end Good

/-! ### The root-`x` good set and versions at the schedule, chosen -/

section Chosen

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The root-`x` good set at the schedule instance** (RELDET's `GW2Rd.exists_goodSet_sched` at the root
`rootPt r.1`). -/
theorem exists_goodSet_schedX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∃ GT : Set Ω, (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s) := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hcf : ∀ᵐ ω ∂c.P, c.ζ ω = ⊤ ∧ Continuous (c.W · ω) ∧ c.W 0 ω = 0 := by
    filter_upwards [GW1LaunchClock.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ] with ω h1 h2
    exact ⟨h2, h1.1, h1.2.1⟩
  exact exists_goodSetX hfl hα hcf (continuous_schedW c r l a) (schedW_zero c r l a)
    ((ae_schedW_regular h13 c r l a).mono fun _ h => h.2.2.1) (rootPt r.1) c.s

/-- **The root-`x` good set at the schedule instance**, chosen. -/
def schedGTX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Set Ω :=
  (exists_goodSet_schedX h13 c r l a).choose

theorem schedGTX_spec (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (∀ ω ∈ schedGTX h13 c r l a,
        PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet (schedGTX h13 c r l a) ∧
      (∀ᵐ ω ∂c.P, ω ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s) :=
  (exists_goodSet_schedX h13 c r l a).choose_spec

/-- **`StageInst.GoodX` at the actual schedule from the root point, with the chosen root-`x` good set.** -/
theorem schedInstX_good_of_rootx (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hopen : OpenLinesX (schedInstX c r l a (schedGTX h13 c r l a) hA ch) c r l (rootPt r.1)
      (measurable_schedW c r l a)) :
    (schedInstX c r l a (schedGTX h13 c r l a) hA ch).GoodX c r l (rootPt r.1) :=
  schedInstX_good c r l a hs hx (schedGTX_spec h13 c r l a) hA hV ch hβ hE₀ hu₀ hopen

end Chosen

end InteractingSLE.Theorem14.GW2Rz
