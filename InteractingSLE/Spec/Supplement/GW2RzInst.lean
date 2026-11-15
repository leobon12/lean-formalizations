/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzLaw
import InteractingSLE.Spec.Supplement.GW2SdeNeeds


/-!
# GW2 at a root `x`: the root-generic stage instance and its engine (decision D8, layer 5, continued)

Packet PROVE-GW2-ROOTX, round 3. Decision D8 gives the stage instance the root point as a parameter (D8's chart
`((relChart rec).recenter (relBase x s rec)).loewner R a`, `GW2Rz.relChartX`). The instance data are SDE's
`GW2Sde.StageInst`; the root `x₀` enters the derived objects and the targets:

* `stgRX`, `stgVX`, `stgRecX`, `augStageVarX`, **`isSafe_augStageVarX`** (SDE's `GW2SdeAug` at the root `x₀`);
* `StageInst.srecX`, `drvX`, `capX`, `chartX`, `clockX`, **`StageInst.varX`**;
* **`StageInst.LinesLocalX`**, **`StageInst.GoodX`**, `StageStop.GoodX`: the targets of `StageInst.LinesLocal`,
  `StageInst.Good`, `StageStop.Good` with the root-`x` physical layer (good set `PhysGoodX` a.s. equal to the good
  records `goodX x₀ s`, the root-`x` version `IsRelVersionX`, the root-`x` prefix record and stage start), plus
  `0 < s` and `0 ≤ x₀`;
* **the engine**: `StageInst.GoodX.measurable_pre`, **`GoodX.hasRelSafe`** (via `GW2Rz.hasRelSafe_stageX'`),
  **`GoodX.isSafe`**, **`GoodX.generates`**, **`GoodX.generates_isSafe`** (`Good ⇒ Generates ∧ IsSafe`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Rz

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Rd GW2Sde Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.PocketTraversal Supp8.RelSafeS Restart.FCDet
  GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4 LocalSets

/-! ### The root-`x` stage variable -/

section Defs

variable {Ω : Type u}

/-- The root-`x` stage relative driver: the relative driver restarted at the root-`x` stage start. -/
abbrev stgRX (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (T : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => stgDrv (fun u => R u ω) (stgStartX x₀ s Wα ζα W GT V T ω) t

/-- The root-`x` stage cap: the cap minus the root-`x` stage start. -/
abbrev stgVX (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (V : Ω → ℝ≥0∞) (T : ℝ≥0) : Ω → ℝ≥0∞ :=
  fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω

/-- The augmented stage record: the stage-start history `x` with the record of the relative prefix. -/
abbrev stgRecX (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (T : ℝ≥0) (x : Ω → RecData) : Ω → RecData :=
  augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)

/-- **The stage variable of stage `T`** on the augmented record: the augmented record, the stage driver and cap, the
stage rules of the global cap rules with the exact decoders, and the given word, record event, stage field and
physical stop. -/
def augStageVarX (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (T : ℝ≥0) (x : Ω → RecData) (N : ℕ) (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) (β : RecData → BoundaryWord) (E : Set RecData)
    (Hr : Ω → DistOn upperHalfPlaneOpens) (stop : Ω → ℝ≥0∞) (stopRule : RecData → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞) :
    StageVar Ω where
  record := stgRecX x₀ s Wα ζα W GT R V T x
  β := β
  E := E
  Hr := Hr
  R := stgRX x₀ s Wα ζα W GT R V T
  V := stgVX x₀ s Wα ζα W GT V T
  ρ := stageRule ρ (augσ N) augA augPre
  ρs := fun n => stageRule (ρs n) (augσ N) augA augPre
  stop := stop
  stopRule := stopRule

end Defs

/-- **The safe stage law of the augmented stage variable**: the engine conditions at the stage are derived from the
global announced version (conditional helper: the stage `HasRelSafe`, the good live record event, the word
properties and the stop data are hypotheses). -/
theorem isSafe_augStageVarX {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (hv : IsRelVersionX x₀ s P Wα ζα W γ α R V) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρm : Measurable ρ) (hρ : IsPathRule ρ) (hVρ : ∀ᵐ ω ∂P, V ω = ρ (cfRec s Wα ζα ω, fun u => R u ω))
    {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n)) (hρs : ∀ n, IsPathRule (ρs n))
    (hρsfin : ∀ n y, ρs n y ≠ ⊤) (hρsmono : ∀ y, Monotone fun n => ρs n y)
    (hann : ∀ᵐ ω ∂P, cfRec s Wα ζα ω ∈ goodX x₀ s → (∀ n, ρs n (cfRec s Wα ζα ω, fun u => R u ω) < V ω) ∧
      ⨆ n, ρs n (cfRec s Wα ζα ω, fun u => R u ω) = V ω)
    {T : ℝ≥0} {N : ℕ} {x : Ω → RecData} (hx : Measurable x) (hxrec : ∀ ω, stgRecDec N (x ω) = cfRec s Wα ζα ω)
    (hpre : Measurable (stgPreRecX x₀ s Wα ζα W GT V T R)) {κ : ℝ} {β : RecData → BoundaryWord} (hβ : Measurable β)
    {E : Set RecData} (hE : MeasurableSet E) (hcount : (range fun r : RecData => wordType κ (β r)).Countable)
    (hsort : ∀ r ∈ E, (β r).IsSorted)
    (hEgood : ∀ᵐ ω ∂P, stgRecX x₀ s Wα ζα W GT R V T x ω ∈ E →
      cfRec s Wα ζα ω ∈ goodX x₀ s ∧ (stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0∞) < V ω)
    {Hr : Ω → DistOn upperHalfPlaneOpens} (hHr : Measurable Hr)
    (hS : ∀ w : WordType, HasRelSafe κ w β E (P.map fun ω => (stgRecX x₀ s Wα ζα W GT R V T x ω,
      relVar Hr (stgRX x₀ s Wα ζα W GT R V T) (stgVX x₀ s Wα ζα W GT V T) ω)))
    {stop : Ω → ℝ≥0∞} {stopRule : RecData → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞}
    (hstopRule : ∀ (y : RecData) (t : ℝ≥0), MeasurableSet[pathKilledSigma t] {e | stopRule y e ≤ (t : ℝ≥0∞)})
    (hstopm : Measurable stop)
    (hstopEq : ∀ᵐ ω ∂P, stop ω = stopRule (stgRecX x₀ s Wα ζα W GT R V T x ω)
      ((fun t => stgRX x₀ s Wα ζα W GT R V T t ω), stgVX x₀ s Wα ζα W GT V T ω))
    (hstopLe : ∀ᵐ ω ∂P, stgRecX x₀ s Wα ζα W GT R V T x ω ∈ E → stop ω ≤ stgVX x₀ s Wα ζα W GT V T ω)
    (hstopLt : ∀ᵐ ω ∂P, stgRecX x₀ s Wα ζα W GT R V T x ω ∈ E → stop ω ≠ ⊤ →
      stop ω < stgVX x₀ s Wα ζα W GT V T ω) :
    (augStageVarX x₀ s Wα ζα W GT R V T x N ρ ρs β E Hr stop stopRule).IsSafe κ P
      (stgRecX x₀ s Wα ζα W GT R V T x) := by
  have hRm := hv.1
  have hRc := hv.2.1
  have hR0 := hv.2.2.1
  have hVm := hv.2.2.2.2.1
  set z : Ω → RecData := stgRecX x₀ s Wα ζα W GT R V T x with hzdef
  have hz : Measurable z := measurable_augRec hx hpre
  have hdec : ∀ ω, augσ N (z ω) = cfRec s Wα ζα ω ∧ augA (z ω) = stgStartX x₀ s Wα ζα W GT V T ω ∧
      ∀ t ≤ augA (z ω), augPre (z ω) t = R t ω := fun ω => augDec_specX (hxrec ω) (hRc ω) (hR0 ω)
  have hAe : ∀ ω, augA (z ω) = stgStartX x₀ s Wα ζα W GT V T ω := fun ω => (hdec ω).2.1
  set G : Set Ω := {ω | cfRec s Wα ζα ω ∈ goodX x₀ s ∧ (stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0∞) < V ω} with hGdef
  obtain ⟨hRnm, hRnc, hRn0, hVnm, hV0, hVρn, hρsfin', hρsmono', hlt, hsup⟩ :=
    stgVersion_inputs_ae (P := P) hRm hRc hVm hz hVρ hρsfin hρsmono (G := G)
      (hann.mono fun ω h hG => h hG.1) measurable_augA (Eventually.of_forall fun ω => continuous_augPre (z ω))
      (Eventually.of_forall fun ω => ⟨(hdec ω).1, (hdec ω).2.2⟩)
      (Eventually.of_forall fun ω hG => (hAe ω).symm ▸ hG.2)
  simp only [hAe] at hRnm hRnc hRn0 hVnm hV0 hVρn hlt hsup
  have hEG : ∀ᵐ ω ∂P, z ω ∈ E → ω ∈ G := hEgood
  refine ⟨hβ, hE, hcount, hsort, hHr, hRnm, hRnc, hRn0, hVnm, hS, ?_,
    measurable_stageRule hρm (measurable_augσ N) measurable_augA measurable_augPre,
    isPathRule_stageRule hρ (augσ N) augA augPre, hVρn,
    fun n => measurable_stageRule (hρsm n) (measurable_augσ N) measurable_augA measurable_augPre,
    fun n => isPathRule_stageRule (hρs n) (augσ N) augA augPre, hρsfin', hρsmono', ?_, ?_, hstopRule, hstopm,
    hstopEq, hstopLe, hstopLt⟩
  · filter_upwards [hV0, hEG] with ω h1 h2 hm using h1 (h2 hm)
  · filter_upwards [hlt, hEG] with ω h1 h2 hm using h1 (h2 hm)
  · filter_upwards [hsup, hEG] with ω h1 h2 hm using h1 (h2 hm)


/-! ### The root-`x` stage instance -/

section Inst

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The augmented stage record of an instance at the root `x₀` after history `l`. -/
abbrev _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.srecX (I : StageInst Ω) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ) : Ω → RecData :=
  stgRecX x₀ c.s c.W c.ζ I.W I.GT I.R I.V I.T (GW2Rd.stageEncRec c r l)

/-- The stage relative driver of an instance at the root `x₀`. -/
abbrev _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.drvX (I : StageInst Ω) (c : SourceData Ω) (x₀ : ℝ) :
    ℝ≥0 → Ω → ℝ :=
  stgRX x₀ c.s c.W c.ζ I.W I.GT I.R I.V I.T

/-- The stage cap of an instance at the root `x₀`. -/
abbrev _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.capX (I : StageInst Ω) (c : SourceData Ω) (x₀ : ℝ) :
    Ω → ℝ≥0∞ :=
  stgVX x₀ c.s c.W c.ζ I.W I.GT I.V I.T

/-- **The stage chart of an instance at the root `x₀`** (decision D8): GB6's relative chart re-centred at the root,
then the centred Loewner map of the relative driver at the stage start. -/
abbrev _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.chartX (I : StageInst Ω) (c : SourceData Ω) (x₀ : ℝ)
    (ω : Ω) : Chart :=
  stgChart (relChartX x₀ c.s (cfRec c.s c.W c.ζ ω)) (fun t => I.R t ω) (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω)

/-- The stage clock of an instance at the root `x₀`. -/
abbrev _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.clockX (I : StageInst Ω) (c : SourceData Ω) (x₀ : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  stgClockX x₀ c.s c.W c.ζ I.W I.GT I.V I.T t ω

/-- **The stage variable of an instance at the root `x₀`** with a physical stop. -/
def _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.varX (I : StageInst Ω) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ) (st : StageStop Ω) : StageVar Ω :=
  augStageVarX x₀ c.s c.W c.ζ I.W I.GT I.R I.V I.T (GW2Rd.stageEncRec c r l) ((entryList l).length + 1) I.ρ I.ρs
    I.β I.E I.Hr st.stop st.rule

end Inst

/-- **The stage line data of one word type at the root `x₀`** (`StageInst.LinesLocal` with the root-`x` record,
chart, clock, driver and cap; targets for RELDET and STAGEMEAN). -/
structure _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.LinesLocalX {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ)
    (hWm : ∀ t, Measurable (I.W t)) (w : WordType) : Prop where
  transport : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l x₀) →
    ∀ hc : (I.chartX c x₀ ω).IsConformal, Chart.chartTransport hc 1 I.σa I.kc (c.h ω) = I.Hr ω
  harmonic : InnerProductSpace.HarmonicOnNhd I.u₀ H
  zbgff : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField c.h I.u₀) c.P
  sets_le : ∀ t, stgFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) I.T (measurable_stageEncRec c r l) t ≤ I.ℋ t
  sets_le_ambient : ∀ t, I.ℋ t ≤ mΩ
  sets_meas : ∀ t, Measurable[mΩ, hittingSigma] (I.B t)
  sets_open : ∀ t ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω)
  loc : ∀ t, WholeField.IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (WholeField.centredField c.h I.u₀) c.P
  shape : ∀ t : ℝ≥0, ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l x₀) →
    min (physClockX x₀ c.s c.W c.ζ I.W I.GT (I.T + t) ω) (I.V ω) < I.V ω →
    H \ I.B t ω = (relChartX x₀ c.s (cfRec c.s c.W c.ζ ω)).2.1 ''
      (H \ fwdHull (Ito.rpath fun u => I.R u ω)
        (min (physClockX x₀ c.s c.W c.ζ I.W I.GT (I.T + t) ω) (I.V ω)).toNNReal)
  mean : ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
    IsLocalSetMean (I.B t) (WholeField.centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
    ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l x₀) → I.clockX c x₀ t ω < I.capX c x₀ ω →
    Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) (I.clockX c x₀ t ω).toNNReal) →
    ∀ hc : (I.chartX c x₀ ω).IsConformal, Chart.chartTransport hc 1 I.σa I.kc
        (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens I.u₀) ψ =
      ∫ z, couplingMean c.κ (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) (I.clockX c x₀ t ω).toNNReal
        (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c x₀)
          (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
            (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))
          (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
            (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) ω
          (I.clockX c x₀ t ω).toNNReal) z * ψ z
  int : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun y => canonFld y φ)
    ((c.P.map fun ω => (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))[|typeEvent c.κ w I.β I.E])
  thr : ∀ᵐ y ∂((c.P.map fun ω => (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))[|
      typeEvent c.κ w I.β I.E]),
    canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL c.κ w (I.β y.1))
      (fun y => typedXR c.κ w (I.β y.1)) y

/-- **The per-stage inputs of an instance at the root `x₀`** (`StageInst.Good` with the root-`x` physical layer:
the root-`x` good set and version, the good records `goodX`, the root-`x` prefix record and stage start). -/
structure _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.GoodX {Ω : Type u} [MeasurableSpace Ω]
    (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ) :
    Prop where
  s_pos : 0 < c.s
  x_nonneg : 0 ≤ x₀
  physGood : ∀ ω ∈ I.GT, PhysGoodX x₀ c.s c.W c.ζ I.W I.γ c.α ω
  measurable_W : ∀ t, Measurable (I.W t)
  measurableSet_GT : MeasurableSet I.GT
  GT_ae : ∀ᵐ ω ∂c.P, ω ∈ I.GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s
  version : IsRelVersionX x₀ c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V
  measurable_ρ : Measurable I.ρ
  isPathRule_ρ : IsPathRule I.ρ
  V_eq : ∀ᵐ ω ∂c.P, I.V ω = I.ρ (cfRec c.s c.W c.ζ ω, fun u => I.R u ω)
  measurable_ρs : ∀ n, Measurable (I.ρs n)
  isPathRule_ρs : ∀ n, IsPathRule (I.ρs n)
  ρs_ne_top : ∀ n y, I.ρs n y ≠ ⊤
  ρs_mono : ∀ y, Monotone fun n => I.ρs n y
  announce : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s →
    (∀ n, I.ρs n (cfRec c.s c.W c.ζ ω, fun u => I.R u ω) < I.V ω) ∧
      ⨆ n, I.ρs n (cfRec c.s c.W c.ζ ω, fun u => I.R u ω) = I.V ω
  prefix_retained : MeasurableSpace.comap (stgPreRecX x₀ c.s c.W c.ζ I.W I.GT I.V I.T I.R) inferInstance ≤
    LocalSets.aeSigma (c.sigma r l) c.P
  measurable_β : Measurable I.β
  measurableSet_E : MeasurableSet I.E
  countable_wordType : (range fun y : RecData => wordType c.κ (I.β y)).Countable
  isSorted : ∀ y ∈ I.E, (I.β y).IsSorted
  E_good : ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E →
    cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s ∧ stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω < I.V ω
  measurable_Hr : Measurable I.Hr
  lines : ∀ w : WordType, I.LinesLocalX c r l x₀ measurable_W w

/-- **The physical stop of a comparison at the root `x₀`**: a protected stopping rule of the stage killed path. -/
structure _root_.InteractingSLE.Theorem14.GW2Sde.StageStop.GoodX {Ω : Type u} [MeasurableSpace Ω]
    (st : StageStop Ω) (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ) : Prop where
  rule_meas : ∀ (y : RecData) (t : ℝ≥0), MeasurableSet[pathKilledSigma t] {e | st.rule y e ≤ (t : ℝ≥0∞)}
  measurable_stop : Measurable st.stop
  stop_eq : ∀ᵐ ω ∂c.P, st.stop ω = st.rule (I.srecX c r l x₀ ω) ((fun t => I.drvX c x₀ t ω), I.capX c x₀ ω)
  stop_le : ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E → st.stop ω ≤ I.capX c x₀ ω
  stop_lt : ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E → st.stop ω ≠ ⊤ → st.stop ω < I.capX c x₀ ω

/-! ### The engine at the root `x₀` -/

section Good

variable {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)} {x₀ : ℝ} {I : StageInst Ω}

/-- The root-`x` prefix record is measurable (ambient). -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.GoodX.measurable_pre (hI : I.GoodX c r l x₀) :
    Measurable (stgPreRecX x₀ c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
  (measurable_stgPreRecX hI.physGood hI.s_pos hI.x_nonneg (measurable_gb6Rec_src c) hI.measurable_W
    (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hI.measurable_W hI.measurableSet_GT hI.GT_ae)
    ⟨hI.version, I.ρ, hI.measurable_ρ, hI.isPathRule_ρ, hI.V_eq⟩ I.T).mono
    ((physFilt (measurable_gb6Rec_src c) hI.measurable_W c.P).le I.T) le_rfl

/-- **The stage K2 law of a good instance at the root `x₀`** (`GW2Rz.hasRelSafe_stageX'`). -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.GoodX.hasRelSafe (hI : I.GoodX c r l x₀) (w : WordType) :
    HasRelSafe c.κ w I.β I.E (c.P.map fun ω => (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) := by
  have hL := hI.lines w
  have hver : IsRelVersionXR x₀ c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V :=
    ⟨hI.version, I.ρ, hI.measurable_ρ, hI.isPathRule_ρ, hI.V_eq⟩
  exact hasRelSafe_stageX' hI.measurable_β hI.measurableSet_E c.hh.1 hI.measurable_Hr hI.physGood hI.s_pos
    hI.x_nonneg (measurable_gb6Rec_src c) hI.measurable_W hI.measurableSet_GT hI.GT_ae hver I.T
    (measurable_stageEncRec c r l) I.σa I.kc (hL.transport.mono fun ω h hm => h hm _)
    (hI.E_good.mono fun ω h hm => (h hm.1).1) (hI.E_good.mono fun ω h hm => ne_top_of_lt (h hm.1).2)
    hL.harmonic hL.zbgff I.ℋ hL.sets_le hL.sets_le_ambient I.B hL.sets_meas hL.sets_open hL.loc hL.shape
    (fun t g hg ψ => (hL.mean t g hg ψ).mono fun ω h h1 h2 h3 => h h1 h2 h3 _) hL.int hL.thr

/-- **The safe stage law of the stage variable of a good instance at the root `x₀`.** -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.GoodX.isSafe (hI : I.GoodX c r l x₀) {st : StageStop Ω}
    (hst : st.GoodX I c r l x₀) : (I.varX c r l x₀ st).IsSafe c.κ c.P (I.varX c r l x₀ st).record := by
  refine isSafe_augStageVarX hI.version hI.measurable_ρ hI.isPathRule_ρ hI.V_eq hI.measurable_ρs hI.isPathRule_ρs
    hI.ρs_ne_top hI.ρs_mono hI.announce (measurable_stageEncRec c r l) (stgRecDec_stageEncRec c r l)
    hI.measurable_pre hI.measurable_β hI.measurableSet_E hI.countable_wordType hI.isSorted ?_ hI.measurable_Hr
    hI.hasRelSafe hst.rule_meas hst.measurable_stop hst.stop_eq hst.stop_le hst.stop_lt
  filter_upwards [hI.E_good] with ω h hE
  refine ⟨(h hE).1, ?_⟩
  rw [ENNReal.coe_toNNReal (ne_top_of_lt (h hE).2)]
  exact (h hE).2

/-- **The augmented record of a good instance at the root `x₀` generates `c.sigma r l`** up to null sets. -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.GoodX.generates (hI : I.GoodX c r l x₀) (st : StageStop Ω) :
    (I.varX c r l x₀ st).Generates (𝒢 := c.sigma r l) c.P :=
  generates_augRec rfl (measurable_stageEncRec c r l) hI.measurable_pre (GW2Rd.comap_stageEncRec_sigma c r l)
    hI.prefix_retained

/-- **The root-`x` engine**: a good instance at the root `x₀` with a good physical stop gives a stage variable that
generates `c.sigma r l` and is safe. -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageInst.GoodX.generates_isSafe (hI : I.GoodX c r l x₀)
    {st : StageStop Ω} (hst : st.GoodX I c r l x₀) :
    (I.varX c r l x₀ st).Generates (𝒢 := c.sigma r l) c.P ∧
      (I.varX c r l x₀ st).IsSafe c.κ c.P (I.varX c r l x₀ st).record :=
  ⟨hI.generates st, hI.isSafe hst⟩

end Good

end InteractingSLE.Theorem14.GW2Rz
