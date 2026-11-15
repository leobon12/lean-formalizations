/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeAug
import InteractingSLE.Spec.Supplement.GW2SqFilt
import InteractingSLE.Spec.Supplement.GW2RdRootLink
import InteractingSLE.Spec.Supplement.Q3ChainDet
import InteractingSLE.Spec.Supplement.GW2SdeWire

/-!
# GW2's retained stopped SDE: the per-stage inputs still missing (precise targets)

Packet PROVE-GW2-SDE (round 2). `FrameSafeStatement D F` (`GW2SdeWire`) is now reduced to LOWER-LEVEL per-stage
inputs. For each source `c`, root `r`, history `l` and candidate `a`, the future piece is described by a
`StageInst`: GB6's relative exploration with the counterflow `(c.W, c.ζ, c.α)` retained at `c.s` and the joined
schedule `W` explored, an announced version `(R, V, ρ, ρs)`, the physical stage start `T`, the stage word map `β`,
record event `E`, stage field `Hr` and the stage line data. The stage record is RELDET's augmented record
`augRec (stageEncRec c r l) (stgPreRec …)` and the stage variable is `augStageVar` (`StageInst.var`).

**What is proved here:** from `StageInst.Good` and `StageStop.Good`,
* the stage K2 law `HasRelSafe` on every word type (`StageInst.Good.hasRelSafe`, via PROVE-GW2-RELDET's
  `GW2Rd.hasRelSafe_stage'`: stage filtration enlarged by the stage history, kernels from the marked locality);
* the stage shape from GB6's shape when the physical union is the counterflow's retained set together with the
  explored hull at `T + t` (`shape_of_union`);
* `StageVar.IsSafe` of the stage variable (`StageInst.Good.isSafe`, via `isSafe_augStageVar`): the stage engine
  conditions are derived from the global version;
* `StageVar.Generates (c.sigma r l)` of the augmented record (`StageInst.Good.generates`, via `generates_augRec`);
* **`frameSafeStatement_of_pkgGood`** and **`retainedStoppedSDEStatement_of_pkgGood`**.

**The precise targets** (fields of `StageInst.Good`, `StageInst.LinesLocal`, `StageStop.Good`, `FrameWordStatement`):

* GB6's good set at the schedule instance (RELDET, with SWITCH's joined trace): `physGood`, `measurable_W`,
  `measurableSet_GT`, `GT_ae`;
* the announced GB6 version (`IsGB6RelVersionA`) at the schedule instance (RELDET): `version`, `measurable_ρ`,
  `isPathRule_ρ`, `V_eq`, `measurable_ρs`, `isPathRule_ρs`, `ρs_ne_top`, `ρs_mono`, `announce`;
* part (II): `prefix_retained` — the relative prefix record is `c.sigma r l`-measurable up to null sets; reduced by
  `StageInst.prefix_retained_of_path` to the explored driver on `[0, T]` being so, and DISCHARGED (`GW2SdePrefix`,
  `StageInst.prefix_retained_of_joined_historyTime`) when the stage starts at ROOT2's `historyTime` and the explored
  driver up to it is ROOT2's joined future driver;
* the stage word map and its record event (RELDET / STAGEMEAN): `measurable_β`, `measurableSet_E`,
  `countable_wordType`, `isSorted`;
* `E_good` (RELDET): good counterflow record and a live stage on `E`; reduced by `StageInst.E_good_of` to
  `E ⊆ {augσ ∈ gb6TS}` plus the stage being alive (`stgStartM < V`);
* `LinesLocal.transport`, `measurable_Hr`: DISCHARGED for the canonical stage field
  `Hr := stgField σa kc c.h (I.chart c)` (`chartTransport_eq_stgField`, `measurable_stgField_inst`);
* the stage union and its locality (RELDET, `exists_union_stageSet_gw2`): `LinesLocal.harmonic`, `.zbgff`,
  `.sets_le` (marks containing `physFilt (T + t) ⊔ σ(x)`), `.sets_le_ambient`, `.sets_meas`, `.sets_open`, `.loc`;
* `LinesLocal.shape`: GB6's whole-exploration shape of `B t` at `T + t`; DISCHARGED for the physical union
  (`StageInst.shape_of_physUnion`);
* `LinesLocal.mean` (STAGEMEAN, `exists_unionMean_gw2_pathStop`): every local-set mean of `B t`, plus `u₀`, read in
  the stage chart, is the coupling mean of the stage word;
* `LinesLocal.thr`, `.int` (STAGEMEAN, `ae_no_threshold_gw2_random`; `int` as in `BW1In.integrable_canonFld_bw`):
  the threshold before the stage stop and the integrability;
* `StageStop.Good` (ROOT2): the physical stop is a protected stopping rule of the stage killed path;
* `FrameWordStatement` (ROOT2 / near-comparison work): the frame's words present the stage's flow-line word.

The line kernels (`hker`) are DERIVED from the marked locality (`GW2Rd.hasRelSafe_stage'`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Sde

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Rd Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.PocketTraversal Supp8.RelSafeS Restart.FCDet
  GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4 LocalSets

/-- The counterflow record of a source is measurable (it is `cfRec`). -/
theorem measurable_gb6Rec_src {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) :
    Measurable (gb6Rec c.s c.W c.ζ) :=
  measurable_cfRec c.hcf c.s

/-- **The GB6 instance of one future piece** (data): the explored driver (the joined schedule of the candidate's
program) with its trace and good set, an announced version `(R, V, ρ, ρs)` of the relative exploration against the
counterflow retained at `c.s`, the physical stage start `T`, the stage word map `β`, record event `E` and stage field
`Hr`, and the stage line data (the transport constants `σa`, `kc`, the centring `u₀`, the marks `ℋ` and the physical
union `B` of the stage). -/
structure StageInst (Ω : Type u) where
  W : ℝ≥0 → Ω → ℝ
  γ : Ω → ℝ≥0 → ℂ
  GT : Set Ω
  R : ℝ≥0 → Ω → ℝ
  V : Ω → ℝ≥0∞
  ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  T : ℝ≥0
  β : RecData → BoundaryWord
  E : Set RecData
  Hr : Ω → DistOn upperHalfPlaneOpens
  σa : ℝ
  kc : ℝ
  u₀ : ℂ → ℝ
  ℋ : ℝ≥0 → MeasurableSpace Ω
  B : ℝ≥0 → Ω → Set ℂ

/-- A physical stop with its stopping rule. -/
structure StageStop (Ω : Type u) where
  stop : Ω → ℝ≥0∞
  rule : RecData → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞

section Inst

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The augmented stage record of an instance after history `l`. -/
abbrev StageInst.srec (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : Ω → RecData :=
  stgRec c.s I.W c.W c.ζ I.GT I.R I.V I.T (GW2Rd.stageEncRec c r l)

/-- The stage relative driver of an instance. -/
abbrev StageInst.drv (I : StageInst Ω) (c : SourceData Ω) : ℝ≥0 → Ω → ℝ :=
  stgR c.s I.W c.W c.ζ I.GT I.R I.V I.T

/-- The stage cap of an instance. -/
abbrev StageInst.cap (I : StageInst Ω) (c : SourceData Ω) : Ω → ℝ≥0∞ :=
  stgV c.s I.W c.W c.ζ I.GT I.V I.T

/-- The stage chart of an instance. -/
abbrev StageInst.chart (I : StageInst Ω) (c : SourceData Ω) (ω : Ω) : Chart :=
  stgChart (relChart (gb6Rec c.s c.W c.ζ ω)) (fun t => I.R t ω) (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω)

/-- The stage clock of an instance. -/
abbrev StageInst.clock (I : StageInst Ω) (c : SourceData Ω) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  stgClock c.s I.W c.W c.ζ I.GT I.V I.T t ω

/-- **The stage variable of an instance** with a physical stop. -/
def StageInst.var (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (st : StageStop Ω) : StageVar Ω :=
  augStageVar c.s I.W c.W c.ζ I.GT I.R I.V I.T (GW2Rd.stageEncRec c r l) ((entryList l).length + 1) I.ρ I.ρs I.β
    I.E I.Hr st.stop st.rule

end Inst

/-- **The stage line data of one word type in the local form** (targets for RELDET and STAGEMEAN): the transport of
the field, the marked locality of the physical union `B t` of the stage for the centred original field (with its shape
as GB6's whole-exploration shape at `T + t`), the union mean identification for EVERY local-set mean of `B t`, the
threshold and the integrability. The line kernels are derived (`GW2Rd.hasRelSafe_stage'`). -/
structure StageInst.LinesLocal {Ω : Type u} [mΩ : MeasurableSpace Ω] (I : StageInst Ω) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hWm : ∀ t, Measurable (I.W t)) (w : WordType) :
    Prop where
  transport : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) →
    ∀ hc : (I.chart c ω).IsConformal, Chart.chartTransport hc 1 I.σa I.kc (c.h ω) = I.Hr ω
  harmonic : InnerProductSpace.HarmonicOnNhd I.u₀ H
  zbgff : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField c.h I.u₀) c.P
  sets_le : ∀ t, stgFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) I.T (measurable_stageEncRec c r l) t ≤ I.ℋ t
  sets_le_ambient : ∀ t, I.ℋ t ≤ mΩ
  sets_meas : ∀ t, Measurable[mΩ, hittingSigma] (I.B t)
  sets_open : ∀ t ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω)
  loc : ∀ t, WholeField.IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (WholeField.centredField c.h I.u₀) c.P
  shape : ∀ t : ℝ≥0, ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) →
    min (physClock c.s I.W c.W c.ζ I.GT (I.T + t) ω) (I.V ω) < I.V ω →
    H \ I.B t ω = (relChart (gb6Rec c.s c.W c.ζ ω)).2.1 ''
      (H \ fwdHull (Ito.rpath fun u => I.R u ω) (min (physClock c.s I.W c.W c.ζ I.GT (I.T + t) ω) (I.V ω)).toNNReal)
  mean : ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
    IsLocalSetMean (I.B t) (WholeField.centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
    ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω →
    Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) (I.clock c t ω).toNNReal) →
    ∀ hc : (I.chart c ω).IsConformal, Chart.chartTransport hc 1 I.σa I.kc
        (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens I.u₀) ψ =
      ∫ z, couplingMean c.κ (fun s : ℝ => I.drv c s.toNNReal ω) (I.clock c t ω).toNNReal
        (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
          (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
            (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
          (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
            (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
          (I.clock c t ω).toNNReal) z * ψ z
  int : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun y => canonFld y φ)
    ((c.P.map fun ω => (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))[|typeEvent c.κ w I.β I.E])
  thr : ∀ᵐ y ∂((c.P.map fun ω => (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))[|typeEvent c.κ w I.β I.E]),
    canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL c.κ w (I.β y.1))
      (fun y => typedXR c.κ w (I.β y.1)) y

/-- **The per-stage inputs of an instance** (targets; see the table in the module docstring). -/
structure StageInst.Good {Ω : Type u} [MeasurableSpace Ω] (I : StageInst Ω) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Prop where
  physGood : ∀ ω ∈ I.GT, PhysGood c.s I.W c.W c.ζ I.γ c.α ω
  measurable_W : ∀ t, Measurable (I.W t)
  measurableSet_GT : MeasurableSet I.GT
  GT_ae : ∀ᵐ ω ∂c.P, ω ∈ I.GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s
  version : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V
  measurable_ρ : Measurable I.ρ
  isPathRule_ρ : IsPathRule I.ρ
  V_eq : ∀ᵐ ω ∂c.P, I.V ω = I.ρ (gb6Rec c.s c.W c.ζ ω, fun u => I.R u ω)
  measurable_ρs : ∀ n, Measurable (I.ρs n)
  isPathRule_ρs : ∀ n, IsPathRule (I.ρs n)
  ρs_ne_top : ∀ n y, I.ρs n y ≠ ⊤
  ρs_mono : ∀ y, Monotone fun n => I.ρs n y
  announce : ∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s →
    (∀ n, I.ρs n (gb6Rec c.s c.W c.ζ ω, fun u => I.R u ω) < I.V ω) ∧
      ⨆ n, I.ρs n (gb6Rec c.s c.W c.ζ ω, fun u => I.R u ω) = I.V ω
  prefix_retained : MeasurableSpace.comap (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R) inferInstance ≤
    LocalSets.aeSigma (c.sigma r l) c.P
  measurable_β : Measurable I.β
  measurableSet_E : MeasurableSet I.E
  countable_wordType : (range fun y : RecData => wordType c.κ (I.β y)).Countable
  isSorted : ∀ y ∈ I.E, (I.β y).IsSorted
  E_good : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E →
    gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s ∧ stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω < I.V ω
  measurable_Hr : Measurable I.Hr
  lines : ∀ w : WordType, I.LinesLocal c r l measurable_W w

/-- **The physical stop of a comparison** (target for ROOT2): a protected stopping rule of the stage killed path. -/
structure StageStop.Good {Ω : Type u} [MeasurableSpace Ω] (st : StageStop Ω) (I : StageInst Ω) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Prop where
  rule_meas : ∀ (y : RecData) (t : ℝ≥0), MeasurableSet[pathKilledSigma t] {e | st.rule y e ≤ (t : ℝ≥0∞)}
  measurable_stop : Measurable st.stop
  stop_eq : ∀ᵐ ω ∂c.P, st.stop ω = st.rule (I.srec c r l ω) ((fun t => I.drv c t ω), I.cap c ω)
  stop_le : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → st.stop ω ≤ I.cap c ω
  stop_lt : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → st.stop ω ≠ ⊤ → st.stop ω < I.cap c ω

/-! ### The canonical stage field and the prefix record -/

/-- **The canonical stage field**: the field read in the stage chart (`0` where the chart is not conformal). With
`Hr := stgField σa kc c.h (I.chart c)` the targets `LinesLocal.transport` and `Good.measurable_Hr` are discharged by
`chartTransport_eq_stgField` and `measurable_stgField_inst`. -/
def stgField {Ω : Type*} (σa kc : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (ch : Ω → Chart) (ω : Ω) :
    DistOn upperHalfPlaneOpens :=
  open Classical in if hc : (ch ω).IsConformal then Chart.chartTransport hc 1 σa kc (h ω) else 0

theorem chartTransport_eq_stgField {Ω : Type*} {σa kc : ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {ch : Ω → Chart}
    {ω : Ω} (hc : (ch ω).IsConformal) : Chart.chartTransport hc 1 σa kc (h ω) = stgField σa kc h ch ω := by
  unfold stgField
  split_ifs
  rfl

/-- The canonical stage field of a measurable field along a chart with measurable data is measurable. -/
theorem measurable_stgField {Ω : Type*} [mΩ : MeasurableSpace Ω] {σa kc : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) {ch : Ω → Chart} (hm : WalkInf.IsMeasChart mΩ ch) : Measurable (stgField σa kc h ch) := by
  obtain ⟨hc, hliftc, -, hdom, hfwd, -, hliftm⟩ := hm
  have e : stgField σa kc h ch = fun ω => Chart.chartTransport (hc ω) 1 σa kc (h ω) :=
    funext fun ω => (chartTransport_eq_stgField (hc ω)).symm
  rw [e]
  exact Chart.measurable_chartTransport_random' hc hdom hfwd hliftm hliftc hh 1 σa kc

/-- The prefix record of a GB6 stage is measurable (ambient), from GB6's good set and an R-form version. -/
theorem measurable_stgPreRec_amb {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hgb : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s)
    (hver : IsGB6RelVersionR s P W Wα ζα γ α R V) (T : ℝ≥0) : Measurable (stgPreRec s W Wα ζα GT V T R) :=
  (measurable_stgPreRec hGT hgb hWm (measurableSet_goodSet_physFilt hgb hWm hGTm hGTae) hver T).mono
    ((physFilt hgb hWm P).le T) le_rfl

/-- **The canonical stage field of an instance is measurable** (discharges `Good.measurable_Hr` for
`Hr := stgField σa kc c.h (I.chart c)`). -/
theorem measurable_stgField_inst {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) :
    Measurable (stgField I.σa I.kc c.h (I.chart c)) :=
  measurable_stgField c.hh.1 (isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre)

/-- **`Good.E_good` from the record event**: if the record event lies in the good counterflow records (read by the
exact decoder `augσ`) and the stage is alive on it, `E_good` holds. -/
theorem StageInst.E_good_of {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hEσ : ∀ z ∈ I.E, augσ ((entryList l).length + 1) z ∈ gb6TS c.s)
    (hlive : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω < I.V ω) :
    ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E →
      gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s ∧ stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω < I.V ω := by
  filter_upwards [hlive] with ω h hE
  refine ⟨?_, h hE⟩
  have hd := (augDec_spec (s := c.s) (W := I.W) (Wα := c.W) (ζα := c.ζ) (GT := I.GT) (V := I.V) (T := I.T)
    (stgRecDec_stageEncRec c r l ω) (hv.2.1 ω) (hv.2.2.1 ω)).1
  rw [← hd]
  exact hEσ _ hE

/-- **Part (II) reduced to the explored path**: the prefix record of a GB6 stage is readable at the physical stage
start, so it is `𝒢`-measurable up to null sets as soon as the retained record and the explored driver on `[0, T]` are.
-/
theorem comap_stgPreRec_le_aeSigma {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hgb : Measurable (gb6Rec s Wα ζα))
    (hWm : ∀ r, Measurable (W r)) (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s)
    (hver : IsGB6RelVersionR s P W Wα ζα γ α R V) (T : ℝ≥0)
    (hrec𝒢 : MeasurableSpace.comap (gb6Rec s Wα ζα) inferInstance ≤ LocalSets.aeSigma 𝒢 P)
    (hW𝒢 : ∀ r ≤ T, MeasurableSpace.comap (W r) inferInstance ≤ LocalSets.aeSigma 𝒢 P) :
    MeasurableSpace.comap (stgPreRec s W Wα ζα GT V T R) inferInstance ≤ LocalSets.aeSigma 𝒢 P := by
  have h1 := (measurable_stgPreRec hGT hgb hWm (measurableSet_goodSet_physFilt hgb hWm hGTm hGTae) hver T).comap_le
  refine h1.trans ?_
  rw [physFilt_apply]
  exact sup_le (sup_le hrec𝒢 (iSup₂_le fun r hr => hW𝒢 r hr)) (Supp8.Q3Chain.nullSets_le_aeSigma 𝒢)

/-- **`Good.prefix_retained` from the explored path**: for an instance, part (II) holds as soon as the explored
driver on `[0, T]` is `c.sigma r l`-measurable up to null sets (the counterflow record is exactly
`c.sigma r l`-measurable). -/
theorem StageInst.prefix_retained_of_path {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} (I : StageInst Ω)
    (hGT : ∀ ω ∈ I.GT, PhysGood c.s I.W c.W c.ζ I.γ c.α ω) (hWm : ∀ t, Measurable (I.W t))
    (hGTm : MeasurableSet I.GT) (hGTae : ∀ᵐ ω ∂c.P, ω ∈ I.GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s)
    (hver : IsGB6RelVersionR c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hW : ∀ t ≤ I.T, MeasurableSpace.comap (I.W t) inferInstance ≤ LocalSets.aeSigma (c.sigma r l) c.P) :
    MeasurableSpace.comap (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R) inferInstance ≤
      LocalSets.aeSigma (c.sigma r l) c.P :=
  comap_stgPreRec_le_aeSigma hGT (measurable_gb6Rec_src c) hWm hGTm hGTae hver I.T
    ((GW2Rd.measurable_cfRec_sigma c r l).comap_le.trans (LocalSets.le_aeSigma _ _)) hW

section Good

variable {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)} {I : StageInst Ω}

/-- The prefix record is readable at the physical stage start. -/
theorem StageInst.Good.measurable_pre (hI : I.Good c r l) :
    Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R) :=
  measurable_stgPreRec_amb hI.physGood (measurable_gb6Rec_src c) hI.measurable_W hI.measurableSet_GT hI.GT_ae
    ⟨hI.version, I.ρ, hI.measurable_ρ, hI.isPathRule_ρ, hI.V_eq⟩ I.T

/-- **The stage K2 law of a good instance** (PROVE-GW2-RELDET's `GW2Rd.hasRelSafe_stage'`). -/
theorem StageInst.Good.hasRelSafe (hI : I.Good c r l) (w : WordType) :
    HasRelSafe c.κ w I.β I.E (c.P.map fun ω => (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) := by
  have hL := hI.lines w
  have hver : IsGB6RelVersionR c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V :=
    ⟨hI.version, I.ρ, hI.measurable_ρ, hI.isPathRule_ρ, hI.V_eq⟩
  exact hasRelSafe_stage' hI.measurable_β hI.measurableSet_E c.hh.1 hI.measurable_Hr hI.physGood
    (measurable_gb6Rec_src c) hI.measurable_W hI.measurableSet_GT hI.GT_ae hver I.T (measurable_stageEncRec c r l)
    I.σa I.kc (hL.transport.mono fun ω h hm => h hm _)
    (hI.E_good.mono fun ω h hm => (h hm.1).1) (hI.E_good.mono fun ω h hm => ne_top_of_lt (h hm.1).2)
    hL.harmonic hL.zbgff I.ℋ hL.sets_le hL.sets_le_ambient I.B hL.sets_meas hL.sets_open hL.loc hL.shape
    (fun t g hg ψ => (hL.mean t g hg ψ).mono fun ω h h1 h2 h3 => h h1 h2 h3 _) hL.int hL.thr

/-- **The stage shape of the physical union** (GB6's `ae_compl_union_eq_relChart` at `T + t`): when the union is the
counterflow's retained set together with the explored hull at `T + t`, the shape target holds. -/
theorem shape_of_union {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {P : Measure Ω} (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)
    (hver : IsGB6RelVersionR s P W Wα ζα γ α R V) (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s)
    {F : Set Ω} (hF : ∀ᵐ ω ∂P, ω ∈ F → gb6Rec s Wα ζα ω ∈ gb6TS s) (T : ℝ≥0) {B : ℝ≥0 → Ω → Set ℂ}
    (hB : ∀ t ω, B t ω = Supp8.Q3Rel.invHull (rdrv (gb6Rec s Wα ζα ω)) s ∪
      fwdHull (fun r : ℝ => W r.toNNReal ω) ((T + t : ℝ≥0) : ℝ)) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → min (physClock s W Wα ζα GT (T + t) ω) (V ω) < V ω →
      H \ B t ω = (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => R u ω) (min (physClock s W Wα ζα GT (T + t) ω) (V ω)).toNNReal) := by
  filter_upwards [ae_compl_union_eq_relChart hGT hver (T + t), hGTae, hF] with ω h1 h2 h3 hωF hlt
  rw [hB]
  exact h1 (h2.2 (h3 hωF)) hlt

/-- **The safe stage law of the stage variable of a good instance** with a good physical stop. -/
theorem StageInst.Good.isSafe (hI : I.Good c r l) {st : StageStop Ω} (hst : st.Good I c r l) :
    (I.var c r l st).IsSafe c.κ c.P (I.var c r l st).record := by
  refine isSafe_augStageVar hI.version hI.measurable_ρ hI.isPathRule_ρ hI.V_eq hI.measurable_ρs hI.isPathRule_ρs
    hI.ρs_ne_top hI.ρs_mono hI.announce (measurable_stageEncRec c r l) (stgRecDec_stageEncRec c r l)
    hI.measurable_pre hI.measurable_β hI.measurableSet_E hI.countable_wordType hI.isSorted ?_ hI.measurable_Hr
    hI.hasRelSafe hst.rule_meas hst.measurable_stop hst.stop_eq hst.stop_le hst.stop_lt
  filter_upwards [hI.E_good] with ω h hE
  refine ⟨(h hE).1, ?_⟩
  rw [ENNReal.coe_toNNReal (ne_top_of_lt (h hE).2)]
  exact (h hE).2

/-- **The augmented record of a good instance generates `c.sigma r l`** up to null sets. -/
theorem StageInst.Good.generates (hI : I.Good c r l) (st : StageStop Ω) :
    (I.var c r l st).Generates (𝒢 := c.sigma r l) c.P :=
  generates_augRec rfl (measurable_stageEncRec c r l) hI.measurable_pre (GW2Rd.comap_stageEncRec_sigma c r l)
    hI.prefix_retained

/-- **`LinesLocal.shape` for the physical union** of an instance: the counterflow's retained set together with the
explored hull at `T + t` (GB6's shape at `T + t`, `shape_of_union`). -/
theorem StageInst.shape_of_physUnion (hGT : ∀ ω ∈ I.GT, PhysGood c.s I.W c.W c.ζ I.γ c.α ω)
    (hver : IsGB6RelVersionR c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hGTae : ∀ᵐ ω ∂c.P, ω ∈ I.GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s)
    (hEgood : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s)
    (hB : ∀ t ω, I.B t ω = Supp8.Q3Rel.invHull (rdrv (gb6Rec c.s c.W c.ζ ω)) c.s ∪
      fwdHull (fun s : ℝ => I.W s.toNNReal ω) ((I.T + t : ℝ≥0) : ℝ)) (w : WordType) (t : ℝ≥0) :
    ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) →
      min (physClock c.s I.W c.W c.ζ I.GT (I.T + t) ω) (I.V ω) < I.V ω →
      H \ I.B t ω = (relChart (gb6Rec c.s c.W c.ζ ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => I.R u ω)
          (min (physClock c.s I.W c.W c.ζ I.GT (I.T + t) ω) (I.V ω)).toNNReal) :=
  shape_of_union hGT hver hGTae (hEgood.mono fun _ h hm => h hm.1) I.T hB t

end Good

/-! ### The package of the actual construction -/

/-- **The per-stage package of one source and root**: an instance for every history and candidate, the physical stops
of the near comparisons `(n, m)` reading candidate `a` and of the slow comparisons, and the frame shells. -/
structure Pkg {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  inst : List (EntryIdx c.Θ c.Q) → ℕ → StageInst Ω
  nearStop : List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ → StageStop Ω
  slowStop : List (EntryIdx c.Θ c.Q) → ℕ → StageStop Ω
  nearFamily : List (EntryIdx c.Θ c.Q) → Ω → NearCrossingFamily.{u} c.κ
  nearCandidate : List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ
  slowShell : List (EntryIdx c.Θ c.Q) → ℕ → Ω → SlowShell

/-- The frame of a package. -/
def Pkg.frame {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} (K : Pkg c r) :
    Frame c r where
  nearFamily := K.nearFamily
  nearCandidate := K.nearCandidate
  nearVar l n m a := (K.inst l a).var c r l (K.nearStop l n m a)
  slowShell := K.slowShell
  slowVar l a := (K.inst l a).var c r l (K.slowStop l a)

/-- A package for every source setup and root. -/
abbrev PkgFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q), Pkg c r

/-- The frame family of a package family. -/
def PkgFamily.frame (K : PkgFamily.{u}) : FrameFamily.{u} := fun Ω _ _ c r => (K Ω c r).frame

/-- **The frame words** (target for ROOT2 / the near-comparison work): almost surely on the alive history, the record
is in the stage's record event and the frame's word presents the stage's angle-`0` flow-line word. -/
structure FrameWordStatement (D : ConstructionFamily.{u}) (F : FrameFamily.{u}) : Prop where
  nearWord : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).record ω ∈
        ((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).E ∧
      FCDet.IsFlowType c.κ 0
        (((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).β
          (((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).record ω))
        ((F Ω c r).nearFamily l ω).xL ((F Ω c r).nearFamily l ω).xR (((F Ω c r).nearFamily l ω).ρLs m)
        (((F Ω c r).nearFamily l ω).ρRs m)
  slowWord : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ((F Ω c r).slowVar l a).record ω ∈ ((F Ω c r).slowVar l a).E ∧
      FCDet.IsFlowType c.κ 0 (((F Ω c r).slowVar l a).β (((F Ω c r).slowVar l a).record ω))
        ((F Ω c r).slowShell l a ω).xL ((F Ω c r).slowShell l a ω).xR
        (angleWordL c.κ ((F Ω c r).slowShell l a ω).φ ((F Ω c r).slowShell l a ω).mL
          ((F Ω c r).slowShell l a ω).ρL₀)
        (angleWordR c.κ ((F Ω c r).slowShell l a ω).φ ((F Ω c r).slowShell l a ω).mR
          ((F Ω c r).slowShell l a ω).ρR₀)

/-- **The per-stage targets of a package family** (named input; see the module docstring's table). -/
structure PkgGoodStatement (D : ConstructionFamily.{u}) (K : PkgFamily.{u}) : Prop where
  inst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ((K Ω c r).inst l a).Good c r l
  nearStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((K Ω c r).nearStop l n m a).Good ((K Ω c r).inst l a) c r l
  slowStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((K Ω c r).slowStop l a).Good ((K Ω c r).inst l a) c r l
  words : FrameWordStatement D K.frame

/-- **`FrameSafeStatement` from the per-stage targets.** -/
theorem frameSafeStatement_of_pkgGood {D : ConstructionFamily.{u}} {K : PkgFamily.{u}}
    (hK : PkgGoodStatement D K) : FrameSafeStatement D K.frame where
  nearSafe Ω _ _ c r l n := (hK.nearStop Ω c r l n).mono fun _ hm a =>
    ⟨(hK.inst Ω c r l a).generates _, (hK.inst Ω c r l a).isSafe (hm a)⟩
  nearWord := hK.words.nearWord
  slowSafe Ω _ _ c r k l hl a :=
    ⟨(hK.inst Ω c r l a).generates _, (hK.inst Ω c r l a).isSafe (hK.slowStop Ω c r k l hl a)⟩
  slowWord := hK.words.slowWord

/-- **JOINTDET's `RetainedStoppedSDEStatement` from the per-stage targets** (for any construction `D`, in particular
`RootJ31.constructionFamily`; Theorems 1.2–1.3, R48). -/
theorem retainedStoppedSDEStatement_of_pkgGood (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) {D : ConstructionFamily.{u}}
    {K : PkgFamily.{u}} (hK : PkgGoodStatement D K) :
    GW2JDetR11.RetainedStoppedSDEStatement D (comparisonFamily K.frame) :=
  retainedStoppedSDEStatement_of_frameSafe h12p₀ h13₀ h13 D K.frame (frameSafeStatement_of_pkgGood hK)

end InteractingSLE.Theorem14.GW2Sde
