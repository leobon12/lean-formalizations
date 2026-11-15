/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61AsmSlit
import InteractingSLE.Spec.Sec5.Aux61MarksInit
import InteractingSLE.Spec.Sec5.Aux61NestMarks

/-!
# The assembly data from the physical marked local sets: nested marks, live sets, retained initial mean

Packet PROVE-AUX61-MARKS. `MarksData` is `Aux61Asm.AsmData` without the initial distribution and its window data, with
the **physical** marks `baseMarks i r` and marked sets `baseSets i r` (e.g. UNIONLOC's rule marks at the glued stop and
a set containing `ℍ ∩ (K_s ∪ K̃_T)`, `Aux61MarksRule`). `MarksFacts` lists the physical facts: nested physical marks,
the physical marked sets nested, recorded by their marks, relatively closed, history-marked local, with CHARTLOC's
geometry, and one time-`0` decomposition with its **boundary values on the window** (`initial_boundary`,
`InitialBoundary`); no time-`0` identification is assumed.

`MarksData.toAsmData` builds the assembly data:
* the marks `baseMarks i r ⊔ germ₀` (the germ of the time-`0` live marked set retained, NEST), the live marked sets
  `liveSet S_r (baseSets i r)` (`S_r` the live event at fibre time `r`);
* the history enriched by the time-`0` decomposition `h₀` of `initial_boundary`: `meanHistory Z h₀ = (Z, h₀)`, event
  `B × 𝒟'`;
* the initial distribution `initialDist` (`Aux61MarksInit`) with its window data from `initial_boundary`.

`asmBaseFacts_toAsmData` proves every field of `Aux61Asm.AsmBaseFacts` for it: in particular `marks_mono`, `sets_mono`,
`locality` (NEST's `isHistoryAvoidanceLocal_liveSet_sup_germ`) and **`initial_identification`** (uniqueness at time `0`
for the retained record, `Aux61MarksInit.initial_identification_initialDist`). `localCover_of_marks` then gives the
fibre cover from SLIT's wiring (W) for the built data.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMapInv)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61Fib (FibCode FibData PathGood)
open Aux61FibK (codeFiltration)
open Aux61FibData (IsRestartSpec IsMeasChart inPath clr withQ)
open Aux61GInst (HasAccessLanding accessExitCode)
open Aux61GCont (InitialWindowData)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet liveSet_of_mem liveSet_of_notMem measurableSet_live)
open Aux61UnionK (HasFibreLocalCover chartHull)
open Aux61Asm (AsmData AsmBaseFacts GluedSlitFacts asmSigma)
open Aux61GHist (meanHistory)
open LocalSets (germSigma)
open WholeField (IsHistoryAvoidanceLocal centredField)

universe u

/-- **The physical assembly data**: `Aux61Asm.AsmData` without the initial distribution and its window data, with the
physical marks `baseMarks` and marked sets `baseSets` (before the time-`0` germ is retained and the sets are made
live). -/
structure MarksData {X : Type u} [MeasurableSpace X] (μ : Measure X) where
  ι : Type
  [countable : Countable ι]
  β : ι → Type u
  [mβ : ∀ i, MeasurableSpace (β i)]
  Z : ∀ i, X → β i
  B : ∀ i, Set (β i)
  data : ι → FibData
  event : ι → Set X
  chart : ι → X → Chart
  path : ι → X → ℝ≥0 → ℂ
  life : ι → X → ℝ≥0∞
  window : ι → Set ℂ
  field : X → DistOn upperHalfPlaneOpens
  scale : ℝ
  constant : ℝ
  left : ι → ℝ
  right : ι → ℝ
  originalMean : ℂ → ℝ
  baseMarks : ι → ℝ≥0 → MeasurableSpace X
  baseSets : ι → ℝ≥0 → X → Set ℂ
  physicalDriver : ι → ℝ≥0 → X → ℝ → ℝ
  physicalPath : ι → ℝ≥0 → X → ℝ → ℂ
  start : ι → ℝ≥0 → X → ℝ
  duration : ι → ℝ≥0 → X → ℝ
  domain : ι → ℝ≥0 → X → Set ℂ
  chartPath : ι → ℝ≥0 → X → ℝ → ℂ
  chartLife : ι → ℝ≥0 → X → ℝ
  index : Type
  [countableIndex : Countable index]
  time : index → ι → ℝ≥0 → X → ℝ
  patches : index → ι → ℝ≥0 → X → Set ℂ
  mean : index → ι → ℝ≥0 → X → ℂ → ℝ
  physicalMean : index → ι → ℝ≥0 → X → ℂ → ℝ
  comparisonEvent : index → ι → ℝ≥0 → Set X

attribute [instance] MarksData.countable MarksData.mβ MarksData.countableIndex

variable {X : Type u} [mX : MeasurableSpace X] {μ : Measure X}

namespace MarksData

variable (D : MarksData μ)

/-- The selected-access restart code. -/
abbrev code (i : D.ι) : X → FibCode :=
  accessExitCode (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i) D.scale D.constant D.field

/-- The centred field. -/
abbrev cfield : X → DistOn upperHalfPlaneOpens := centredField D.field D.originalMean

/-- The live marked sets: the physical set on the live event at fibre time `r`, `ℍ` off it. -/
abbrev liveSets (i : D.ι) (r : ℝ≥0) : X → Set ℂ :=
  liveSet (liveEv (D.Z i) (D.B i) (D.code i) r) (D.baseSets i r)

/-- The germ σ-algebra of the time-`0` live marked set. -/
abbrev germ0 (i : D.ι) : MeasurableSpace X := germSigma (D.liveSets i 0) D.cfield

/-- The marks of the assembly: the physical marks with the time-`0` germ retained. -/
abbrev marks (i : D.ι) (r : ℝ≥0) : MeasurableSpace X := D.baseMarks i r ⊔ D.germ0 i

/-- The conditioning algebra of the assembly at fibre time `q` (for the physical history). -/
abbrev sigma (i : D.ι) (q : ℝ≥0) : MeasurableSpace X :=
  asmSigma (D.Z i) (D.B i) (D.code i) (D.liveSets i) (D.marks i) D.cfield q

/-- **The boundary values of a retained time-`0` mean on the window**: almost surely under the law of the retained
record `(Z, g)`, on the history event every harmonic representative of a harmonic retained mean tends to the reference
mean at every window point. -/
def InitialBoundary (i : D.ι) (g : X → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ᵐ b ∂μ.map (meanHistory (D.Z i) g), b.1 ∈ D.B i → IsHarmonicDistOn b.2 H → ∀ v : ℂ → ℝ,
    InnerProductSpace.HarmonicOnNhd v H → (∀ ψ : TestOn upperHalfPlaneOpens, b.2 ψ = ∫ z, v z * ψ z) →
    ∀ a ∈ (D.data i).O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 (D.data i) z) (𝓝[H] (a : ℂ)) (𝓝 0)

/-- `InitialBoundary` from a measurable set of good retained records carrying the retained record almost surely. -/
theorem initialBoundary_of_measurableSet (i : D.ι) {g : X → DistOn upperHalfPlaneOpens}
    (hZ : Measurable (D.Z i)) (hg : Measurable g) {M : Set (D.β i × DistOn upperHalfPlaneOpens)}
    (hM : MeasurableSet M) (hgood : ∀ b ∈ M, b.1 ∈ D.B i → IsHarmonicDistOn b.2 H → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v H → (∀ ψ : TestOn upperHalfPlaneOpens, b.2 ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ (D.data i).O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 (D.data i) z) (𝓝[H] (a : ℂ)) (𝓝 0))
    (hae : ∀ᵐ x ∂μ, meanHistory (D.Z i) g x ∈ M) : D.InitialBoundary i g := by
  have hm : AEMeasurable (meanHistory (D.Z i) g) μ := (Aux61GHist.measurable_meanHistory hZ hg).aemeasurable
  filter_upwards [(ae_map_iff hm hM).2 hae] with b hb
  exact hgood b hb

end MarksData

/-- **The physical facts of the data.** Restart and window facts (GLUEINST's cover binders), the physical marked local
sets (nested physical marks containing the history, the raw code and the chart; nested physical sets recorded by
their marks, relatively closed, history-marked local, with CHARTLOC's geometry), the boundary values of the time-`0`
conditional mean on the window, and the positive-time glued slit facts and comparison cover (CONFIG). -/
structure MarksFacts (μ : Measure X) (D : MarksData μ) : Prop where
  measurable_Z : ∀ i, Measurable (D.Z i)
  measurable_B : ∀ i, MeasurableSet (D.B i)
  spec : ∀ i, IsRestartSpec (D.event i) (D.chart i) (D.path i) (D.life i)
  open_window : ∀ i, IsOpen (D.window i)
  zero_window : ∀ i, (0 : ℂ) ∈ D.window i
  landing : ∀ i, HasAccessLanding (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i)
  injective_path : ∀ i, ∀ x ∈ D.event i, InjOn (D.path i x) {u | (u : ℝ≥0∞) < D.life i x}
  continuous_lift : ∀ i, ∀ x ∈ D.event i, ContinuousOn (D.chart i x).2.2 (D.chart i x).dom
  harmonic_lift : ∀ i, ∀ x ∈ D.event i,
    InnerProductSpace.HarmonicOnNhd (D.chart i x).2.2 (D.chart i x).dom
  measurable_field : Measurable D.field
  data_window : ∀ i, (D.data i).V = D.window i
  data_clearance : ∀ i, (D.data i).ℓ = clr (D.window i)
  reference : ∀ i, Aux61Cov.RefWin (D.data i).κ (D.data i).bR (D.data i).JR (Ioo (D.left i) (D.right i))
  physical_stop : ∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i →
    x ∈ D.event i ∧ 0 < D.life i x ∧ (D.life i x < ⊤ ∨ ∃ u : ℝ≥0,
      (u : ℝ≥0∞) < D.life i x ∧ inPath (D.event i) (D.chart i) (D.path i) (D.life i) x u ∉ D.window i)
  harmonic_originalMean : InnerProductSpace.HarmonicOnNhd D.originalMean H
  zero_field : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField D.field D.originalMean) μ
  baseMarks_le : ∀ i r, D.baseMarks i r ≤ mX
  baseMarks_mono : ∀ i r, D.baseMarks i 0 ≤ D.baseMarks i r
  Z_le : ∀ i, (D.mβ i).comap (D.Z i) ≤ D.baseMarks i 0
  code_le : ∀ i (r : ℝ≥0), (codeFiltration.{u} r).comap (fun x => ULift.up.{u} (D.code i x)) ≤ D.baseMarks i r
  event_measurable : ∀ i, MeasurableSet[D.baseMarks i 0] (D.event i)
  chart_measurable : ∀ i, @IsMeasChart X (D.baseMarks i 0) (D.chart i)
  baseSets_marks : ∀ i r, Measurable[D.baseMarks i r, hittingSigma] (D.baseSets i r)
  baseSets_closed : ∀ i r x, D.baseSets i r x ⊆ H ∧ IsOpen (H \ D.baseSets i r x)
  baseSets_mono : ∀ i r x, D.baseSets i 0 x ⊆ D.baseSets i r x
  locality : ∀ i r, IsHistoryAvoidanceLocal (D.baseMarks i r) (D.baseSets i r) (centredField D.field D.originalMean) μ
  geometry : ∀ i (r : ℝ≥0), ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (r : ℝ≥0∞) < (D.code i x).life →
    H \ D.baseSets i r x = (D.chart i x).2.1 '' (H \ chartHull (D.code i) r x)
  initial_boundary : ∀ i, ∃ g : X → DistOn upperHalfPlaneOpens,
    IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) g ∧ D.InitialBoundary i g
  glued : ∀ i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (t : ℝ≥0∞) < (D.code i x).life →
    GluedSlitFacts (D.data i).κ (D.code i x) t (D.physicalDriver i t x) (D.physicalPath i t x) (D.start i t x)
      (D.duration i t x) (D.chart i x) (D.domain i t x) (D.chartPath i t x) (D.chartLife i t x)
      (fun j => D.time j i t x) (fun j => D.patches j i t x) (D.baseSets i t x) (fun j => D.mean j i t x)
      (fun j => D.physicalMean j i t x)
  comparison_cover : ∀ i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (t : ℝ≥0∞) < (D.code i x).life →
    ∀ j, D.time j i t x < D.start i t x + D.duration i t x → x ∈ D.comparisonEvent j i t

/-- **The cover facts of the data** for the event `E` (GLUEINST's history cover and completed window). -/
structure MarksCover (μ : Measure X) (E : X → Prop) (D : MarksData μ) : Prop where
  history_cover : ∀ᵐ x ∂μ, E x → ∃ i, D.Z i x ∈ D.B i
  completed_window : ∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → E x →
    D.life i x < ⊤ ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < D.life i x →
      inPath (D.event i) (D.chart i) (D.path i) (D.life i) x u ∈ D.window i) ∧
    ∃ y ∈ Ioo (D.left i) (D.right i), Tendsto (inPath (D.event i) (D.chart i) (D.path i) (D.life i) x)
      (𝓝[<] (D.life i x).toNNReal) (𝓝 (y : ℂ))

/-! ### The live sets and the retained marks -/

section Props

variable {D : MarksData μ} (hF : MarksFacts μ D)
include hF

theorem MarksFacts.measurable_code (i : D.ι) : Measurable (D.code i) :=
  Aux61GInst.measurable_accessExitCode (hF.spec i) (hF.open_window i) (hF.zero_window i) (hF.landing i)
    (hF.injective_path i) (hF.continuous_lift i) hF.measurable_field

/-- The live event at fibre time `q` is recorded by the physical marks at every later-or-equal fibre time. -/
theorem MarksFacts.measurableSet_liveEv (i : D.ι) {q r : ℝ≥0} (hqr : D.baseMarks i q ≤ D.baseMarks i r) :
    MeasurableSet[D.baseMarks i r] (liveEv (D.Z i) (D.B i) (D.code i) q) :=
  measurableSet_live (((hF.Z_le i).trans (hF.baseMarks_mono i q)).trans hqr) ((hF.code_le i q).trans hqr)
    (hF.measurable_B i)

/-- The live marked sets are recorded by the physical marks. -/
theorem MarksFacts.measurable_liveSets_base (i : D.ι) (r : ℝ≥0) :
    Measurable[D.baseMarks i r, hittingSigma] (D.liveSets i r) :=
  Aux61Nest.measurable_liveSet (hF.measurableSet_liveEv i le_rfl) (hF.baseSets_marks i r)

/-- The live marked sets are recorded by the assembly marks (SLIT's wiring field `sets_marks`). -/
theorem MarksFacts.measurable_liveSets_marks (i : D.ι) (r : ℝ≥0) :
    Measurable[D.marks i r, hittingSigma] (D.liveSets i r) :=
  (hF.measurable_liveSets_base i r).mono le_sup_left le_rfl

theorem MarksFacts.measurable_liveSets (i : D.ι) (r : ℝ≥0) : Measurable[mX, hittingSigma] (D.liveSets i r) :=
  (hF.measurable_liveSets_base i r).mono (hF.baseMarks_le i r) le_rfl

/-- **The assembly marks are sub-σ-algebras of the ambient one.** -/
theorem MarksFacts.marks_le (i : D.ι) (r : ℝ≥0) : D.marks i r ≤ mX :=
  sup_le (hF.baseMarks_le i r)
    (LocalSets.germSigma_le (hF.measurable_liveSets i 0) (WholeField.measurable_centredField hF.measurable_field _))

/-- **The assembly marks are nested.** -/
theorem MarksFacts.marks_mono (i : D.ι) (r : ℝ≥0) : D.marks i 0 ≤ D.marks i r :=
  sup_le_sup_right (hF.baseMarks_mono i r) _

omit hF in
/-- The live sets are relatively closed. -/
theorem MarksFacts.liveSets_closed (hF : MarksFacts μ D) (i : D.ι) (r : ℝ≥0) (x : X) :
    D.liveSets i r x ⊆ H ∧ IsOpen (H \ D.liveSets i r x) :=
  Aux61Nest.liveSet_properties (hF.baseSets_closed i r) x

omit hF in
/-- **The live sets are nested.** -/
theorem MarksFacts.liveSets_mono (hF : MarksFacts μ D) (i : D.ι) (r : ℝ≥0) (x : X) :
    D.liveSets i 0 x ⊆ D.liveSets i r x :=
  Aux61Nest.liveSet_subset Aux61OldB.liveEv_subset_zero (fun x => (hF.baseSets_closed i 0 x).1)
    (hF.baseSets_mono i r) x

/-- **History-marked locality of the live sets for the assembly marks** (the time-`0` germ retained; NEST). -/
theorem MarksFacts.locality_marks [IsProbabilityMeasure μ] (i : D.ι) (r : ℝ≥0) :
    IsHistoryAvoidanceLocal (D.marks i r) (D.liveSets i r) D.cfield μ :=
  Aux61Nest.isHistoryAvoidanceLocal_liveSet_sup_germ hF.zero_field (hF.baseMarks_le i r)
    (hF.measurableSet_liveEv i le_rfl) (hF.measurableSet_liveEv i (hF.baseMarks_mono i r))
    Aux61OldB.liveEv_subset_zero ((hF.baseSets_marks i 0).mono (hF.baseMarks_mono i r) le_rfl)
    (fun x => (hF.baseSets_closed i 0 x).1) ((hF.baseSets_marks i r).mono (hF.baseMarks_le i r) le_rfl)
    (hF.baseSets_mono i r) (hF.locality i r)

/-- CHARTLOC's geometry for the live sets. -/
theorem MarksFacts.geometry_live (i : D.ι) (r : ℝ≥0) :
    ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (r : ℝ≥0∞) < (D.code i x).life →
      H \ D.liveSets i r x = (D.chart i x).2.1 '' (H \ chartHull (D.code i) r x) := by
  filter_upwards [hF.geometry i r] with x hx hxB hxr
  have e : D.liveSets i r x = D.baseSets i r x :=
    liveSet_of_mem (show x ∈ liveEv (D.Z i) (D.B i) (D.code i) r from ⟨hxB, hxr⟩)
  rw [e]
  exact hx hxB hxr

/-- The chart is measurable for the assembly marks at time `0`. -/
theorem MarksFacts.chart_measurable_marks (i : D.ι) : @IsMeasChart X (D.marks i 0) (D.chart i) := by
  have hcm := hF.chart_measurable i
  have h0 : D.baseMarks i 0 ≤ D.marks i 0 := le_sup_left
  exact @IsMeasChart.mk X (D.marks i 0) (D.chart i)
    (fun z => h0 _ (@IsMeasChart.dom X (D.baseMarks i 0) _ hcm z))
    (fun z => (@IsMeasChart.fwd X (D.baseMarks i 0) _ hcm z).mono h0 le_rfl)
    (fun z => (@IsMeasChart.lift X (D.baseMarks i 0) _ hcm z).mono h0 le_rfl)

omit hF in
/-- The conditioning algebra at time `0` is contained in the assembly marks at time `0` (the time-`0` germ is
retained among the marks). -/
theorem MarksData.sigma_zero_le_marks (i : D.ι) : D.sigma i 0 ≤ D.marks i 0 := by
  have e : liveSet (liveEv (D.Z i) (D.B i) (D.code i) 0) (D.liveSets i 0) = D.liveSets i 0 :=
    Aux61Nest.liveSet_idem _ _
  have hg : germSigma (liveSet (liveEv (D.Z i) (D.B i) (D.code i) 0) (D.liveSets i 0)) D.cfield ≤ D.marks i 0 := by
    rw [e]
    exact le_sup_right
  exact sup_le hg (sup_le le_rfl hg)

/-- **A time-`0` decomposition exists** for the physical history, given the assembly marks and live sets (NEST's pair
theorem through ASSEMBLE's `exists_isChartGaussAt_asmSigma`). -/
theorem MarksFacts.exists_initialGauss [IsProbabilityMeasure μ] (i : D.ι) :
    ∃ g : X → DistOn upperHalfPlaneOpens, IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) g :=
  Aux61Asm.exists_isChartGaussAt_asmSigma (hF.measurable_B i) (hF.spec i) (hF.open_window i) (hF.zero_window i)
    (hF.landing i) (hF.injective_path i) (hF.continuous_lift i) (hF.harmonic_lift i) hF.measurable_field
    hF.harmonic_originalMean hF.zero_field (hF.marks_le i) (hF.marks_mono i)
    ((hF.Z_le i).trans le_sup_left) (fun r => (hF.code_le i r).trans le_sup_left)
    (le_sup_left (a := D.baseMarks i 0) _ (hF.event_measurable i)) (hF.chart_measurable_marks i)
    (hF.measurable_liveSets_marks i 0) (hF.measurable_liveSets i) (hF.liveSets_closed i) (hF.liveSets_mono i)
    (hF.locality_marks i) (hF.geometry_live i) 0

end Props

/-! ### The built assembly data -/

section Build

variable {D : MarksData μ}

/-- The time-`0` decomposition of `initial_boundary` (retained in the history). -/
def MarksFacts.initialMean (hF : MarksFacts μ D) (i : D.ι) : X → DistOn upperHalfPlaneOpens :=
  Classical.choose (hF.initial_boundary i)

theorem MarksFacts.initialMean_spec (hF : MarksFacts μ D) (i : D.ι) :
    IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) (hF.initialMean i) :=
  (Classical.choose_spec (hF.initial_boundary i)).1

theorem MarksFacts.initialMean_boundary (hF : MarksFacts μ D) (i : D.ι) : D.InitialBoundary i (hF.initialMean i) :=
  (Classical.choose_spec (hF.initial_boundary i)).2

/-- The window data of the explicit initial distribution of the retained record. -/
def MarksFacts.initialData (hF : MarksFacts μ D) (i : D.ι) :
    InitialWindowData (D.β i × DistOn upperHalfPlaneOpens) (μ.map (meanHistory (D.Z i) (hF.initialMean i)))
      (D.data i) (initialDist (D.data i) (D.B i)) :=
  Classical.choice (nonempty_initialWindowData_initialDist (D.data i) (hF.measurable_B i)
    (hF.initialMean_boundary i))

/-- **The built assembly data**: the history retains the time-`0` decomposition, the initial distribution is
`initialDist` with its window data, the marks retain the time-`0` germ, the marked sets are live. -/
abbrev MarksData.toAsmData (D : MarksData μ) (hF : MarksFacts μ D) : AsmData μ where
  ι := D.ι
  β i := D.β i × DistOn upperHalfPlaneOpens
  Z i := meanHistory (D.Z i) (hF.initialMean i)
  B i := D.B i ×ˢ univ
  data := D.data
  initialMean i := initialDist (D.data i) (D.B i)
  initial i := hF.initialData i
  event := D.event
  chart := D.chart
  path := D.path
  life := D.life
  window := D.window
  field := D.field
  scale := D.scale
  constant := D.constant
  left := D.left
  right := D.right
  originalMean := D.originalMean
  marks := D.marks
  sets := D.liveSets
  physicalDriver := D.physicalDriver
  physicalPath := D.physicalPath
  start := D.start
  duration := D.duration
  domain := D.domain
  chartPath := D.chartPath
  chartLife := D.chartLife
  index := D.index
  time := D.time
  patches := D.patches
  mean := D.mean
  physicalMean := D.physicalMean
  comparisonEvent := D.comparisonEvent

end Build

end InteractingSLE.Sec5.Aux61Marks
