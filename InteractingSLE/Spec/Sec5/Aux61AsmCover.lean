/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61AsmCore
import InteractingSLE.Spec.Sec5.Aux61GContCover
import InteractingSLE.Spec.Sec5.Aux61GStepSlitData

/-!
# Assembly of the fibre cover from the physical marked local sets

Packet PROVE-AUX61-ASSEMBLE. Every object is explicit data (`AsmData`); every remaining assertion is a
named field of `AsmFacts`. The assembly `localCover_of_asm` proves `HasFibreLocalCover` by:

* the Gaussian decompositions at every fibre time, from the physical marked local sets with nested marks
  (NEST's pair theorem, `exists_isChartGaussAt_asmSigma`), with nested conditioning algebras
  (`asmSigma_zero_le`);
* at fibre time `0`, the decomposition is replaced by the history-measurable initial mean (the a.e.
  identification `initial_identification` and `isChartGaussAt_congr_ae`);
* the glued slit samples, from the per-sample physical facts and the constructed initial data
  (GLUEINST's `gluedSlitSample_of_initialData`, the code's path facts `pathGood_accessExitCode`);
* (K-b) at every fibre time: at `0` from the initial data (GLUEINST's `isChartMeanAt_zero_of_initialData`), at
  positive times from the nested decompositions and the glued slit data (GLUEINST's `isChartMeanAt_of_initialData`,
  i.e. OLDB's growth/old-boundary theorems and CONFIG's slit sides); all glued objects may depend on the fibre time;
* the cover itself (GLUEINST's `hasFibreLocalCover_of_captured_access`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMapInv)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Asm

open Aux61Fib (FibCode FibData PathGood)
open Aux61FibK (codeFiltration)
open Aux61FibData (IsRestartSpec IsMeasChart inPath clr withQ)
open Aux61GInst (HasAccessLanding accessExitCode)
open Aux61GCont (InitialWindowData)
open Aux61ChLoc (IsChartGaussAt)
open Aux61UnionK (HasFibreLocalCover chartHull)
open Aux61Conf2 (IsGluedSlit IsGluedSlitSample)
open WholeField (IsHistoryAvoidanceLocal centredField)

universe u

/-- **The physical glued slit facts of one sample** (the part of CONFIG's `IsGluedSlitSample` that does not
mention the constructed initial data): the glued slit geometry, the comparison cover of the slit, the smaller
means' coupling formulas and their basic heights on the two sides. -/
structure GluedSlitFacts (κ : ℝ) (s : FibCode) (q : ℝ≥0) (Wph : ℝ → ℝ) (η : ℝ → ℂ) (r τ : ℝ) (c : Chart)
    (Ω : Set ℂ) (γ : ℝ → ℂ) (Tc : ℝ) {J : Type*} (ρ : J → ℝ) (L : J → Set ℂ) (A : Set ℂ)
    (M₂ uph : J → ℂ → ℝ) : Prop where
  glued : IsGluedSlit Wph η r τ c Ω (fun t : ℝ => s.driver t.toNNReal) γ Tc q
  cover : ∀ u ∈ Ioo 0 τ, ∃ j, r + u < ρ j ∧ ρ j < r + τ ∧ η (r + u) ∈ L j ∧
    ∃ ε > 0, A ∩ ball (η (r + u)) ε ⊆ L j
  mean : ∀ j, ∀ z ∈ Ω, M₂ j z = couplingMean κ Wph (ρ j) (uph j) z
  physL : ∀ j, ∀ p : ℝ, p < 0 → extendFrom H (fwdMapInv Wph (ρ j)) p ∈ H →
    Tendsto (uph j) (𝓝[H] (p : ℂ)) (𝓝 (-(Real.pi / Real.sqrt κ)))
  physR : ∀ j, ∀ p : ℝ, 0 < p → extendFrom H (fwdMapInv Wph (ρ j)) p ∈ H →
    Tendsto (uph j) (𝓝[H] (p : ℂ)) (𝓝 (Real.pi / Real.sqrt κ))

/-- The physical facts and the constructed initial data give CONFIG's glued sample. -/
theorem GluedSlitFacts.isGluedSlitSample {β : Type*} [MeasurableSpace β] {ν : Measure β} {d : FibData}
    {T₀ : β → DistOn upperHalfPlaneOpens} (D : InitialWindowData β ν d T₀) (b : β) {s : FibCode} {q : ℝ≥0}
    (hgood : PathGood d s) (hq : (q : ℝ≥0∞) < s.life) {Wph : ℝ → ℝ} {η γ : ℝ → ℂ} {r τ Tc : ℝ} {c : Chart}
    {Ω : Set ℂ} {J : Type*} {ρ : J → ℝ} {L : J → Set ℂ} {A : Set ℂ} {M₂ uph : J → ℂ → ℝ}
    (hf : GluedSlitFacts d.κ s q Wph η r τ c Ω γ Tc ρ L A M₂ uph) :
    IsGluedSlitSample d.κ (withQ d (D.correction b)) (D.cutoff b) D.neighbourhood s q
      Wph η r τ c Ω γ Tc ρ L A M₂ uph :=
  Aux61GStep.gluedSlitSample_of_initialData D b hgood hq hf.glued hf.cover hf.mean hf.physL hf.physR

/-- **The explicit objects of the assembled fibre cover** on a probability space `(X, μ)`: the countable
histories, the selected-access restart (event, chart, physical path, contact time, window), the field and its
chart constants, the reference word and window, the initial mean as a function of the history with its
constructed window data, the physical marked local sets with their marks, and the glued slit objects. -/
structure AsmData {X : Type u} [MeasurableSpace X] (μ : Measure X) where
  ι : Type
  [countable : Countable ι]
  β : ι → Type u
  [mβ : ∀ i, MeasurableSpace (β i)]
  Z : ∀ i, X → β i
  B : ∀ i, Set (β i)
  data : ι → FibData
  initialMean : ∀ i, β i → DistOn upperHalfPlaneOpens
  initial : ∀ i, InitialWindowData (β i) (μ.map (Z i)) (data i) (initialMean i)
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
  marks : ι → ℝ≥0 → MeasurableSpace X
  sets : ι → ℝ≥0 → X → Set ℂ
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

attribute [instance] AsmData.countable AsmData.mβ AsmData.countableIndex

variable {X : Type u} [mX : MeasurableSpace X] {μ : Measure X}

/-- The selected-access restart code of the data. -/
abbrev AsmData.code (D : AsmData μ) (i : D.ι) : X → FibCode :=
  accessExitCode (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i) D.scale D.constant D.field

/-- The conditioning algebra of the data at fibre time `q`. -/
abbrev AsmData.sigma (D : AsmData μ) (i : D.ι) (q : ℝ≥0) : MeasurableSpace X :=
  asmSigma (D.Z i) (D.B i) (D.code i) (D.sets i) (D.marks i) (centredField D.field D.originalMean) q

/-- **The remaining assertions about the data, except the comparison limits.** Restart and window facts
(GLUEINST's cover binders), the physical marked local sets (CHARTLOC/UNIONLOC/NEST), the identification of the
time-`0` conditional mean with the history-measurable initial mean, and the positive-time glued slit facts and
comparison cover (CONFIG). -/
structure AsmBaseFacts (μ : Measure X) (E : X → Prop) (D : AsmData μ) : Prop where
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
  history_cover : ∀ᵐ x ∂μ, E x → ∃ i, D.Z i x ∈ D.B i
  completed_window : ∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → E x →
    D.life i x < ⊤ ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < D.life i x →
      inPath (D.event i) (D.chart i) (D.path i) (D.life i) x u ∈ D.window i) ∧
    ∃ y ∈ Ioo (D.left i) (D.right i), Tendsto (inPath (D.event i) (D.chart i) (D.path i) (D.life i) x)
      (𝓝[<] (D.life i x).toNNReal) (𝓝 (y : ℂ))
  measurable_initialMean : ∀ i, Measurable (D.initialMean i)
  harmonic_originalMean : InnerProductSpace.HarmonicOnNhd D.originalMean H
  zero_field : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField D.field D.originalMean) μ
  marks_le : ∀ i r, D.marks i r ≤ mX
  marks_mono : ∀ i r, D.marks i 0 ≤ D.marks i r
  Z_le : ∀ i, (D.mβ i).comap (D.Z i) ≤ D.marks i 0
  code_le : ∀ i (r : ℝ≥0), (codeFiltration.{u} r).comap (fun x => ULift.up.{u} (D.code i x)) ≤ D.marks i r
  event_measurable : ∀ i, MeasurableSet[D.marks i 0] (D.event i)
  chart_measurable : ∀ i, @IsMeasChart X (D.marks i 0) (D.chart i)
  sets_zero_measurable : ∀ i, Measurable[D.marks i 0, hittingSigma] (D.sets i 0)
  sets_measurable : ∀ i r, Measurable[mX, hittingSigma] (D.sets i r)
  sets_closed : ∀ i r x, D.sets i r x ⊆ H ∧ IsOpen (H \ D.sets i r x)
  sets_mono : ∀ i r x, D.sets i 0 x ⊆ D.sets i r x
  locality : ∀ i r, IsHistoryAvoidanceLocal (D.marks i r) (D.sets i r) (centredField D.field D.originalMean) μ
  geometry : ∀ i (r : ℝ≥0), ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (r : ℝ≥0∞) < (D.code i x).life →
    H \ D.sets i r x = (D.chart i x).2.1 '' (H \ chartHull (D.code i) r x)
  initial_identification : ∀ i (g : X → DistOn upperHalfPlaneOpens),
    IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) g →
    ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → ((0 : ℝ≥0) : ℝ≥0∞) < (D.code i x).life → g x = D.initialMean i (D.Z i x)
  glued : ∀ i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (t : ℝ≥0∞) < (D.code i x).life →
    GluedSlitFacts (D.data i).κ (D.code i x) t (D.physicalDriver i t x) (D.physicalPath i t x) (D.start i t x)
      (D.duration i t x) (D.chart i x) (D.domain i t x) (D.chartPath i t x) (D.chartLife i t x)
      (fun j => D.time j i t x) (fun j => D.patches j i t x) (D.sets i t x) (fun j => D.mean j i t x)
      (fun j => D.physicalMean j i t x)
  comparison_cover : ∀ i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (t : ℝ≥0∞) < (D.code i x).life →
    ∀ j, D.time j i t x < D.start i t x + D.duration i t x → x ∈ D.comparisonEvent j i t

/-- **The remaining assertions about the data**: the base facts and SLIT's comparison limits at the positive fibre
times, for every valid Gaussian decomposition. -/
structure AsmFacts (μ : Measure X) (E : X → Prop) (D : AsmData μ) : Prop extends AsmBaseFacts μ E D where
  comparison_limits : ∀ i (t : ℝ≥0) (g : X → DistOn upperHalfPlaneOpens),
    IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) t (D.sigma i t) g → 0 < t →
    ∀ᵐ x ∂μ, ∀ j, D.Z i x ∈ D.B i → (t : ℝ≥0∞) < (D.code i x).life → x ∈ D.comparisonEvent j i t →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ chartHull (D.code i) t x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull (D.code i) t x →
        g x ψ = ∫ z, v z * ψ z) →
      ∀ z₀ ∈ D.patches j i t x ∪ {z : ℂ | z.im = 0}, (∃ ε > 0, D.sets i t x ∩ ball z₀ ε ⊆ D.patches j i t x) →
      ∀ l : Filter ℂ, l ≤ 𝓟 (H \ chartHull (D.code i) t x) → Tendsto (D.chart i x).2.1 l (𝓝 z₀) →
        Tendsto (fun ζ => v ζ - (D.mean j i t x ((D.chart i x).2.1 ζ) + 0 +
          QuantumZipper.chiC (D.data i).κ * (D.chart i x).2.2 ((D.chart i x).2.1 ζ))) l (𝓝 0)

/-- **The assembled fibre cover.** From the explicit data and the named facts, the fibre-local cover holds. The
Gaussian decompositions at every fibre time are constructed from the physical marked local sets; (K-b) at every
fibre time (the canonical mean) and the cover are proved. -/
theorem localCover_of_asm [IsProbabilityMeasure μ] {E : X → Prop} (D : AsmData μ) (hF : AsmFacts μ E D) :
    HasFibreLocalCover μ E := by
  classical
  have hY : ∀ i, Measurable (D.code i) := fun i =>
    Aux61GInst.measurable_accessExitCode (hF.spec i) (hF.open_window i) (hF.zero_window i) (hF.landing i)
      (hF.injective_path i) (hF.continuous_lift i) hF.measurable_field
  have hex : ∀ i (r : ℝ≥0), ∃ g, IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) r (D.sigma i r) g :=
    fun i r => exists_isChartGaussAt_asmSigma (hF.measurable_B i) (hF.spec i) (hF.open_window i)
      (hF.zero_window i) (hF.landing i) (hF.injective_path i) (hF.continuous_lift i) (hF.harmonic_lift i)
      hF.measurable_field hF.harmonic_originalMean hF.zero_field (hF.marks_le i) (hF.marks_mono i)
      (hF.Z_le i) (hF.code_le i) (hF.event_measurable i) (hF.chart_measurable i) (hF.sets_zero_measurable i)
      (hF.sets_measurable i) (hF.sets_closed i) (hF.sets_mono i) (hF.locality i) (hF.geometry i) r
  choose g hg using hex
  have hG0 : ∀ i, IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0)
      (fun x => D.initialMean i (D.Z i x)) := by
    intro i
    have hZm : Measurable[D.sigma i 0] (D.Z i) :=
      Measurable.of_comap_le ((hF.Z_le i).trans (le_sup_left.trans le_sup_right))
    refine isChartGaussAt_congr_ae (hF.measurable_B i) (hY i) (hg i 0)
      ((hF.measurable_initialMean i).comp hZm) ?_
    filter_upwards [hF.initial_identification i (g i 0) (hg i 0)] with x hx hxB hxq
    exact (hx hxB hxq).symm
  have hglued : ∀ i (t : ℝ≥0), 0 < t → ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (t : ℝ≥0∞) < (D.code i x).life →
      IsGluedSlitSample (D.data i).κ (withQ (D.data i) ((D.initial i).correction (D.Z i x)))
        ((D.initial i).cutoff (D.Z i x)) (D.initial i).neighbourhood (D.code i x) t
        (D.physicalDriver i t x) (D.physicalPath i t x) (D.start i t x) (D.duration i t x) (D.chart i x)
        (D.domain i t x) (D.chartPath i t x) (D.chartLife i t x)
        (fun j => D.time j i t x) (fun j => D.patches j i t x) (D.sets i t x) (fun j => D.mean j i t x)
        (fun j => D.physicalMean j i t x) := by
    intro i t ht
    filter_upwards [hF.glued i t ht] with x hx hxB hxq
    have hgood : PathGood (D.data i) (D.code i x) :=
      Aux61GInst.pathGood_accessExitCode (hF.spec i) (hF.open_window i) (hF.zero_window i) (hF.landing i)
        (hF.injective_path i) (D.data i) (hF.data_window i) (hF.data_clearance i)
        (Aux61GInst.mem_exitEv_of_lt_accessLife hxq)
    exact (hx hxB hxq).isGluedSlitSample (D.initial i) (D.Z i x) hgood hxq
  have hmean : ∀ i (t : ℝ≥0), ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (t : ℝ≥0∞) < (D.code i x).life →
      ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (chartHull (D.code i) t x) →
        g i t x ψ = ∫ z, Aux61UnionK.canonMean (withQ (D.data i) ((D.initial i).correction (D.Z i x)))
          ((D.initial i).cutoff (D.Z i x)) (ULift.up.{u} (D.code i x)) t z * ψ z := by
    intro i t
    by_cases ht : t = 0
    · subst t
      exact (Aux61GStep.isChartMeanAt_zero_of_initialData (hF.measurable_Z i) (hY i) (hF.measurable_B i)
        (D.initial i) (hG0 i)) (g i 0) (hg i 0)
    · have ht0 : 0 < t := pos_iff_ne_zero.2 ht
      exact (Aux61GStep.isChartMeanAt_of_initialData (hF.measurable_Z i) (hY i) (hF.measurable_B i)
        (D.initial i) (hG0 i) (hg i t) (asmSigma_zero_le _ (hF.marks_mono i t)) (hglued i t ht0)
        (hF.comparison_cover i t ht0) (hF.comparison_limits i t (g i t) (hg i t) ht0)) (g i t) (hg i t)
  exact Aux61GCont.hasFibreLocalCover_of_captured_access D.Z hF.measurable_Z D.B hF.measurable_B
    D.data D.initialMean D.initial D.event D.chart D.path D.life hF.spec D.window hF.open_window
    hF.zero_window hF.landing hF.injective_path hF.continuous_lift D.field hF.measurable_field D.scale
    D.constant hF.data_window hF.data_clearance D.left D.right hF.reference hF.physical_stop
    hF.history_cover hF.completed_window D.sigma g hg hmean

end InteractingSLE.Sec5.Aux61Asm
