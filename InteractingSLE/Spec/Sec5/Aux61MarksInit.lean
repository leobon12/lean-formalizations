/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61AsmCore
import InteractingSLE.Spec.Sec5.Aux61MeanIdUniq
import InteractingSLE.Spec.Sec5.Aux61GHistInitial
import InteractingSLE.Spec.Sec5.Aux61GHistMarks
import InteractingSLE.Spec.Sec5.Aux61GHistHarmonic

/-!
# The time-`0` identification: the time-`0` conditional mean is a function of the retained history

Packet PROVE-AUX61-MARKS. The assembly `Aux61Asm.localCover_of_asm` asks (field `initial_identification`) that every
Gaussian decomposition at fibre time `0` equals `T₀(Z)` almost surely on the live event, for the history `Z` and the
initial distribution `T₀` of the constructed window data. Here:

* **uniqueness at time `0`** (`ae_eq_of_isChartGaussAt_zero`): the chart hull at time `0` is empty, so two
  decompositions given the same σ-algebra agree as distributions (MEAN's `gauss_ae_forall_apply_eq`);
  hence `initial_identification` holds as soon as `T₀ ∘ Z` is itself a decomposition
  (`initial_identification_of_gauss`);
* **the retained record** `meanHistory Z h₀ = (Z, h₀)` of a time-`0` decomposition `h₀` and the explicit initial
  distribution `initialDist d B (z, g) = g` if `z ∈ B` and `g` is harmonic on `ℍ`, the reference distribution otherwise
  (measurable, harmonic everywhere); `initialDist ∘ meanHistory Z h₀` is a decomposition given every σ-algebra for which
  `h₀` is one (`isChartGaussAt_initialDist`), so `initial_identification` holds for the retained record
  (`initial_identification_initialDist`);
* the window data for `initialDist` from the boundary values of the retained mean on the window
  (`nonempty_initialWindowData_initialDist`; GLUEINST's `nonempty_initialWindowData_of_local_history_boundary`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61Fib (FibCode FibData)
open Aux61GCont (InitialWindowData)
open Aux61ChLoc (IsChartGaussAt liveEv)
open Aux61GHist (meanHistory referenceDist)

universe u

section Uniq

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode}

/-- **Uniqueness of the time-`0` decomposition.** Two Gaussian decompositions at fibre time `0` given the same
σ-algebra agree almost surely on the live event (the chart hull at time `0` is empty, so they agree on every test). -/
theorem ae_eq_of_isChartGaussAt_zero [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    {g g' : X → DistOn upperHalfPlaneOpens} (hG : IsChartGaussAt μ Z B Y 0 𝒢 g)
    (hG' : IsChartGaussAt μ Z B Y 0 𝒢 g') :
    ∀ᵐ x ∂μ, Z x ∈ B → ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life → g x = g' x := by
  filter_upwards [Aux61MeanId.gauss_ae_forall_apply_eq hG hG' hY hB] with x hx hxB hxq
  refine ContinuousLinearMap.ext fun ψ => hx hxB hxq ψ ?_
  rw [Aux61OldB.chartHull_zero]
  exact disjoint_empty _

/-- **The time-`0` identification from one decomposition.** If `T₀ ∘ Z` is a decomposition at fibre time `0` given `𝒢`,
then every decomposition at fibre time `0` given `𝒢` is `T₀ ∘ Z` almost surely on the live event (the field
`initial_identification` of `Aux61Asm.AsmBaseFacts`). -/
theorem initial_identification_of_gauss [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    {T₀ : β → DistOn upperHalfPlaneOpens} (hT : IsChartGaussAt μ Z B Y 0 𝒢 fun x => T₀ (Z x))
    (g : X → DistOn upperHalfPlaneOpens) (hg : IsChartGaussAt μ Z B Y 0 𝒢 g) :
    ∀ᵐ x ∂μ, Z x ∈ B → ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life → g x = T₀ (Z x) :=
  ae_eq_of_isChartGaussAt_zero hY hB hg hT

end Uniq

/-! ### The explicit initial distribution of the retained record -/

section Initial

variable {β : Type*} [mβ : MeasurableSpace β]

open scoped Classical in
/-- **The initial distribution of the retained record** `(z, g)`: the retained mean `g` when `z` is in the history
event and `g` is harmonic on `ℍ`, the reference distribution of the data otherwise. -/
def initialDist (d : FibData) (B : Set β) (b : β × DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  if b.1 ∈ B ∧ IsHarmonicDistOn b.2 H then b.2 else referenceDist d

/-- The good set of retained records: in the history event, with a harmonic retained mean. -/
def initialGood (B : Set β) : Set (β × DistOn upperHalfPlaneOpens) :=
  {b | b.1 ∈ B ∧ IsHarmonicDistOn b.2 H}

theorem measurableSet_initialGood {B : Set β} (hB : MeasurableSet B) : MeasurableSet (initialGood B) :=
  (measurable_fst hB).inter (measurable_snd Aux61GHist.measurableSet_isHarmonicDistOn_H)

omit mβ in
theorem initialDist_of_mem {d : FibData} {B : Set β} {b : β × DistOn upperHalfPlaneOpens}
    (hb : b ∈ initialGood B) : initialDist d B b = b.2 := by
  classical
  exact ite_eq_left_of_eq_true _ _ (eq_true (show b.1 ∈ B ∧ IsHarmonicDistOn b.2 H from hb))

omit mβ in
theorem initialDist_of_notMem {d : FibData} {B : Set β} {b : β × DistOn upperHalfPlaneOpens}
    (hb : b ∉ initialGood B) : initialDist d B b = referenceDist d := by
  classical
  exact ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (b.1 ∈ B ∧ IsHarmonicDistOn b.2 H) from hb))

theorem measurable_initialDist (d : FibData) {B : Set β} (hB : MeasurableSet B) :
    Measurable (initialDist d B) := by
  classical
  have e : initialDist d B = (initialGood B).piecewise Prod.snd fun _ => referenceDist d := by
    funext b
    by_cases hb : b ∈ initialGood B
    · rw [initialDist_of_mem hb, piecewise_eq_of_mem _ _ _ hb]
    · rw [initialDist_of_notMem hb, piecewise_eq_of_notMem _ _ _ hb]
  rw [e]
  exact Measurable.piecewise (measurableSet_initialGood hB) measurable_snd measurable_const

omit mβ in
theorem initialDist_harmonic (d : FibData) (B : Set β) (b : β × DistOn upperHalfPlaneOpens) :
    IsHarmonicDistOn (initialDist d B b) H := by
  by_cases hb : b ∈ initialGood B
  · rw [initialDist_of_mem hb]
    exact hb.2
  · rw [initialDist_of_notMem hb]
    exact Aux61GHist.referenceDist_harmonic d

end Initial

section Retained

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {h₀ : X → DistOn upperHalfPlaneOpens}

omit mX mβ in
/-- Retaining the mean does not change the live event. -/
theorem liveEv_meanHistory (Z : X → β) (B : Set β) (Y : X → FibCode) (h₀ : X → DistOn upperHalfPlaneOpens)
    (q : ℝ≥0) : liveEv (meanHistory Z h₀) (B ×ˢ univ) Y q = liveEv Z B Y q := by
  ext x
  simp only [liveEv, meanHistory, mem_ofPred_eq, mem_prod, mem_univ, and_true]

/-- **The retained record carries a decomposition with mean `initialDist`.** If `h₀` is a time-`0` decomposition given
`𝒢`, so is `initialDist d B ∘ meanHistory Z h₀`, for the retained record `(Z, h₀)` and the history event `B × 𝒟'`:
on the live event the chart hull is empty, so `h₀` is harmonic on `ℍ` and `initialDist` returns it. -/
theorem isChartGaussAt_initialDist [IsFiniteMeasure μ] (d : FibData) (hY : Measurable Y) (hB : MeasurableSet B)
    (hG : IsChartGaussAt μ Z B Y 0 𝒢 h₀) :
    IsChartGaussAt μ (meanHistory Z h₀) (B ×ˢ univ) Y 0 𝒢 fun x => initialDist d B (meanHistory Z h₀ x) := by
  have hG' := Aux61GHist.isChartGaussAt_meanHistory hG hG.measurable
  have hZm : Measurable[𝒢] (meanHistory Z h₀) :=
    (Measurable.of_comap_le hG.marksZ).prodMk hG.measurable
  refine Aux61Asm.isChartGaussAt_congr_ae (hB.prod MeasurableSet.univ) hY hG'
    ((measurable_initialDist d hB).comp hZm) ?_
  filter_upwards [hG.harmonic] with x hx hxB hxq
  have hxB' : Z x ∈ B := hxB.1
  have hh : IsHarmonicDistOn (h₀ x) H := by
    have := hx hxB' hxq
    rwa [Aux61OldB.chartHull_zero, sdiff_empty] at this
  exact initialDist_of_mem ⟨hxB', hh⟩

/-- **The time-`0` identification for the retained record**: every decomposition at fibre time `0` given `𝒢` is
`initialDist d B (Z, h₀)` almost surely on the live event. -/
theorem initial_identification_initialDist [IsFiniteMeasure μ] (d : FibData) (hY : Measurable Y)
    (hB : MeasurableSet B) (hG : IsChartGaussAt μ Z B Y 0 𝒢 h₀) (g : X → DistOn upperHalfPlaneOpens)
    (hg : IsChartGaussAt μ (meanHistory Z h₀) (B ×ˢ univ) Y 0 𝒢 g) :
    ∀ᵐ x ∂μ, meanHistory Z h₀ x ∈ B ×ˢ univ → ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life →
      g x = initialDist d B (meanHistory Z h₀ x) :=
  initial_identification_of_gauss hY (hB.prod MeasurableSet.univ) (isChartGaussAt_initialDist d hY hB hG) g hg

end Retained

/-! ### The window data of the explicit initial distribution -/

section Window

variable {β : Type*} [mβ : MeasurableSpace β]

/-- **The window data for `initialDist`** from the boundary values of the retained mean on the window: almost surely
under the law `ν` of the retained record, on the good set every harmonic representative of the retained mean tends to
the reference mean at every window point (off the good set `initialDist` is the reference distribution, whose
comparison is automatic). -/
theorem nonempty_initialWindowData_initialDist (d : FibData) {B : Set β} (hB : MeasurableSet B)
    {ν : Measure (β × DistOn upperHalfPlaneOpens)}
    (hboundary : ∀ᵐ b ∂ν, b.1 ∈ B → IsHarmonicDistOn b.2 H → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v H → (∀ ψ : TestOn upperHalfPlaneOpens, b.2 ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z) (𝓝[H] (a : ℂ)) (𝓝 0)) :
    Nonempty (InitialWindowData (β × DistOn upperHalfPlaneOpens) ν d (initialDist d B)) := by
  refine Aux61GHist.nonempty_initialWindowData_of_local_history_boundary d (B := initialGood B)
    (measurable_initialDist d hB) (ae_of_all _ (initialDist_harmonic d B))
    (fun b hb => initialDist_of_notMem hb) ?_
  filter_upwards [hboundary] with b hb hbG v hv hrep a ha
  rw [initialDist_of_mem hbG] at hrep
  exact hb hbG.1 hbG.2 v hv hrep a ha

end Window

end InteractingSLE.Sec5.Aux61Marks
