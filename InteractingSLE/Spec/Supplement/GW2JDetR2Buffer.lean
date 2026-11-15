/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetStop

/-!
# GW2: regular stopped driver models under retained-record kernels

`IsRegularStoppedDriver` records the primitive stopped coupling and the regular
Galmarino rule required by the proved Aux. 54. `StoppedKernelBuffer` records a
joint field-driver law on a buffer, rather than only its field marginal. No
determination conclusion is a field of either object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u v

namespace InteractingSLE.Theorem14.GW2JDetR2

open Restart Exist Exist.Staged LawUnique Sec2.Assembly Supp8.GB6 Supp8.GB6.RelDrv

/-- A driver coupled to the shifted field through a regular Galmarino stop.
All coupling predicates and regularity predicates are the existing ones. -/
def IsRegularStoppedDriver (κ θ : ℝ) (c : BoundaryWord) {S : Type v}
    [mS : MeasurableSpace S] (Q : Measure S) (Hc : S → DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → S → ℝ) (e : S → ℝ≥0∞) : Prop :=
  ∃ (X : S → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mS)
    (VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → S → ℝ)
    (VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → S → ℝ)
    (B : ℝ≥0 → S → ℝ)
    (R : HistorySpace (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) → ℝ≥0∞),
    (∀ z, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc z) (X z)) ∧
    StoppedExtend.IsStoppedHullCoupling κ
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
      Q 𝓕 W VL VR B e X ∧
    Measurable R ∧ StoppedExtendWF.IsHistGalmarino R ∧
    (∀ᵐ z ∂Q, e z = R (killedHistory W VL VR e z)) ∧
    Aux54.IsRegularStop (flowLineRhoL κ c.fn c.jumps 0 θ)
      (flowLineRhoR κ c.fn c.jumps 0 θ) Q W VL VR e

/-- A regular stopped model has a good canonical code and matches it through
its stop. This uses the landed determination theorem and corrected Aux. 54. -/
theorem IsRegularStoppedDriver.ae_good_match
    (h12p : Theorem12ParamStatement.{v}) (h13 : Theorem13Statement.{v})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0})
    {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) {c : BoundaryWord} (hc : c.IsSorted)
    {S : Type v} [MeasurableSpace S] {Q : Measure S} [IsProbabilityMeasure Q]
    {Hc : S → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → S → ℝ} {e : S → ℝ≥0∞}
    (hG : IsGFFWithBoundaryData Q Hc c.fn c.jumps)
    (hW : ∀ t, Measurable (W t)) (he : Measurable e)
    (hcont : ∀ z, ContinuousOn (fun t => W t z) {t | (t : ℝ≥0∞) < e z})
    (hmodel : IsRegularStoppedDriver κ θ c Q Hc W e) :
    ∀ᵐ z ∂Q, IsGoodDrvCode (F (c, Hc z)) ∧
      IsStopDrvMatch (F (c, Hc z)) (fun t => W t z) (e z) := by
  obtain ⟨X, 𝓕, VL, VR, B, R, hX, hSC, hRm, hRG, hRe, hreg⟩ := hmodel
  have hm := GW2JDet.ae_stopped_driver_eq_drvDec h12p h13 h12p₀ h13₀ hκ hF hc
    hG hX hSC hRm hRG hRe hreg hW he hcont
    (Eventually.of_forall fun _ _ _ => rfl)
  filter_upwards [hm, GW2JDet.ae_isGoodDrvCode_of_isGFF_theta h12p₀ h13₀ hκ hF hc hG]
    with z hz hg
  exact ⟨hg, hz.1⟩

/-- One stopped relative experiment with its complete joint field-driver law
given the retained datum `r`. The model carrier belongs to `Type`, independently
of the universe of the original sample space. -/
structure StoppedKernelBuffer (κ θ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) {C : Type v} [MeasurableSpace C] (r : Ω → C) (M : Set Ω)
    (word : C → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens) where
  sampleSpace : Type
  [mSample : MeasurableSpace sampleSpace]
  sample : Ω → sampleSpace
  measurable_sample : Measurable sample
  field : sampleSpace → DistOn upperHalfPlaneOpens
  measurable_field : Measurable field
  driver : ℝ≥0 → sampleSpace → ℝ
  measurable_driver : ∀ t, Measurable (driver t)
  stop : sampleSpace → ℝ≥0∞
  measurable_stop : Measurable stop
  continuous_driver : ∀ z, ContinuousOn (fun t => driver t z)
    {t | (t : ℝ≥0∞) < stop z}
  kernel : Kernel C sampleSpace
  [markov : IsMarkovKernel kernel]
  law : (P.restrict M).map (fun ω => (r ω, sample ω)) =
    (P.restrict M).map r ⊗ₘ kernel
  models : ∀ᵐ x ∂(P.restrict M).map r, (word x).IsSorted ∧
    IsGFFWithBoundaryData (kernel x) field (word x).fn (word x).jumps ∧
    IsRegularStoppedDriver κ θ (word x) (kernel x) field driver stop
  field_eq : ∀ᵐ ω ∂P, ω ∈ M → field (sample ω) = Hc ω

/-- A stopped joint kernel determines its physical sample's relative driver.
The original probability space need not be standard Borel. -/
theorem StoppedKernelBuffer.ae_good_match
    (h12p : Theorem12ParamStatement.{0}) (h13 : Theorem13Statement.{0})
    {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Type v} [MeasurableSpace C] {r : Ω → C} (hr : Measurable r)
    {M : Set Ω} (hM : MeasurableSet M) {word : C → BoundaryWord} (hw : Measurable word)
    {Hc : Ω → DistOn upperHalfPlaneOpens}
    (D : StoppedKernelBuffer κ θ P r M word Hc) :
    ∀ᵐ ω ∂P, ω ∈ M → IsGoodDrvCode (F (word (r ω), Hc ω)) ∧
      IsStopDrvMatch (F (word (r ω), Hc ω))
        (fun t => D.driver t (D.sample ω)) (D.stop (D.sample ω)) := by
  let _ := D.mSample
  have := D.markov
  have hcode : Measurable fun p : C × D.sampleSpace => F (word p.1, D.field p.2) :=
    hF.1.comp ((hw.comp measurable_fst).prodMk (D.measurable_field.comp measurable_snd))
  have hgood : MeasurableSet {p : C × D.sampleSpace |
      IsGoodDrvCode (F (word p.1, D.field p.2))} := hcode measurableSet_isGoodDrvCode
  have hmatch : MeasurableSet {p : C × D.sampleSpace |
      IsStopDrvMatch (F (word p.1, D.field p.2))
        (fun t => D.driver t p.2) (D.stop p.2)} :=
    measurableSet_isStopDrvMatch hcode
      (fun t => (D.measurable_driver t).comp measurable_snd)
      (D.measurable_stop.comp measurable_snd)
  have htransfer := Sec5.MarkovOther.ae_mem_of_compProd_eq_prod hM hr
    D.measurable_sample D.law (hgood.inter hmatch) ?_
  · filter_upwards [htransfer, D.field_eq] with ω hω hfield hωM
    have hm := hω hωM
    change IsGoodDrvCode (F (word (r ω), D.field (D.sample ω))) ∧
      IsStopDrvMatch (F (word (r ω), D.field (D.sample ω)))
        (fun t => D.driver t (D.sample ω)) (D.stop (D.sample ω)) at hm
    rwa [hfield hωM] at hm
  filter_upwards [D.models] with x hx
  exact hx.2.2.ae_good_match h12p h13 h12p h13 hκ hF hx.1 hx.2.1
    D.measurable_driver D.measurable_stop D.continuous_driver

end InteractingSLE.Theorem14.GW2JDetR2
