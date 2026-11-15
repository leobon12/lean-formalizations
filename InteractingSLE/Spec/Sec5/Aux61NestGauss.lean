/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NestMarks

/-!
# The initial and later chart decompositions with nested conditioning algebras

Packet PROVE-AUX61-NEST. Construct both decompositions by the existing marked
chart theorem. At the later time retain the initial live germ as an extra
mark; the marked-locality theorem justifies that enlargement. This applies to
any measurable fibre code with the indicated chart field, including completed
access codes, and is independent of which exit-code construction is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Nest

open Aux61Fib (FibCode)
open Aux61FibK (codeFiltration)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet liveSet_of_mem measurableSet_live)
open Aux61UnionK (chartHull)
open LocalSets (germSigma)
open WholeField (IsHistoryAvoidanceLocal centredField)

universe u

variable {X : Type u} {ℋ₀ ℋ : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [mβ : MeasurableSpace β]

/-- The initial and later Gaussian decompositions, with the initial germ
retained among the later marks. No inclusion between the two germ algebras is
assumed. The initial physical set is measurable from the initial record. -/
theorem exists_isChartGaussAt_pair_of_marked
    {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Y : X → FibCode} (hY : Measurable Y) (q : ℝ≥0)
    {h : X → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ)
    {c : X → Chart} (hc : ∀ x, (c x).IsConformal) (a k : ℝ)
    (hfield : ∀ x, Z x ∈ B → ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life →
      (Y x).field = Chart.chartTransport (hc x) 1 a k (h x))
    (hℋ : ℋ ≤ mX) (hℋ₀ : ℋ₀ ≤ ℋ) (hZ₀ : mβ.comap Z ≤ ℋ₀)
    (hY₀ : (codeFiltration.{u} 0).comap (fun x => ULift.up.{u} (Y x)) ≤ ℋ₀)
    (hYq : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ ℋ)
    (hdom : ∀ z, MeasurableSet[ℋ₀] {x | z ∈ (c x).dom})
    (hfwd : ∀ z, Measurable[ℋ₀] ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z))
    (hliftm : ∀ z, Measurable[ℋ₀] ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z))
    (hliftc : ∀ x, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom)
    {A₀ A : X → Set ℂ}
    (hA₀m : Measurable[ℋ₀, hittingSigma] A₀)
    (hAm : Measurable[mX, hittingSigma] A)
    (hA₀c : ∀ x, A₀ x ⊆ H ∧ IsOpen (H \ A₀ x))
    (hAc : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x))
    (hAA : ∀ x, A₀ x ⊆ A x)
    (hloc₀ : IsHistoryAvoidanceLocal ℋ₀ A₀ (centredField h u₀) μ)
    (hloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) μ)
    (hgeo₀ : ∀ᵐ x ∂μ, Z x ∈ B → ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life →
      H \ A₀ x = (c x).2.1 '' (H \ chartHull Y 0 x))
    (hgeo : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      H \ A x = (c x).2.1 '' (H \ chartHull Y q x)) :
    ∃ h₀ hq : X → DistOn upperHalfPlaneOpens,
      IsChartGaussAt μ Z B Y 0
        (germSigma (liveSet (liveEv Z B Y 0) A₀) (centredField h u₀) ⊔ ℋ₀) h₀ ∧
      IsChartGaussAt μ Z B Y q
        (germSigma (liveSet (liveEv Z B Y q) A) (centredField h u₀) ⊔
          (ℋ ⊔ germSigma (liveSet (liveEv Z B Y 0) A₀) (centredField h u₀))) hq ∧
      germSigma (liveSet (liveEv Z B Y 0) A₀) (centredField h u₀) ⊔ ℋ₀ ≤
        germSigma (liveSet (liveEv Z B Y q) A) (centredField h u₀) ⊔
          (ℋ ⊔ germSigma (liveSet (liveEv Z B Y 0) A₀) (centredField h u₀)) := by
  have hℋ₀m : ℋ₀ ≤ mX := hℋ₀.trans hℋ
  have hA₀m' : Measurable[mX, hittingSigma] A₀ := hA₀m.mono hℋ₀m le_rfl
  obtain ⟨h₀, hG₀⟩ := Aux61ChLoc.exists_isChartGaussAt_of_marked hB hY 0 hhm hu₀ hh0
    hc a k hfield hℋ₀m hZ₀ hY₀ hdom hfwd hliftm hliftc hlift hA₀m' hA₀c hloc₀ hgeo₀
  have hS₀ : MeasurableSet[ℋ₀] (liveEv Z B Y 0) := measurableSet_live hZ₀ hY₀ hB
  have hSq : MeasurableSet[ℋ] (liveEv Z B Y q) := measurableSet_live (hZ₀.trans hℋ₀) hYq hB
  have hSS : liveEv Z B Y q ⊆ liveEv Z B Y 0 := by
    intro x hx
    exact ⟨hx.1, lt_of_le_of_lt (by simp only [ENNReal.coe_zero, zero_le]) hx.2⟩
  have hloc' := isHistoryAvoidanceLocal_liveSet_sup_germ hh0 hℋ hSq (hℋ₀ _ hS₀) hSS
    (hA₀m.mono hℋ₀ le_rfl) (fun x => (hA₀c x).1) hAm hAA hloc
  have hmarks : ℋ ⊔ germSigma (liveSet (liveEv Z B Y 0) A₀) (centredField h u₀) ≤ mX :=
    sup_le hℋ (LocalSets.germSigma_le (measurable_liveSet (hℋ₀m _ hS₀) hA₀m')
      (WholeField.measurable_centredField hhm u₀))
  have hsmall : ℋ₀ ≤ ℋ ⊔ germSigma (liveSet (liveEv Z B Y 0) A₀) (centredField h u₀) :=
    hℋ₀.trans le_sup_left
  have hfieldq : ∀ x, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      (Y x).field = Chart.chartTransport (hc x) 1 a k (h x) :=
    fun x hx hq => hfield x hx
      (lt_of_le_of_lt (by simp only [ENNReal.coe_zero, zero_le]) hq)
  have hgeo' : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      H \ liveSet (liveEv Z B Y q) A x = (c x).2.1 '' (H \ chartHull Y q x) := by
    filter_upwards [hgeo] with x hx hxB hxq
    rw [liveSet_of_mem (show x ∈ liveEv Z B Y q from ⟨hxB, hxq⟩)]
    exact hx hxB hxq
  obtain ⟨hq, hGq⟩ := Aux61ChLoc.exists_isChartGaussAt_of_marked hB hY q hhm hu₀ hh0
    hc a k hfieldq hmarks (hZ₀.trans hsmall) (hYq.trans le_sup_left)
    (fun z => hsmall _ (hdom z)) (fun z => (hfwd z).mono hsmall le_rfl)
    (fun z => (hliftm z).mono hsmall le_rfl) hliftc hlift
    (measurable_liveSet (hℋ _ hSq) hAm) (liveSet_properties hAc) hloc' hgeo'
  rw [liveSet_idem] at hGq
  exact ⟨h₀, hq, hG₀, hGq, germ_sup_le_sup_germ hℋ₀ _ _ _⟩

end InteractingSLE.Sec5.Aux61Nest
