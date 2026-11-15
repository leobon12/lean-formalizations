/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceWiring

/-! # Concrete source MARKS data, assembly and fibre cover in every setting -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61Asm Aux61Kernel Aux61FibData Prop51G Cond44Ref WangWu LawUnique GlueCond
universe u

/-- Collect the original source binders, without adding any hypotheses. -/
abbrev sourceSetting (t : ℚ) (c : WinCode) (ht : 0 < t)
    (κ : ℝ) (hκ : 0 < κ) (hκ4 : κ < 4) (a b θ₁ θ₂ : ℝ) (h12 : θ₁ < θ₂) (hG : ¬ IsLargeGap κ θ₁ θ₂)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [hP : IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) (({0} : Finset ℝ) : Set ℝ))
    (hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ)
    {Ω₂ : Type u} [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [hP₂ : IsProbabilityMeasure P₂]
    (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [hK : IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) (s : ℚ) (hs : 0 < s) :
    SourceSetting.{u} where
  t := t
  windowCode := c
  t_pos := ht
  κ := κ
  κ_pos := hκ
  κ_lt_four := hκ4
  a := a
  b := b
  θ₁ := θ₁
  θ₂ := θ₂
  angle_lt := h12
  small_gap := hG
  bound_right := hb
  bound_left := ha
  Ω := Ω
  mΩ := mΩ
  P := P
  prob := hP
  field := h
  path := η
  life := ζ
  gff := hh
  flow := hfl
  Ω₂ := Ω₂
  mΩ₂ := mΩ₂
  P₂ := P₂
  prob₂ := hP₂
  field₂ := h₂
  W₂ := W₂
  life₂ := ζ₂
  counterflow := hcf
  field_law := hlaw
  kernel := k
  markov := hK
  kernel_law := hk
  s := s
  s_pos := hs

variable (F : ∀ S : SourceSetting.{u}, SourceRestartData S.Ω S.nL S.nR)

/-- Concrete physical source data in all original small-gap settings. -/
def sourceMarksDataOn : MarksDataOn.{u} := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  let S := sourceSetting t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  exact S.marksData (F S)

variable (I : ∀ S : SourceSetting.{u}, S.Inputs (F S))
include I

/-- All MARKS facts for the concrete source, from the named upstream inputs. -/
theorem sourceMarksFactsOn : MarksFactsOn (sourceMarksDataOn F) := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  let S := sourceSetting t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  exact S.marksFacts (F S) (I S)

/-- The physical history/window inputs give the cover of the concrete source. -/
theorem sourceMarksCoverOn : MarksCoverOn (sourceMarksDataOn F) := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  let S := sourceSetting t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  exact S.marksCover (F S) (I S)

/-- The physical comparison wiring, constructed in each original setting. -/
def sourceMarksWiringDataOn : MarksWiringDataOn (sourceMarksDataOn F) (sourceMarksFactsOn F I) := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  let S := sourceSetting t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  exact S.wiring (F S) (I S)

/-- `SlitWiring` holds for the constructed physical comparisons in every setting. -/
theorem sourceMarksWiringOn :
    MarksWiringOn (sourceMarksDataOn F) (sourceMarksFactsOn F I) (sourceMarksWiringDataOn F I) := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  let S := sourceSetting t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  exact S.wiring_facts (F S) (I S)

/-- The constructed universal assembly, retaining the initial mean and live sets. -/
abbrev sourceAsmDataOn : AsmDataOn.{u} :=
  asmDataOnOfMarks (sourceMarksDataOn F) (sourceMarksFactsOn F I)

/-- The constructed universal slit comparison data. -/
abbrev sourceSlitWiringDataOn : SlitWiringDataOn (sourceAsmDataOn F I) :=
  slitWiringDataOnOfMarks (sourceMarksDataOn F) (sourceMarksFactsOn F I) (sourceMarksWiringDataOn F I)

/-- Every physical wiring clause holds for the concrete universal assembly. -/
theorem sourceSlitWiringOn : SlitWiringOn (sourceAsmDataOn F I) (sourceSlitWiringDataOn F I) :=
  slitWiringOn_of_marks (sourceMarksDataOn F) (sourceMarksFactsOn F I)
    (sourceMarksWiringDataOn F I) (sourceMarksWiringOn F I)

/-- All assembly facts, including the physical comparison limits. -/
theorem sourceAsmFactsOn : AsmFactsOn (sourceAsmDataOn F I) :=
  asmFactsOn_of_marks (sourceMarksDataOn F) (sourceMarksFactsOn F I) (sourceMarksCoverOn F I)
    (sourceMarksWiringDataOn F I) (sourceMarksWiringOn F I)

/-- The corrected dyadic fibre cover from the concrete physical source.
Only the explicitly named open MARKS and restart inputs are required. -/
theorem dyCover_of_source :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_marks (sourceMarksDataOn F) (sourceMarksFactsOn F I) (sourceMarksCoverOn F I)
    (sourceMarksWiringDataOn F I) (sourceMarksWiringOn F I)

end InteractingSLE.Sec5.Aux61SlitW
