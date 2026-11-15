/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWMarks
import InteractingSLE.Spec.Sec5.Aux61SlitWContain
import InteractingSLE.Spec.Sec5.Aux61MarksOn
import InteractingSLE.Spec.Sec5.Aux61AsmSlitOn

/-! # The universal assembly data built from the physical marked data -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61Asm
universe u

/-- Build the universal assembly with its retained initial mean and live sets
from MARKS' physical data. -/
abbrev asmDataOnOfMarks (D : MarksDataOn.{u}) (hF : MarksFactsOn D) : AsmDataOn.{u} := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs).toAsmData
    (hF t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- The built universal assembly has all base facts from MARKS' physical
and captured-cover facts. -/
theorem asmBaseFactsOn_of_marks (D : MarksDataOn.{u}) (hF : MarksFactsOn D) (hC : MarksCoverOn D) :
    AsmBaseFactsOn (asmDataOnOfMarks D hF) := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact asmBaseFacts_toAsmData
    (hF t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hC t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- MARKS' comparison objects are the comparison objects for the built
universal assembly, with no change of sets or marks. -/
abbrev slitWiringDataOnOfMarks (D : MarksDataOn.{u}) (hF : MarksFactsOn D)
    (W : MarksWiringDataOn D hF) : SlitWiringDataOn (asmDataOnOfMarks D hF) := W

/-- The physical comparison wiring passes to the universal assembly. -/
theorem slitWiringOn_of_marks (D : MarksDataOn.{u}) (hF : MarksFactsOn D)
    (W : MarksWiringDataOn D hF) (hW : MarksWiringOn D hF W) :
    SlitWiringOn (asmDataOnOfMarks D hF) (slitWiringDataOnOfMarks D hF W) := hW

/-- The universal assembly, including the comparison limits, for the MARKS
construction. The local comparison is supplied by the constructed wiring. -/
theorem asmFactsOn_of_marks (D : MarksDataOn.{u}) (hF : MarksFactsOn D) (hC : MarksCoverOn D)
    (W : MarksWiringDataOn D hF) (hW : MarksWiringOn D hF W) :
    AsmFactsOn (asmDataOnOfMarks D hF) := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact asmFacts_of_slitWiring _
    (asmBaseFacts_toAsmData
      (hF t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
      (hC t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs))
    (W t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hW t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

end InteractingSLE.Sec5.Aux61SlitW
