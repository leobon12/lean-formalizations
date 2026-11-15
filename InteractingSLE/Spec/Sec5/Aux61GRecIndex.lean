/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksAsm

/-! # Restrict physical MARKS data to one restart-window index

All physical facts and slit wiring survive this restriction. The selected
mean is the same chosen Gaussian mean, since its existential witness is
reused verbatim. No boundary assertion or local-set fact is added.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace InteractingSLE.Sec5.Aux61GRec
open Aux61Marks (MarksData MarksFacts)
open Aux61Asm (SlitWiringData SlitWiring)

universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- The physical data at one selected index, indexed by a singleton. -/
def singletonMarks (D : MarksData μ) (i : D.ι) : MarksData μ where
  ι := Unit
  β _ := D.β i
  mβ _ := D.mβ i
  Z _ := D.Z i
  B _ := D.B i
  data _ := D.data i
  event _ := D.event i
  chart _ := D.chart i
  path _ := D.path i
  life _ := D.life i
  window _ := D.window i
  field := D.field
  scale := D.scale
  constant := D.constant
  left _ := D.left i
  right _ := D.right i
  originalMean := D.originalMean
  baseMarks _ := D.baseMarks i
  baseSets _ := D.baseSets i
  physicalDriver _ := D.physicalDriver i
  physicalPath _ := D.physicalPath i
  start _ := D.start i
  duration _ := D.duration i
  domain _ := D.domain i
  chartPath _ := D.chartPath i
  chartLife _ := D.chartLife i
  index := D.index
  time j _ := D.time j i
  patches j _ := D.patches j i
  mean j _ := D.mean j i
  physicalMean j _ := D.physicalMean j i
  comparisonEvent j _ := D.comparisonEvent j i

/-- Every physical MARKS fact restricts to the selected index. -/
theorem singletonMarksFacts {D : MarksData μ} (hF : MarksFacts μ D) (i : D.ι) :
    MarksFacts μ (singletonMarks D i) where
  measurable_Z _ := hF.measurable_Z i
  measurable_B _ := hF.measurable_B i
  spec _ := hF.spec i
  open_window _ := hF.open_window i
  zero_window _ := hF.zero_window i
  landing _ := hF.landing i
  injective_path _ := hF.injective_path i
  continuous_lift _ := hF.continuous_lift i
  harmonic_lift _ := hF.harmonic_lift i
  measurable_field := hF.measurable_field
  data_window _ := hF.data_window i
  data_clearance _ := hF.data_clearance i
  reference _ := hF.reference i
  physical_stop _ := hF.physical_stop i
  harmonic_originalMean := hF.harmonic_originalMean
  zero_field := hF.zero_field
  baseMarks_le _ := hF.baseMarks_le i
  baseMarks_mono _ := hF.baseMarks_mono i
  Z_le _ := hF.Z_le i
  code_le _ := hF.code_le i
  event_measurable _ := hF.event_measurable i
  chart_measurable _ := hF.chart_measurable i
  baseSets_marks _ := hF.baseSets_marks i
  baseSets_closed _ := hF.baseSets_closed i
  baseSets_mono _ := hF.baseSets_mono i
  locality _ := hF.locality i
  geometry _ := hF.geometry i
  initial_boundary _ := hF.initial_boundary i
  glued _ := hF.glued i
  comparison_cover _ := hF.comparison_cover i

/-- Restrict the positive-time comparison objects, with the same retained
initial mean and its selected correction data. -/
def singletonWiring {D : MarksData μ} (hF : MarksFacts μ D)
    (W : SlitWiringData (D.toAsmData hF)) (i : D.ι) :
    SlitWiringData ((singletonMarks D i).toAsmData (singletonMarksFacts hF i)) where
  patchMean j _ := W.patchMean j i
  union j _ := W.union j i
  unionMarks j _ := W.unionMarks j i

/-- All slit wiring facts restrict to the same singleton data. -/
theorem singletonWiring_facts {D : MarksData μ} (hF : MarksFacts μ D)
    (W : SlitWiringData (D.toAsmData hF)) (hW : SlitWiring μ (D.toAsmData hF) W)
    (i : D.ι) :
    SlitWiring μ ((singletonMarks D i).toAsmData (singletonMarksFacts hF i))
      (singletonWiring hF W i) where
  scale_eq := hW.scale_eq
  constant_eq _ := hW.constant_eq i
  sets_marks _ := hW.sets_marks i
  patches_measurable j _ := hW.patches_measurable j i
  patches_closed j _ := hW.patches_closed j i
  patches_unbounded j _ := hW.patches_unbounded j i
  patchMean_local j _ := hW.patchMean_local j i
  mean_harmonic j _ := hW.mean_harmonic j i
  mean_represents j _ := hW.mean_represents j i
  unionMarks_le j _ := hW.unionMarks_le j i
  union_measurable j _ := hW.union_measurable j i
  union_closed j _ := hW.union_closed j i
  union_local j _ := hW.union_local j i
  marks_le j _ := hW.marks_le j i
  sets_subset j _ := hW.sets_subset j i
  patches_marks j _ := hW.patches_marks j i
  patches_subset j _ := hW.patches_subset j i
  event_measurable j _ := hW.event_measurable j i
  union_eq j _ := hW.union_eq j i

end InteractingSLE.Sec5.Aux61GRec
