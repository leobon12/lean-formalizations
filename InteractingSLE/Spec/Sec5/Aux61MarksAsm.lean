/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksData

/-!
# The assembly facts of the built data: marks, nesting, locality and the time-`0` identification discharged

Packet PROVE-AUX61-MARKS. For the data `D.toAsmData hF` built from the physical marked local sets (`Aux61MarksData`),
every field of `Aux61Asm.AsmBaseFacts` is proved from the physical facts `MarksFacts` and the cover facts `MarksCover`
(`asmBaseFacts_toAsmData`). In particular the fields `marks_le`, `marks_mono`, `Z_le` (the history retains the time-`0`
decomposition, measurable for the retained time-`0` germ), `sets_mono`, `locality` and **`initial_identification`**
are no longer inputs. `localCover_of_marks` gives the fibre cover from SLIT's wiring (W) for the built data.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61Fib (FibCode)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet liveSet_of_mem)
open Aux61UnionK (HasFibreLocalCover)
open Aux61Asm (AsmData AsmBaseFacts asmSigma)
open Aux61GHist (meanHistory)

universe u

/-- Retaining the mean in the history does not change the conditioning algebras. -/
theorem asmSigma_meanHistory {X : Type u} {β : Type*} [MeasurableSpace β] (Z : X → β) (B : Set β) (Y : X → FibCode)
    (h₀ : X → DistOn upperHalfPlaneOpens)
    (A : ℝ≥0 → X → Set ℂ) (ℋ : ℝ≥0 → MeasurableSpace X) (h : X → DistOn upperHalfPlaneOpens) (q : ℝ≥0) :
    asmSigma (meanHistory Z h₀) (B ×ˢ univ) Y A ℋ h q = asmSigma Z B Y A ℋ h q := by
  simp only [asmSigma, liveEv_meanHistory]

variable {X : Type u} [mX : MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {D : MarksData μ}

omit [IsProbabilityMeasure μ] in
/-- The conditioning algebras of the built data are those of the physical history. -/
theorem MarksFacts.sigma_toAsmData (hF : MarksFacts μ D) (i : D.ι) (q : ℝ≥0) :
    (D.toAsmData hF).sigma i q = D.sigma i q :=
  asmSigma_meanHistory _ _ _ _ _ _ _ _

omit [IsProbabilityMeasure μ] in
/-- The retained history is measurable for the assembly marks at time `0`. -/
theorem MarksFacts.measurable_retained (hF : MarksFacts μ D) (i : D.ι) :
    Measurable[D.marks i 0] (meanHistory (D.Z i) (hF.initialMean i)) :=
  (Measurable.of_comap_le ((hF.Z_le i).trans le_sup_left)).prodMk
    ((hF.initialMean_spec i).measurable.mono (D.sigma_zero_le_marks i) le_rfl)

/-- **The assembly facts of the built data.** Every field of `Aux61Asm.AsmBaseFacts` for `D.toAsmData hF`, from the
physical facts and the cover facts; the marks, their nesting, the live sets, their locality and the time-`0`
identification are proved. -/
theorem asmBaseFacts_toAsmData {E : X → Prop} (hF : MarksFacts μ D) (hC : MarksCover μ E D) :
    AsmBaseFacts μ E (D.toAsmData hF) where
  measurable_Z i := Aux61GHist.measurable_meanHistory (hF.measurable_Z i)
    ((hF.initialMean_spec i).measurable.mono (hF.initialMean_spec i).le le_rfl)
  measurable_B i := (hF.measurable_B i).prod MeasurableSet.univ
  spec := hF.spec
  open_window := hF.open_window
  zero_window := hF.zero_window
  landing := hF.landing
  injective_path := hF.injective_path
  continuous_lift := hF.continuous_lift
  harmonic_lift := hF.harmonic_lift
  measurable_field := hF.measurable_field
  data_window := hF.data_window
  data_clearance := hF.data_clearance
  reference := hF.reference
  physical_stop i := by
    filter_upwards [hF.physical_stop i] with x hx hxB
    exact hx hxB.1
  history_cover := by
    filter_upwards [hC.history_cover] with x hx hE
    obtain ⟨i, hi⟩ := hx hE
    exact ⟨i, hi, mem_univ _⟩
  completed_window i := by
    filter_upwards [hC.completed_window i] with x hx hxB hE
    exact hx hxB.1 hE
  measurable_initialMean i := measurable_initialDist (D.data i) (hF.measurable_B i)
  harmonic_originalMean := hF.harmonic_originalMean
  zero_field := hF.zero_field
  marks_le := hF.marks_le
  marks_mono := hF.marks_mono
  Z_le i := (hF.measurable_retained i).comap_le
  code_le i r := (hF.code_le i r).trans le_sup_left
  event_measurable i := le_sup_left (a := D.baseMarks i 0) _ (hF.event_measurable i)
  chart_measurable := hF.chart_measurable_marks
  sets_zero_measurable i := hF.measurable_liveSets_marks i 0
  sets_measurable := hF.measurable_liveSets
  sets_closed := hF.liveSets_closed
  sets_mono := hF.liveSets_mono
  locality := hF.locality_marks
  geometry i r := by
    filter_upwards [hF.geometry_live i r] with x hx hxB hxr
    exact hx hxB.1 hxr
  initial_identification i g hg := by
    have hg' : IsChartGaussAt μ (meanHistory (D.Z i) (hF.initialMean i)) (D.B i ×ˢ univ) (D.code i) 0
        (D.sigma i 0) g := by
      rw [← hF.sigma_toAsmData i 0]
      exact hg
    exact initial_identification_initialDist (D.data i) (hF.measurable_code i) (hF.measurable_B i)
      (hF.initialMean_spec i) g hg'
  glued i t ht := by
    filter_upwards [hF.glued i t ht] with x hx hxB hxq
    have e : D.liveSets i t x = D.baseSets i t x :=
      liveSet_of_mem (show x ∈ liveEv (D.Z i) (D.B i) (D.code i) t from ⟨hxB.1, hxq⟩)
    rw [e]
    exact hx hxB.1 hxq
  comparison_cover i t ht := by
    filter_upwards [hF.comparison_cover i t ht] with x hx hxB hxq
    exact hx hxB.1 hxq

/-- **The fibre cover from the physical marked local sets and SLIT's wiring** for the built data. -/
theorem localCover_of_marks {E : X → Prop} (hF : MarksFacts μ D) (hC : MarksCover μ E D)
    (W : Aux61Asm.SlitWiringData (D.toAsmData hF)) (hW : Aux61Asm.SlitWiring μ (D.toAsmData hF) W) :
    HasFibreLocalCover μ E :=
  Aux61Asm.localCover_of_slitWiring (D.toAsmData hF) (asmBaseFacts_toAsmData hF hC) W hW

/-- **The fibre cover from the physical marked local sets and the comparison limits** for the built data. -/
theorem localCover_of_marks_limits {E : X → Prop} (hF : MarksFacts μ D) (hC : MarksCover μ E D)
    (hlim : ∀ i (t : ℝ≥0) (g : X → DistOn upperHalfPlaneOpens),
      IsChartGaussAt μ ((D.toAsmData hF).Z i) ((D.toAsmData hF).B i) ((D.toAsmData hF).code i) t
        ((D.toAsmData hF).sigma i t) g → 0 < t →
      ∀ᵐ x ∂μ, ∀ j, (D.toAsmData hF).Z i x ∈ (D.toAsmData hF).B i →
        (t : ℝ≥0∞) < ((D.toAsmData hF).code i x).life → x ∈ (D.toAsmData hF).comparisonEvent j i t →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ Aux61UnionK.chartHull ((D.toAsmData hF).code i) t x) →
        (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ Aux61UnionK.chartHull ((D.toAsmData hF).code i) t x →
          g x ψ = ∫ z, v z * ψ z) →
        ∀ z₀ ∈ (D.toAsmData hF).patches j i t x ∪ {z : ℂ | z.im = 0},
          (∃ ε > 0, (D.toAsmData hF).sets i t x ∩ ball z₀ ε ⊆ (D.toAsmData hF).patches j i t x) →
        ∀ l : Filter ℂ, l ≤ 𝓟 (H \ Aux61UnionK.chartHull ((D.toAsmData hF).code i) t x) →
          Tendsto ((D.toAsmData hF).chart i x).2.1 l (𝓝 z₀) →
          Tendsto (fun ζ => v ζ - ((D.toAsmData hF).mean j i t x (((D.toAsmData hF).chart i x).2.1 ζ) + 0 +
            QuantumZipper.chiC ((D.toAsmData hF).data i).κ *
              ((D.toAsmData hF).chart i x).2.2 (((D.toAsmData hF).chart i x).2.1 ζ))) l (𝓝 0)) :
    HasFibreLocalCover μ E :=
  Aux61Asm.localCover_of_asm (D.toAsmData hF) { asmBaseFacts_toAsmData hF hC with comparison_limits := hlim }

end InteractingSLE.Sec5.Aux61Marks
