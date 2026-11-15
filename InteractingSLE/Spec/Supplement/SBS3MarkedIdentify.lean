/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedBoundary
import InteractingSLE.Spec.Supplement.SBS3MarkedKernel
import InteractingSLE.Spec.Supplement.GW2ConeData

/-!
# S3: identify words of two versions of the same marked chart law

Use the retained event before disintegrating equality of the transported
fields. Gaussian boundary-data uniqueness then compares the word values.
Finite differences in their redundant marks do not change physical side
provenance at an unmarked interior landing.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.StagedLaw Restart

/-- Words for almost surely equal GFFs agree away from both finite mark sets. -/
theorem eq_word_values_of_ae_eq {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y Z : Ω → DistOn upperHalfPlaneOpens}
    {c d : BoundaryWord} (hc : c.IsSorted) (hd : d.IsSorted)
    (hY : IsGFFWithBoundaryData P Y c.fn c.jumps)
    (hZ : IsGFFWithBoundaryData P Z d.fn d.jumps) (he : Y =ᵐ[P] Z) :
    ∀ x : ℝ, x ∉ c.jumps → x ∉ d.jumps → c.fn x = d.fn x :=
  GW2Cone.eq_of_isGFFWithBoundaryData
    (c.isBoundedHarmonicExtension_mean hc) (d.isBoundedHarmonicExtension_mean hd)
    (isGFFWithBoundaryData_congr_ae hY hZ.1 he) hZ

/-- Two marked-law versions of the same transported field have the same
word values on their common retained event. Equality of the fields is first
localized on that event and then transferred under its retained kernel. -/
theorem ae_eq_word_values_of_common_chart {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {h Y Z : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {χ : ℝ}
    {β γ : Ω → BoundaryWord} {G : Set Ω} (hG : MeasurableSet[𝒢] G)
    (hc : ∀ᵐ ω ∂P, ω ∈ G → (c ω).IsConformal)
    (hsort : ∀ᵐ ω ∂P, ω ∈ G → (β ω).IsSorted ∧ (γ ω).IsSorted)
    (hTY : ∀ᵐ ω ∂P, ω ∈ G → IsChartTransport (c ω) 1 0 χ (h ω) (Y ω))
    (hTZ : ∀ᵐ ω ∂P, ω ∈ G → IsChartTransport (c ω) 1 0 χ (h ω) (Z ω))
    (hY : ∀ᵐ ω ∂P, ω ∈ G →
      IsGFFWithBoundaryData (condExpKernel P 𝒢 ω) Y (β ω).fn (β ω).jumps)
    (hZ : ∀ᵐ ω ∂P, ω ∈ G →
      IsGFFWithBoundaryData (condExpKernel P 𝒢 ω) Z (γ ω).fn (γ ω).jumps) :
    ∀ᵐ ω ∂P, ω ∈ G → ∀ x : ℝ,
      x ∉ (β ω).jumps → x ∉ (γ ω).jumps → (β ω).fn x = (γ ω).fn x := by
  have he : ∀ᵐ ω ∂P, ω ∈ G → Y ω = Z ω := by
    filter_upwards [hc, hTY, hTZ] with ω hcω hyω hzω hωG
    exact IsChartTransport.unique (hcω hωG) (hyω hωG) (hzω hωG)
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 he,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hG, hsort, hY, hZ]
    with ω heω hGω hsω hyω hzω hωG
  apply eq_word_values_of_ae_eq (hsω hωG).1 (hsω hωG).2 (hyω hωG) (hzω hωG)
  filter_upwards [heω, hGω hωG] with ω' he' hG' using he' hG'

/-- Redundant finite marks in a different word encoding do not change a
physical interior-side predicate. Continuity selects a nearby coordinate
that avoids both mark sets and has the same new-word value. -/
theorem interior_values_of_word_eq {c d : BoundaryWord} {g : ℝ → ℂ} {P : ℝ → Prop}
    (hgc : Continuous g)
    (he : ∀ y : ℝ, y ∉ c.jumps → y ∉ d.jumps → c.fn y = d.fn y)
    (hOld : ∀ y ∉ c.jumps, g y ∈ H → P (c.fn y))
    {x : ℝ} (hx : x ∉ d.jumps) (hxH : g x ∈ H) : P (d.fn x) := by
  have hH : ∀ᶠ y in 𝓝 x, g y ∈ H := hgc.continuousAt.eventually
    (QuantumZipper.isOpen_H.mem_nhds hxH)
  have hv : ∀ᶠ y in 𝓝 x, d.fn y = d.fn x := d.isPiecewiseConstantBoundaryData x hx
  have hAvoid : ∀ᶠ y in 𝓝[≠] x, y ∉ (c.jumps ∪ d.jumps) :=
    GW1W.eventually_notMem_of_finite (c.jumps ∪ d.jumps).finite_toSet x
  have hAll := ((hH.and hv).filter_mono nhdsWithin_le_nhds).and hAvoid
  obtain ⟨y, ⟨hyH, hyV⟩, hyJ⟩ := hAll.exists
  have hyc : y ∉ c.jumps := fun h => hyJ (Finset.mem_union_left _ h)
  have hyd : y ∉ d.jumps := fun h => hyJ (Finset.mem_union_right _ h)
  rw [← hyV, ← he y hyc hyd]
  exact hOld y hyc hyH

end InteractingSLE.Theorem14.SB.S3
