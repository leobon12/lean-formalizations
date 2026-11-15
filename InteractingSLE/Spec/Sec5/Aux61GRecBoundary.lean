/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GRecMeas
import InteractingSLE.Spec.Sec5.Aux61MarksData
import InteractingSLE.Spec.Sec5.Aux61GVanInitial

/-! # MARKS's initial boundary field from physical-space boundary data

The exact predicate of the record is measurable. Thus its almost-sure
assertion under the record law is equivalent to its pullback. The physical
patch/cutoff constructor supplies that pullback without any measurability
claim about the physical cutoff family as a function of the record.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped ENNReal

namespace InteractingSLE.Sec5.Aux61GRec
open Aux61Marks (MarksData)
open Aux61GCont (InitialWindowData)
open Aux61ChLoc (IsChartGaussAt)

universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} (D : MarksData μ)

/-- The initial germ is already retained among the initial marks. -/
theorem sigma_zero_eq_marks (i : D.ι) : D.sigma i 0 = D.marks i 0 :=
  le_antisymm (D.sigma_zero_le_marks i) (le_sup_left.trans le_sup_right)

/-- The conditioning algebra required by the time-zero comparison theorem
is exactly MARKS's initial assembly algebra. -/
theorem sigma_zero_eq_live_germ_sup_marks (i : D.ι) :
    D.sigma i 0 =
      LocalSets.germSigma
        (Aux61ChLoc.liveSet (Aux61ChLoc.liveEv (D.Z i) (D.B i) (D.code i) 0)
          (D.liveSets i 0)) D.cfield ⊔ D.marks i 0 := by
  rw [sigma_zero_eq_marks D i, Aux61Nest.liveSet_idem]
  exact (sup_eq_right.2 le_sup_right).symm

/-- The exact record-law boundary assertion is equivalent to its physical
pullback. The harmonicity premise is preserved in both directions. -/
theorem initialBoundary_iff_physical (i : D.ι)
    (hZ : Measurable (D.Z i)) (hB : MeasurableSet (D.B i))
    {g : X → DistOn upperHalfPlaneOpens} (hg : Measurable g) :
    D.InitialBoundary i g ↔
      ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → IsHarmonicDistOn (g x) H →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
        (∀ ψ : TestOn upperHalfPlaneOpens, g x ψ = ∫ z, v z * ψ z) →
        ∀ a ∈ (D.data i).O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 (D.data i) z)
          (𝓝[H] (a : ℂ)) (𝓝 0) :=
  ae_map_iff (Aux61GHist.measurable_meanHistory hZ hg).aemeasurable
    (measurableSet_record_boundary (D.data i) hB)

/-- Physical correction/cutoff data on the selected event prove MARKS's
initial boundary property on the law of the actual retained mean. -/
theorem initialBoundary_of_initialData (i : D.ι)
    (hZ : Measurable (D.Z i)) (hB : MeasurableSet (D.B i))
    {g : X → DistOn upperHalfPlaneOpens} (hg : Measurable g)
    (Dphys : InitialWindowData X (μ.restrict (D.Z i ⁻¹' D.B i)) (D.data i) g) :
    D.InitialBoundary i g := by
  apply (initialBoundary_iff_physical D i hZ hB hg).2
  have hp := (ae_restrict_iff' (hB.preimage hZ)).1
    (Aux61GVan.ae_boundary_identification_of_initialData Dphys)
  filter_upwards [hp] with x hx hxB _
  exact hx hxB

/-- The exact existential field `MarksFacts.initial_boundary` follows from
an actual initial Gaussian decomposition and its constructed physical data.
Measurability of the mean and history follow from the Gaussian marks. -/
theorem initial_boundary_of_gauss_initialData (i : D.ι)
    (hB : MeasurableSet (D.B i)) {g : X → DistOn upperHalfPlaneOpens}
    (hG : IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) g)
    (Dphys : InitialWindowData X (μ.restrict (D.Z i ⁻¹' D.B i)) (D.data i) g) :
    ∃ g : X → DistOn upperHalfPlaneOpens,
      IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) g ∧
        D.InitialBoundary i g :=
  ⟨g, hG, initialBoundary_of_initialData D i
    (Measurable.of_comap_le (hG.marksZ.trans hG.le)) hB
    (hG.measurable.mono hG.le le_rfl) Dphys⟩

/-- On-event almost-sure equality of retained means preserves the exact
record-law boundary property, even though the two record laws may differ. -/
theorem initialBoundary_congr_ae (i : D.ι)
    (hZ : Measurable (D.Z i)) (hB : MeasurableSet (D.B i))
    {g g' : X → DistOn upperHalfPlaneOpens} (hg : Measurable g) (hg' : Measurable g')
    (heq : ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → g x = g' x)
    (hbd : D.InitialBoundary i g) : D.InitialBoundary i g' := by
  apply (initialBoundary_iff_physical D i hZ hB hg').2
  filter_upwards [(initialBoundary_iff_physical D i hZ hB hg).1 hbd, heq]
    with x hx he hxB
  rw [← he hxB]
  exact hx hxB

end InteractingSLE.Sec5.Aux61GRec
