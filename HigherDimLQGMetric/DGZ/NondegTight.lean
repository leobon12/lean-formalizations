import HigherDimLQGMetric.DGZ.TightExports
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Countable-product tightness for the DGZ joint limit law

The joint law in DGZ Lemma 6.9 has a whole-space metric coordinate and countably many internal
metric coordinates. This lemma ports the tight-marginals argument of
`LQGMetric.DFGPS.isTightMeasureSet_dyProd` to a dependent countable product.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

/-- A family of laws on a countable product is tight when all coordinate laws are tight. -/
theorem nd_isTightMeasureSet_pi {ι : Type*} [Countable ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, OpensMeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
    [∀ i, T2Space (X i)]
    {S : Set (Measure (∀ i, X i))}
    (h : ∀ i, IsTightMeasureSet
      ((fun μ : Measure (∀ i, X i) => μ.map fun x => x i) '' S)) :
    IsTightMeasureSet S := by
  have hcoord := fun i => isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 (h i)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ι
  choose K hK hKm using fun i => hcoord i (δ i) (by simpa using hδpos i)
  refine ⟨univ.pi K, isCompact_univ_pi hK, fun μ hμ => ?_⟩
  have hsub : (univ.pi K : Set (∀ i, X i))ᶜ ⊆
      ⋃ i, (fun x : ∀ i, X i => x i) ⁻¹' (K i)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_univ_pi, not_forall] at hx
    exact mem_iUnion.2 hx
  have hμi : ∀ i, μ ((fun x : ∀ i, X i => x i) ⁻¹' (K i)ᶜ) ≤ δ i := by
    intro i
    have hi := hKm i _ ⟨μ, hμ, rfl⟩
    rwa [Measure.map_apply (measurable_pi_apply i) (hK i).isClosed.isOpen_compl.measurableSet]
      at hi
  exact (measure_mono hsub).trans
    ((measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hμi).trans hδsum.le))

end HigherDimLQGMetric.DGZ
