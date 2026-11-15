/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# The seeded coupling interface and its measure assembly

Packet PROVE-ZHAN-GT4-A22. The first base measure is already the seeded
force law. The density is `M* m₂`, so its first marginal is the unchanged
seeded base and its second marginal is `m₂ P₂`. The remaining two-view
calculation enters only as the explicit row and column normalization
identities. No ordinary protected-mark hypothesis is imposed on seeds.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}

/-- The seeded coupling with the source density only in the second base.
For the application `M` is the patched normalized seeded density. -/
def seedDualCoupling (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (M : Ω₁ × Ω₂ → ℝ≥0∞) (a₂ : Ω₂ → ℝ≥0∞) : Measure (Ω₁ × Ω₂) :=
  (P₁.prod P₂).withDensity fun ω => M ω * a₂ ω.2

/-- The conditional second-coordinate law given the seeded first path. -/
def seedDualKernel (P₂ : Measure Ω₂) [SFinite P₂]
    (M : Ω₁ × Ω₂ → ℝ≥0∞) (a₂ : Ω₂ → ℝ≥0∞) : Kernel Ω₁ Ω₂ :=
  (Kernel.const Ω₁ P₂).withDensity fun ω₁ ω₂ => M (ω₁, ω₂) * a₂ ω₂

/-- The precise measure inputs still needed from the two-view seeded
martingale calculation. They are normalization integrals of the actual
patch and the amalgamated source density, not hypotheses asserting a
coupling, its marginals, or an image law. -/
structure SeedDualHyp (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (M : Ω₁ × Ω₂ → ℝ≥0∞) (a₂ : Ω₂ → ℝ≥0∞) : Prop where
  measurable_patch : Measurable M
  measurable_source : Measurable a₂
  row_mass : ∀ ω₁, ∫⁻ ω₂, M (ω₁, ω₂) * a₂ ω₂ ∂P₂ = 1
  column_mass : ∀ ω₂, ∫⁻ ω₁, M (ω₁, ω₂) ∂P₁ = 1

namespace SeedDualHyp

variable {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {M : Ω₁ × Ω₂ → ℝ≥0∞}
  {a₂ : Ω₂ → ℝ≥0∞} (h : SeedDualHyp P₁ P₂ M a₂)

include h

/-- Every conditional seeded image measure has mass one. -/
theorem isMarkovKernel [SFinite P₂] : IsMarkovKernel (seedDualKernel (m₁ := m₁) P₂ M a₂) := by
  refine ⟨fun ω₁ => ⟨?_⟩⟩
  rw [seedDualKernel, Kernel.withDensity_apply' _
    (h.measurable_patch.mul (h.measurable_source.comp measurable_snd)), Kernel.const_apply,
    Measure.restrict_univ]
  exact h.row_mass ω₁

/-- The coupling is the composition-product of the seeded base and its
conditional image kernel. This also gives the conditional image law once
the concrete one-rectangle kernel has been identified. -/
theorem eq_compProd [SFinite P₁] [SFinite P₂] :
    seedDualCoupling P₁ P₂ M a₂ = P₁ ⊗ₘ seedDualKernel P₂ M a₂ := by
  have : IsMarkovKernel (seedDualKernel (m₁ := m₁) P₂ M a₂) := h.isMarkovKernel
  have : IsMarkovKernel ((Kernel.const Ω₁ P₂).withDensity
      (fun ω₁ ω₂ => M (ω₁, ω₂) * a₂ ω₂)) := h.isMarkovKernel
  rw [seedDualKernel, Measure.compProd_withDensity
    (h.measurable_patch.mul (h.measurable_source.comp measurable_snd)), Measure.compProd_const]
  rfl

/-- The first marginal stays the original seeded force law. -/
theorem map_fst [SFinite P₁] [SFinite P₂] :
    (seedDualCoupling P₁ P₂ M a₂).map Prod.fst = P₁ := by
  have : IsMarkovKernel (seedDualKernel (m₁ := m₁) P₂ M a₂) := h.isMarkovKernel
  rw [h.eq_compProd]
  exact Measure.fst_compProd _ _

/-- The second marginal is the amalgamated source law `a₂ P₂`. -/
theorem map_snd [SFinite P₁] [SFinite P₂] :
    (seedDualCoupling P₁ P₂ M a₂).map Prod.snd = P₂.withDensity a₂ := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA, seedDualCoupling,
    withDensity_apply _ (measurable_snd hA), withDensity_apply _ hA]
  have he : Prod.snd ⁻¹' A = (univ : Set Ω₁) ×ˢ A := by ext ω; simp
  have hm : Measurable (fun ω : Ω₁ × Ω₂ => M ω * a₂ ω.2) :=
    h.measurable_patch.mul (h.measurable_source.comp measurable_snd)
  rw [he, ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod_symm _ hm.aemeasurable]
  apply lintegral_congr
  intro ω₂
  have hm₂ : Measurable (fun ω₁ : Ω₁ => M (ω₁, ω₂)) :=
    h.measurable_patch.comp (measurable_id.prodMk measurable_const)
  change (∫⁻ ω₁, M (ω₁, ω₂) * a₂ ω₂ ∂P₁) = a₂ ω₂
  rw [lintegral_mul_const _ hm₂, h.column_mass, one_mul]

/-- Probability normalization follows from the unchanged first marginal;
no separate total-mass hypothesis is needed. -/
theorem isProbabilityMeasure [IsProbabilityMeasure P₁] [SFinite P₂] :
    IsProbabilityMeasure (seedDualCoupling P₁ P₂ M a₂) := by
  have hi : IsProbabilityMeasure ((seedDualCoupling P₁ P₂ M a₂).map Prod.fst) := by
    rw [h.map_fst]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

/-- The amalgamated source density is normalized as a consequence of the
two-view identities. -/
theorem isProbabilityMeasure_source [IsProbabilityMeasure P₁] [SFinite P₂] :
    IsProbabilityMeasure (P₂.withDensity a₂) := by
  have := h.isProbabilityMeasure
  rw [← h.map_snd]
  infer_instance

/-- Rectangle events are evaluated by the actual conditional image
kernel, as required for the seeded coupling assembly. -/
theorem apply_prod [SFinite P₁] [SFinite P₂] {A : Set Ω₁} {B : Set Ω₂}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    seedDualCoupling P₁ P₂ M a₂ (A ×ˢ B) =
      ∫⁻ ω₁ in A, ∫⁻ ω₂ in B, M (ω₁, ω₂) * a₂ ω₂ ∂P₂ ∂P₁ := by
  have : IsMarkovKernel (seedDualKernel (m₁ := m₁) P₂ M a₂) := h.isMarkovKernel
  rw [h.eq_compProd, Measure.compProd_apply_prod hA hB]
  apply lintegral_congr
  intro ω₁
  exact Kernel.withDensity_apply' _
    (h.measurable_patch.mul (h.measurable_source.comp measurable_snd)) ω₁ B

end SeedDualHyp

end InteractingSLE.ZhanGT4
