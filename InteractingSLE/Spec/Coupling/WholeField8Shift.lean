/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField8Local

/-!
# Translation invariance of the zero-boundary covariance on an arbitrary open set

Packet PROVE-WHOLEFIELD8. A flow line from `x` is coupled with the translated field `h(· + x) + θχ`; its retained
range kernel lives in the coordinate of the translated field. The translation `z ↦ z + a` preserves Lebesgue measure
and Dirichlet energy, so the dual Dirichlet norm and the covariance `zeroGFFTestCov` of a zero-boundary GFF on any open
set are invariant (`zeroGFFTestCov_comp_add`):

  `G_{D − a}(ρ(· + a), σ(· + a)) = G_D(ρ, σ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open QuantumZipper

section Shift

variable (a : ℂ)

theorem measurePreserving_add_right_complex : MeasurePreserving (fun z : ℂ => z + a) volume volume :=
  measurePreserving_add_right volume a

theorem measurableEmbedding_add_right_complex : MeasurableEmbedding (fun z : ℂ => z + a) :=
  (Homeomorph.addRight a).measurableEmbedding

/-- The Dirichlet energy is translation invariant. -/
theorem dirichletEnergyOn_comp_add (D : Set ℂ) (f : ℂ → ℝ) :
    dirichletEnergyOn ((fun z => z + a) ⁻¹' D) (fun z => f (z + a)) = dirichletEnergyOn D f := by
  unfold dirichletEnergyOn
  congr 1
  simp_rw [fderiv_comp_add_right]
  exact (measurePreserving_add_right_complex a).setIntegral_preimage_emb
    (measurableEmbedding_add_right_complex a) (fun w => ‖fderiv ℝ f w‖ ^ 2) D

/-- Test functions of `D` translate to test functions of `D − a`. -/
theorem comp_add_mem_zeroSpace {D : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace D) :
    (fun z => f (z + a)) ∈ zeroSpace ((fun z => z + a) ⁻¹' D) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨h1.comp (contDiff_id.add contDiff_const), ?_, ?_⟩
  · exact h2.comp_homeomorph (Homeomorph.addRight a)
  · have e : tsupport (fun z => f (z + a)) = (fun z => z + a) ⁻¹' tsupport f :=
      tsupport_comp_eq_preimage f (Homeomorph.addRight a)
    rw [e]
    exact preimage_mono h3

/-- **The dual Dirichlet norm is translation invariant.** -/
theorem dualNormSq_comp_add (D : Set ℂ) (μ : Measure ℂ) :
    dualNormSq ((fun z => z + a) ⁻¹' D) (zeroSpace ((fun z => z + a) ⁻¹' D)) (μ.map fun z => z - a) =
      dualNormSq D (zeroSpace D) μ := by
  have hint : ∀ g : ℂ → ℝ, Continuous g → ∫ z, g z ∂(μ.map fun z => z - a) = ∫ z, g (z - a) ∂μ := fun g hg =>
    integral_map (continuous_sub_right a).measurable.aemeasurable hg.aestronglyMeasurable
  unfold dualNormSq
  refine le_antisymm (iSup₂_le fun f' hf' => ?_) (iSup₂_le fun f hf => ?_)
  · -- `f' = f(· + a)` with `f = f'(· − a)`
    set f : ℂ → ℝ := fun w => f' (w - a) with hfdef
    have hf : f ∈ zeroSpace D := by
      have h := comp_add_mem_zeroSpace (-a) hf'.1
      have e1 : (fun z => (fun z => z + -a) z + a) = (id : ℂ → ℂ) := funext fun z => by simp
      have e2 : (fun z : ℂ => z + -a) ⁻¹' ((fun z => z + a) ⁻¹' D) = D := by
        ext z; simp
      rw [e2] at h
      simpa [hfdef, sub_eq_add_neg] using h
    have hE : dirichletEnergyOn ((fun z => z + a) ⁻¹' D) f' = dirichletEnergyOn D f := by
      rw [← dirichletEnergyOn_comp_add a D f]
      congr 1
      funext z; simp [hfdef]
    have hI : ∫ z, f' z ∂(μ.map fun z => z - a) = ∫ w, f w ∂μ := hint f' hf'.1.1.continuous
    refine le_trans ?_ (le_iSup₂ (f := fun f (_ : f ∈ {f ∈ zeroSpace D | 0 < dirichletEnergyOn D f}) =>
      ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn D f)) f ⟨hf, hE ▸ hf'.2⟩)
    rw [hI, hE]
  · set f' : ℂ → ℝ := fun z => f (z + a) with hf'def
    have hf' : f' ∈ zeroSpace ((fun z => z + a) ⁻¹' D) := comp_add_mem_zeroSpace a hf.1
    have hE : dirichletEnergyOn ((fun z => z + a) ⁻¹' D) f' = dirichletEnergyOn D f :=
      dirichletEnergyOn_comp_add a D f
    have hI : ∫ z, f' z ∂(μ.map fun z => z - a) = ∫ w, f w ∂μ := by
      rw [hint f' hf'.1.continuous]
      simp [hf'def]
    refine le_trans ?_ (le_iSup₂ (f := fun f (_ : f ∈ {f ∈ zeroSpace ((fun z => z + a) ⁻¹' D) |
        0 < dirichletEnergyOn ((fun z => z + a) ⁻¹' D) f}) =>
      ENNReal.ofReal ((∫ x, f x ∂(μ.map fun z => z - a)) ^ 2 /
        dirichletEnergyOn ((fun z => z + a) ⁻¹' D) f)) f' ⟨hf', hE.symm ▸ hf.2⟩)
    rw [hI, hE]

theorem dualCov_comp_add (D : Set ℂ) (μ ν : Measure ℂ) :
    dualCov ((fun z => z + a) ⁻¹' D) (zeroSpace ((fun z => z + a) ⁻¹' D)) (μ.map fun z => z - a)
        (ν.map fun z => z - a) = dualCov D (zeroSpace D) μ ν := by
  unfold dualCov
  rw [← Measure.map_add _ _ (continuous_sub_right a).measurable, dualNormSq_comp_add,
    dualNormSq_comp_add, dualNormSq_comp_add]

/-- The density measure of a translated function is the translated density measure. -/
theorem withDensity_comp_add (g : ℂ → ℝ≥0∞) :
    volume.withDensity (fun z => g (z + a)) = (volume.withDensity g).map fun z => z - a := by
  ext S hS
  rw [Measure.map_apply (continuous_sub_right a).measurable hS, withDensity_apply _ hS,
    withDensity_apply _ ((continuous_sub_right a).measurable hS)]
  have hmp := measurePreserving_add_right_complex a
  have e : (fun z : ℂ => z + a) ⁻¹' ((fun z => z - a) ⁻¹' S) = S := by
    ext z; simp
  rw [← (hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_add_right_complex a) g
    ((fun z : ℂ => z - a) ⁻¹' S)), e]

/-- **Translation invariance of the zero-boundary covariance** on an arbitrary set:
`G_{D − a}(ρ(· + a), σ(· + a)) = G_D(ρ, σ)` for continuous `ρ, σ`. -/
theorem zeroGFFTestCov_comp_add (D : Set ℂ) {ρ σ : ℂ → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ) :
    zeroGFFTestCov ((fun z => z + a) ⁻¹' D) (fun z => ρ (z + a)) (fun z => σ (z + a)) =
      zeroGFFTestCov D ρ σ := by
  have hpos : ∀ g : ℂ → ℝ, Continuous g → testMeasPos (fun z => g (z + a)) = (testMeasPos g).map fun z => z - a :=
    fun g _ => withDensity_comp_add a (fun z => ENNReal.ofReal (g z))
  have hneg : ∀ g : ℂ → ℝ, Continuous g → testMeasNeg (fun z => g (z + a)) = (testMeasNeg g).map fun z => z - a :=
    fun g _ => withDensity_comp_add a (fun z => ENNReal.ofReal (-g z))
  unfold zeroGFFTestCov
  rw [hpos ρ hρ, hpos σ hσ, hneg ρ hρ, hneg σ hσ, dualCov_comp_add, dualCov_comp_add, dualCov_comp_add,
    dualCov_comp_add]

end Shift

end WholeField

end InteractingSLE
