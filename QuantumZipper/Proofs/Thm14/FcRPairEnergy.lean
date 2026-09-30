import QuantumZipper.Proofs.Thm14.FcRPairKernel

/-!
# FCR-PAIR, part 5: kernel covariances of parametrized measures

Measures of the form `(m.withDensity w).map g` on `ℂ` (`m` a measure on a parameter space `Θ`,
`w ≥ 0` a weight, `g : Θ → ℂ` a parametrization). We express `kernelCov K` of two such measures
as an iterated integral over `Θ × Θ` (`kernelCov_map_withDensity`) and prove the dominated
convergence theorem for iterated integrals (`tendsto_iterated_integral`). These are the
bookkeeping steps of the energy convergence of the semicircle approximations. Own elementary
arguments (change of variables for `Measure.map`/`withDensity`, Fubini, dominated convergence).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

variable {Θ : Type*} [MeasurableSpace Θ]

/-- `kernelCov K` of two parametrized weighted measures, as an iterated integral. -/
theorem kernelCov_map_withDensity {m : Measure Θ} [SFinite m] {w₁ w₂ : Θ → ℝ≥0}
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) {g₁ g₂ : Θ → ℂ} (hg₁ : Measurable g₁)
    (hg₂ : Measurable g₂) {K : ℂ → ℂ → ℝ} (hK : Measurable (Function.uncurry K)) :
    kernelCov K ((m.withDensity fun p => w₁ p).map g₁) ((m.withDensity fun p => w₂ p).map g₂) =
      ∫ p, (w₁ p : ℝ) * ∫ q, (w₂ q : ℝ) * K (g₁ p) (g₂ q) ∂m ∂m := by
  unfold kernelCov
  have hs : StronglyMeasurable fun x : ℂ =>
      ∫ y, K x y ∂((m.withDensity fun p => w₂ p).map g₂) :=
    hK.stronglyMeasurable.integral_prod_right'
  rw [integral_map hg₁.aemeasurable hs.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hw₁]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have hm : Measurable fun y => K (g₁ p) y := hK.comp (measurable_const.prodMk measurable_id)
  simp only
  rw [integral_map hg₂.aemeasurable hm.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hw₂, NNReal.smul_def, smul_eq_mul]
  simp only [NNReal.smul_def, smul_eq_mul]

/-- **Dominated convergence for iterated integrals** over `m ⊗ m`. -/
theorem tendsto_iterated_integral {m : Measure Θ} [SFinite m] {F : ℕ → Θ × Θ → ℝ}
    {F₀ D : Θ × Θ → ℝ} (hF : ∀ j, AEStronglyMeasurable (F j) (m.prod m))
    (hD : Integrable D (m.prod m)) (hb : ∀ j, ∀ᵐ x ∂(m.prod m), ‖F j x‖ ≤ D x)
    (hl : ∀ᵐ x ∂(m.prod m), Tendsto (fun j => F j x) atTop (𝓝 (F₀ x))) :
    Tendsto (fun j => ∫ p, ∫ q, F j (p, q) ∂m ∂m) atTop (𝓝 (∫ p, ∫ q, F₀ (p, q) ∂m ∂m)) := by
  have hi : ∀ j, Integrable (F j) (m.prod m) := fun j => hD.mono' (hF j) (hb j)
  have hF₀m : AEStronglyMeasurable F₀ (m.prod m) := aestronglyMeasurable_of_tendsto_ae _ hF hl
  have hi₀ : Integrable F₀ (m.prod m) := by
    refine hD.mono' hF₀m ?_
    filter_upwards [hl, ae_all_iff.2 hb] with x hx hbx
    exact le_of_tendsto' hx.norm hbx
  have e : ∀ j, ∫ p, ∫ q, F j (p, q) ∂m ∂m = ∫ x, F j x ∂(m.prod m) := fun j =>
    (integral_prod _ (hi j)).symm
  simp_rw [e]
  rw [← integral_prod _ hi₀]
  exact tendsto_integral_of_dominated_convergence D hF hD hb hl

end Thm14WDG
end QuantumZipper
