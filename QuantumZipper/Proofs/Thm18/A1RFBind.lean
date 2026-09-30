import QuantumZipper.Proofs.Thm18.A1RFCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RF (2): the full smoothing is the regularized evaluation at one smeared measure

Toward `A1RFFullYStmt` (A1RFCut.lean). For `ρ ≥ 0` let
`ν_ρ = (μ ⊗ m).map Ψ_ρ`, `Ψ_ρ(z, θ) = f_t⁻¹(foldH(z + ρ e^{iθ}))`, with `μ` the pushed side circle
and `m` the normalized angle measure: the pulled-back folded circles of radius `ρ` smeared along
`μ`. Then:

* `A1RF.evalReg_map_prod_eq` (deterministic, any field `x`): if the regularized pairings
  `∫ avgReg x k d((f_t⁻¹)_* fc(z, ρ))` converge for `μ`-a.e. `z` and are bounded uniformly in `k`
  and `z`, then `evalReg x ν_ρ = ∫ evalReg x ((f_t⁻¹)_* fc(z, ρ)) dμ(z)` (Fubini for each `k`,
  dominated convergence in `k`);
* `A1RF.map_prod_zero`: `ν_0 = (f_t⁻¹)_* μ` (the smeared measure at radius `0` is the target).

So the full smoothing node is the continuity at `ρ = 0` of `ρ ↦ evalReg Y ν_ρ`, the continuum
statement of Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 for the family `ν_ρ`.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18
namespace A1RF

variable {Θ : Type*} [MeasurableSpace Θ]

/-- **Regularized pairings of a smeared measure** (Fubini and dominated convergence). -/
theorem tendsto_avgReg_map_prod {x : FieldSample} {μ : Measure ℂ} [IsFiniteMeasure μ]
    {m : Measure Θ} [IsProbabilityMeasure m] {Ψ : ℂ × Θ → ℂ} (hΨ : Measurable Ψ)
    (hbk : ∀ k : ℕ, ∃ M : ℝ, ∀ᵐ p ∂(μ.prod m), |avgReg x k (Ψ p)| ≤ M)
    {M : ℝ} (hdom : ∀ k : ℕ, ∀ᵐ z ∂μ, |∫ θ, avgReg x k (Ψ (z, θ)) ∂m| ≤ M)
    (hconv : ∀ᵐ z ∂μ, Tendsto (fun k : ℕ => ∫ θ, avgReg x k (Ψ (z, θ)) ∂m) atTop
      (𝓝 (evalReg x (m.map fun θ => Ψ (z, θ))))) :
    Tendsto (fun k : ℕ => ∫ u, avgReg x k u ∂((μ.prod m).map Ψ)) atTop
      (𝓝 (∫ z, evalReg x (m.map fun θ => Ψ (z, θ)) ∂μ)) := by
  have hak : ∀ k : ℕ, Measurable (avgReg x k) := fun k =>
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  have hint : ∀ k : ℕ, Integrable (fun p => avgReg x k (Ψ p)) (μ.prod m) := by
    intro k
    obtain ⟨M', hM'⟩ := hbk k
    exact Integrable.mono' (integrable_const M') ((hak k).comp hΨ).aestronglyMeasurable
      (hM'.mono fun p hp => by rw [Real.norm_eq_abs]; exact hp)
  have e : ∀ k : ℕ, ∫ u, avgReg x k u ∂((μ.prod m).map Ψ) =
      ∫ z, ∫ θ, avgReg x k (Ψ (z, θ)) ∂m ∂μ := by
    intro k
    rw [integral_map hΨ.aemeasurable (hak k).aestronglyMeasurable]
    exact integral_prod _ (hint k)
  simp_rw [e]
  refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_)
    (integrable_const M) (fun k => ?_) hconv
  · exact (hint k).integral_prod_left.aestronglyMeasurable
  · exact (hdom k).mono fun z hz => by rw [Real.norm_eq_abs]; exact hz

/-- **`evalReg` of a smeared measure is the integral of the `evalReg`s of its pieces.** -/
theorem evalReg_map_prod_eq {x : FieldSample} {μ : Measure ℂ} [IsFiniteMeasure μ]
    {m : Measure Θ} [IsProbabilityMeasure m] {Ψ : ℂ × Θ → ℂ} (hΨ : Measurable Ψ)
    (hbk : ∀ k : ℕ, ∃ M : ℝ, ∀ᵐ p ∂(μ.prod m), |avgReg x k (Ψ p)| ≤ M)
    {M : ℝ} (hdom : ∀ k : ℕ, ∀ᵐ z ∂μ, |∫ θ, avgReg x k (Ψ (z, θ)) ∂m| ≤ M)
    (hconv : ∀ᵐ z ∂μ, Tendsto (fun k : ℕ => ∫ θ, avgReg x k (Ψ (z, θ)) ∂m) atTop
      (𝓝 (evalReg x (m.map fun θ => Ψ (z, θ))))) :
    evalReg x ((μ.prod m).map Ψ) = ∫ z, evalReg x (m.map fun θ => Ψ (z, θ)) ∂μ :=
  (tendsto_avgReg_map_prod hΨ hbk hdom hconv).limUnder_eq

/-- The pulled-back folded circle as an image of the angle measure. -/
theorem fc_map_eq_angMeas_map {g : ℂ → ℂ} (hg : Measurable g) (z : ℂ) (ρ : ℝ) :
    (foldedCircle z ρ).map g =
      E6.XAreaPC.angMeas.map fun θ => g (foldH (circleMap z ρ θ)) := by
  rw [E6.XAreaPC.foldedCircle_eq_map_angMeas]
  exact Measure.map_map hg (measurable_foldH.comp (measurable_circleMap _ _))

/-- The smearing map `Ψ_ρ(z, θ) = g(foldH(z + ρ e^{iθ}))` is measurable. -/
theorem measurable_smear {g : ℂ → ℂ} (hg : Measurable g) (ρ : ℝ) :
    Measurable fun p : ℂ × ℝ => g (foldH (circleMap p.1 ρ p.2)) := by
  have hc : Continuous fun p : ℂ × ℝ => circleMap p.1 ρ p.2 := by
    unfold circleMap
    fun_prop
  exact hg.comp (measurable_foldH.comp hc.measurable)

/-- **At radius `0` the smeared measure is the target measure.** -/
theorem map_prod_zero {μ : Measure ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ Hbar) {m : Measure ℝ}
    [IsProbabilityMeasure m] [SFinite μ] {g : ℂ → ℂ} (hg : Measurable g) :
    (μ.prod m).map (fun p : ℂ × ℝ => g (foldH (circleMap p.1 0 p.2))) = μ.map g := by
  have e : (fun p : ℂ × ℝ => g (foldH (circleMap p.1 0 p.2))) = (g ∘ foldH) ∘ Prod.fst := by
    funext p; simp [circleMap_zero_radius]
  rw [e, ← Measure.map_map (hg.comp measurable_foldH) measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul]
  refine Measure.map_congr ?_
  filter_upwards [hμ] with z hz
  simp only [comp_apply, foldH, show (0 : ℝ) ≤ z.im from hz, ↓reduceIte]

end A1RF
end R18
end QuantumZipper
