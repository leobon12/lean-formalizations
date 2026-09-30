import QuantumZipper.Proofs.Thm18.G1FrostAlphaPot

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (3): the Neumann energy of two coupled `α`-Frostman laws

The energy moduli of the smeared-loop family `a1rfNu` (A1RFSmear.lean) are all proved by one
coupling estimate: the members are laws `m.map A`, `m.map A'` of two maps on one probability space
(the angles of the side circle and of the smoothing circle), which are `δ`-close outside an
exceptional set of mass `≤ ε`. For `α`-Frostman laws supported in `closedBall 0 Bf`, the Neumann
potentials are bounded by `potMaxα α CF Bf` and `α/2`-Hölder with constant `holderKα α CF Bf`
(`TwoPoint.abs_neuPot_le`, `TwoPoint.abs_neuPot_sub_le`), hence

* `abs_integral_neuPot_map_sub_le`:
  `|∫ neuPot κ ∘ A dm − ∫ neuPot κ ∘ A' dm| ≤ holderKα · δ^{α/2} + 2 potMaxα · ε`;
* `abs_kernelCov2_map_le`: `|E(m.map A − m.map A')| ≤ 2 (holderKα · δ^{α/2} + 2 potMaxα · ε)`.

This is the abstract form of the coupling step of `TwoPoint.abs_integral_neuPot_coupling_le`
(TwoPointEnergy.lean, where the coupling is the common angle of two pushed circles); own
elementary bookkeeping. Source of the method: Hu–Miller–Peres, Ann. Probab. 38 (2010),
Prop. 2.1; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open TwoPoint Thm18Asm.G1RC

variable {Θ : Type*} [MeasurableSpace Θ] {m : Measure Θ} [IsProbabilityMeasure m]

/-- **Coupling bound for the potential of a fixed Frostman measure.** -/
theorem abs_integral_neuPot_map_sub_le {A A' : Θ → ℂ} (hA : Measurable A) (hA' : Measurable A')
    {κ : Measure ℂ} [IsFiniteMeasure κ] {α CF Bf : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hFκ : IsFrostman κ α CF)
    (hCF : 0 ≤ CF) (hBf0 : 0 ≤ Bf) (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ Bf) (hmκ : κ.real univ = 1)
    (hAb : ∀ᵐ θ ∂m, ‖A θ‖ ≤ Bf) (hA'b : ∀ᵐ θ ∂m, ‖A' θ‖ ≤ Bf) {E : Set Θ}
    (hE : MeasurableSet E) {δ ε : ℝ} (hδ : 0 ≤ δ) (hEε : m.real E ≤ ε)
    (hclose : ∀ᵐ θ ∂m, θ ∉ E → ‖A θ - A' θ‖ ≤ δ) :
    |∫ θ, neuPot κ (A θ) ∂m - ∫ θ, neuPot κ (A' θ) ∂m| ≤
      holderKα α CF Bf * δ ^ (α / 2) + 2 * potMaxα α CF Bf * ε := by
  set Pm := potMaxα α CF Bf with hPm
  set KH := holderKα α CF Bf with hKH
  have hPm0 : 0 ≤ Pm := potMaxα_nonneg hα hCF hBf0
  have hKH0 : 0 ≤ KH := holderKα_nonneg hα hCF hBf0
  have hPb : ∀ x : ℂ, ‖x‖ ≤ Bf → |neuPot κ x| ≤ Pm := fun x hx => by
    have := abs_neuPot_le hFκ hα hCF hBf0 hBκ hx
    rwa [hmκ] at this
  have hH : ∀ x x' : ℂ, ‖x‖ ≤ Bf → ‖x'‖ ≤ Bf →
      |neuPot κ x - neuPot κ x'| ≤ KH * ‖x - x'‖ ^ (α / 2) := fun x x' hx hx' => by
    have := abs_neuPot_sub_le hFκ hα hα1 hCF hBf0 hBκ hx hx'
    rwa [hmκ] at this
  have hmeas : ∀ G : Θ → ℂ, Measurable G → AEStronglyMeasurable (fun θ => neuPot κ (G θ)) m :=
    fun G hG => ((measurable_neuPot κ).comp hG).aestronglyMeasurable
  have hi : ∀ G : Θ → ℂ, Measurable G → (∀ᵐ θ ∂m, ‖G θ‖ ≤ Bf) →
      Integrable (fun θ => neuPot κ (G θ)) m := fun G hG hGb =>
    Integrable.of_bound (hmeas G hG) Pm (hGb.mono fun θ hθ => by
      rw [Real.norm_eq_abs]; exact hPb _ hθ)
  rw [← integral_sub (hi A hA hAb) (hi A' hA' hA'b)]
  set g : Θ → ℝ := fun θ => KH * δ ^ (α / 2) + 2 * Pm * E.indicator 1 θ with hg
  have hind : Integrable (E.indicator (1 : Θ → ℝ)) m := (integrable_const (1 : ℝ)).indicator hE
  have hgi : Integrable g m := (integrable_const _).add (hind.const_mul _)
  have hbound : ∀ᵐ θ ∂m, |neuPot κ (A θ) - neuPot κ (A' θ)| ≤ g θ := by
    filter_upwards [hAb, hA'b, hclose] with θ h1 h2 h3
    have hδp : 0 ≤ KH * δ ^ (α / 2) := mul_nonneg hKH0 (Real.rpow_nonneg hδ _)
    by_cases hθ : θ ∈ E
    · have e : E.indicator (1 : Θ → ℝ) θ = 1 := by simp [hθ]
      simp only [hg, e, mul_one]
      have := hPb _ h1
      have := hPb _ h2
      have := abs_sub (neuPot κ (A θ)) (neuPot κ (A' θ))
      linarith
    · have e : E.indicator (1 : Θ → ℝ) θ = 0 := by simp [hθ]
      simp only [hg, e, mul_zero, add_zero]
      refine (hH _ _ h1 h2).trans (mul_le_mul_of_nonneg_left ?_ hKH0)
      exact Real.rpow_le_rpow (norm_nonneg _) (h3 hθ) (by linarith)
  have hint : ∫ θ, g θ ∂m = KH * δ ^ (α / 2) + 2 * Pm * m.real E := by
    simp only [hg]
    rw [integral_add (integrable_const _) (hind.const_mul _), integral_const,
      integral_const_mul, integral_indicator_one hE]
    simp
  calc |∫ θ, (neuPot κ (A θ) - neuPot κ (A' θ)) ∂m|
      ≤ ∫ θ, |neuPot κ (A θ) - neuPot κ (A' θ)| ∂m := abs_integral_le_integral_abs
    _ ≤ ∫ θ, g θ ∂m := integral_mono_ae ((hi A hA hAb).sub (hi A' hA' hA'b)).abs hgi hbound
    _ = KH * δ ^ (α / 2) + 2 * Pm * m.real E := hint
    _ ≤ KH * δ ^ (α / 2) + 2 * Pm * ε := by nlinarith

omit [IsProbabilityMeasure m] in
/-- `kernelCov neumannH (m.map A) κ = ∫ neuPot κ ∘ A dm`. -/
theorem kernelCov_map_eq {A : Θ → ℂ} (hA : Measurable A) (κ : Measure ℂ) [IsFiniteMeasure κ] :
    kernelCov neumannH (m.map A) κ = ∫ θ, neuPot κ (A θ) ∂m := by
  show ∫ x, neuPot κ x ∂(m.map A) = _
  exact integral_map hA.aemeasurable (measurable_neuPot κ).aestronglyMeasurable

/-- **Energy of two coupled `α`-Frostman laws.** -/
theorem abs_kernelCov2_map_le {A A' : Θ → ℂ} (hA : Measurable A) (hA' : Measurable A')
    {α CF Bf : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hF : IsFrostman (m.map A) α CF)
    (hF' : IsFrostman (m.map A') α CF)
    (hCF : 0 ≤ CF) (hBf0 : 0 ≤ Bf)
    (hAb : ∀ᵐ θ ∂m, ‖A θ‖ ≤ Bf) (hA'b : ∀ᵐ θ ∂m, ‖A' θ‖ ≤ Bf) {E : Set Θ}
    (hE : MeasurableSet E) {δ ε : ℝ} (hδ : 0 ≤ δ) (hEε : m.real E ≤ ε)
    (hclose : ∀ᵐ θ ∂m, θ ∉ E → ‖A θ - A' θ‖ ≤ δ) :
    |kernelCov2 neumannH (m.map A, m.map A') (m.map A, m.map A')| ≤
      2 * (holderKα α CF Bf * δ ^ (α / 2) + 2 * potMaxα α CF Bf * ε) := by
  have hcl : IsClosed {y : ℂ | ‖y‖ ≤ Bf} := isClosed_le continuous_norm continuous_const
  have hB : ∀ᵐ y ∂(m.map A), ‖y‖ ≤ Bf := (ae_map_iff hA.aemeasurable hcl.measurableSet).2 hAb
  have hB' : ∀ᵐ y ∂(m.map A'), ‖y‖ ≤ Bf := (ae_map_iff hA'.aemeasurable hcl.measurableSet).2 hA'b
  have hm : (m.map A).real univ = 1 := by
    rw [measureReal_def, Measure.map_apply hA MeasurableSet.univ, preimage_univ, measure_univ,
      ENNReal.toReal_one]
  have hm' : (m.map A').real univ = 1 := by
    rw [measureReal_def, Measure.map_apply hA' MeasurableSet.univ, preimage_univ, measure_univ,
      ENNReal.toReal_one]
  have h1 := abs_integral_neuPot_map_sub_le hA hA' hα hα1 hF hCF hBf0 hB hm hAb hA'b hE hδ hEε hclose
  have h2 := abs_integral_neuPot_map_sub_le hA hA' hα hα1 hF' hCF hBf0 hB' hm' hAb hA'b hE hδ hEε hclose
  have e : kernelCov2 neumannH (m.map A, m.map A') (m.map A, m.map A') =
      (∫ θ, neuPot (m.map A) (A θ) ∂m - ∫ θ, neuPot (m.map A) (A' θ) ∂m) -
      (∫ θ, neuPot (m.map A') (A θ) ∂m - ∫ θ, neuPot (m.map A') (A' θ) ∂m) := by
    unfold kernelCov2
    simp only
    rw [kernelCov_map_eq hA, kernelCov_map_eq hA, kernelCov_map_eq hA', kernelCov_map_eq hA']
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

end A1RS
end R18
end QuantumZipper
