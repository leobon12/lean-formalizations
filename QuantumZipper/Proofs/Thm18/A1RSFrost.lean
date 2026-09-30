import QuantumZipper.Proofs.Thm18.A1RSStrip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (6): Frostman bounds through a chart that is injective off a small bad set

The energy moduli of the smeared-loop family `a1rfNu` (A1RFSmear.lean) need Frostman bounds for
its members that are uniform in all parameters, including the smoothing radius `ρ → 0`. Both
needed bounds have the same shape:

* the pushed side circle `μ_t = (f_t)_* ν₀` (`ν₀ = ψ_* fc(d, s)` is Frostman, `PushFrostmanα`):
  off the strip `{Im f_t ≤ τ}` the inverse `f_t⁻¹` is `M/τ`-Lipschitz (two-point upper bound
  `TwoPoint.norm_revMap_sub_mul_le_upper`), so points of `μ_t` in a small ball come from
  points of `ν₀` in a slightly larger ball;
* the smeared measure `ν_ρ = (f_t⁻¹ ∘ U)_*(μ_t ⊗ angMeas)`, `U = fold(z + ρ e^{iθ})`: off the strip
  `{Im U ≤ τ}` the map `f_t⁻¹` is injective with `‖u − v‖ ≤ (M/τ) ‖f_t⁻¹ u − f_t⁻¹ v‖`
  (`TwoPoint.twoPoint_lower`), so points of `ν_ρ` in a small ball come from values of `U` in a
  slightly larger ball, whose mass is controlled by the Frostman bound of `μ_t`.

`isFrostman_map_of_chart` is the common abstract step: if the law of a "chart" `X` has balls of
mass `≤ C_b r^γ`, the "bad" sets have mass `≤ C_s τ^β`, and `τ ‖X θ − X θ'‖ ≤ M ‖V θ − V θ'‖` off
the bad set of level `τ`, then the law of `V` is `min(β, γ)/2`-Frostman (take `τ = √r`). Own
elementary argument (the strip-splitting device of `TwoPoint.abs_integral_neuPot_coupling_le`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open TwoPoint

variable {Θ : Type*} [MeasurableSpace Θ] {m : Measure Θ} [IsProbabilityMeasure m]

/-- **Frostman bound for a law seen through a chart that is injective off a bad set.** -/
theorem isFrostman_map_of_chart {V X : Θ → ℂ} (hV : Measurable V) {bad : ℝ → Set Θ}
    {Cs β Cb γ M : ℝ} (hCs : 0 ≤ Cs) (hβ : 0 < β) (hCb : 0 ≤ Cb) (hγ : 0 < γ) (hM : 0 < M)
    (hbad : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → m.real (bad τ) ≤ Cs * τ ^ β)
    (hball : ∀ c : ℂ, ∀ r : ℝ, 0 < r → m.real {θ | X θ ∈ closedBall c r} ≤ Cb * r ^ γ)
    (hinj : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ θ θ' : Θ, θ ∉ bad τ → θ' ∉ bad τ →
      τ * ‖X θ - X θ'‖ ≤ M * ‖V θ - V θ'‖) :
    IsFrostman (m.map V) (min β γ / 2) (Cs + Cb * (2 * M) ^ γ + 1) := by
  intro x r hr
  set α := min β γ / 2 with hα
  have hα0 : 0 < α := by rw [hα]; exact half_pos (lt_min hβ hγ)
  have hK0 : 0 ≤ Cs + Cb * (2 * M) ^ γ := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * M) γ
    positivity
  rw [Measure.map_apply hV isClosed_closedBall.measurableSet]
  change m.real (V ⁻¹' closedBall x r) ≤ _
  rcases le_or_gt r 1 with hr1 | hr1
  · set τ := Real.sqrt r with hτ
    have hτ0 : 0 < τ := Real.sqrt_pos.2 hr
    have hτ1 : τ ≤ 1 := by rw [hτ]; exact Real.sqrt_le_one.2 hr1
    have hτpow : ∀ e : ℝ, τ ^ e = r ^ (e / 2) := fun e => by
      rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]; ring_nf
    set S := V ⁻¹' closedBall x r with hS
    have hsplit : m.real S ≤ m.real (bad τ) + m.real (S \ bad τ) := by
      refine (measureReal_mono (fun θ hθ => ?_)).trans (measureReal_union_le _ _)
      by_cases hb : θ ∈ bad τ
      · exact Or.inl hb
      · exact Or.inr ⟨hθ, hb⟩
    have h1 : m.real (bad τ) ≤ Cs * r ^ (β / 2) := by rw [← hτpow]; exact hbad τ hτ0 hτ1
    have h2 : m.real (S \ bad τ) ≤ Cb * (2 * M) ^ γ * r ^ (γ / 2) := by
      rcases (S \ bad τ).eq_empty_or_nonempty with he | ⟨θ₀, hθ₀S, hθ₀b⟩
      · rw [he, measureReal_empty]
        have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * M) γ
        have := Real.rpow_nonneg hr.le (γ / 2)
        positivity
      · have hsub : S \ bad τ ⊆ {θ | X θ ∈ closedBall (X θ₀) (2 * M * r / τ)} := by
          rintro θ ⟨hθS, hθb⟩
          have hi := hinj τ hτ0 hτ1 θ θ₀ hθb hθ₀b
          have hd : ‖V θ - V θ₀‖ ≤ 2 * r := by
            have a1 : dist (V θ) x ≤ r := hθS
            have a2 : dist (V θ₀) x ≤ r := hθ₀S
            rw [← dist_eq_norm]
            linarith [dist_triangle_right (V θ) (V θ₀) x]
          show dist (X θ) (X θ₀) ≤ 2 * M * r / τ
          rw [dist_eq_norm, le_div_iff₀ hτ0]
          nlinarith
        have hb := hball (X θ₀) (2 * M * r / τ) (by positivity)
        refine (measureReal_mono hsub).trans (hb.trans (le_of_eq ?_))
        rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (inv_nonneg.2 hτ0.le),
          Real.mul_rpow (by positivity) hr.le, Real.inv_rpow hτ0.le, hτpow]
        have hr2 : r ^ γ = r ^ (γ / 2) * r ^ (γ / 2) := by
          rw [← Real.rpow_add hr]; ring_nf
        have hpos : 0 < r ^ (γ / 2) := Real.rpow_pos_of_pos hr _
        rw [hr2]
        field_simp
    have hmono : ∀ e : ℝ, α ≤ e → r ^ e ≤ r ^ α := fun e he =>
      Real.rpow_le_rpow_of_exponent_ge hr hr1 he
    have e1 := hmono (β / 2) (by rw [hα]; linarith [min_le_left β γ])
    have e2 := hmono (γ / 2) (by rw [hα]; linarith [min_le_right β γ])
    have hrα : 0 ≤ r ^ α := Real.rpow_nonneg hr.le _
    have hCbM : 0 ≤ Cb * (2 * M) ^ γ :=
      mul_nonneg hCb (Real.rpow_nonneg (by linarith) _)
    have f1 := mul_le_mul_of_nonneg_left e1 hCs
    have f2 := mul_le_mul_of_nonneg_left e2 hCbM
    nlinarith
  · have h1 : m.real (V ⁻¹' closedBall x r) ≤ 1 := by
      have := measureReal_mono (μ := m) (subset_univ (V ⁻¹' closedBall x r))
      rwa [probReal_univ] at this
    have hr1' : 1 ≤ r ^ α := Real.one_le_rpow hr1.le hα0.le
    nlinarith

end A1RS
end R18
end QuantumZipper
