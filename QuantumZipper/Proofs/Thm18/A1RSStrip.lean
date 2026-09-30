import QuantumZipper.Proofs.Thm18.A1RSMass
import QuantumZipper.Proofs.Thm18.A1RFSmear

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (5): the smoothed pushed side circle gives small mass to a strip along `ℝ`

The smeared loops of `a1rfNu` (A1RFSmear.lean) are the images under `f_t⁻¹` of the points
`U = fold(Z + ρ e^{iΘ})`, `Z ~ μ_t` (the pushed side circle), `Θ ~ angMeas`. Off the strip
`{Im U ≤ τ}` the map `f_t⁻¹` is Lipschitz with a constant polynomial in `1/τ`, so every energy
modulus of the family is paid for by the mass of that strip. This file bounds it, uniformly in
the smoothing radius `ρ ≥ 0`, from the mass bound `μ{Im ≤ δ} ≤ C δ^{1/2}`
(`a1rMu_strip_le_unif`, A1RSMass.lean):

`(μ ⊗ angMeas){(z, θ) : Im fold(z + ρ e^{iθ}) ≤ τ} ≤ (2C + 2) τ^{1/4}`, `0 < τ ≤ 1`
(`prod_strip_le`).

Two regimes: for `ρ ≤ √τ` only centres with `Im z ≤ τ + ρ ≤ 2√τ` contribute (mass bound); for
`ρ > √τ` each circle gives the strip mass `≤ (3/2) √(τ/ρ) ≤ (3/2) τ^{1/4}`
(`A1R.foldedCircle_strip_le`, from `RTBeur.circleUnif_strip_le`). Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

/-- The strip set in the parameters `(z, θ)` of the smoothing circles. -/
def stripPar (ρ τ : ℝ) : Set (ℂ × ℝ) := {p | (foldH (circleMap p.1 ρ p.2)).im ≤ τ}

theorem measurableSet_stripPar (ρ τ : ℝ) : MeasurableSet (stripPar ρ τ) := by
  have hc : Continuous fun p : ℂ × ℝ => (foldH (circleMap p.1 ρ p.2)).im := by
    have : (fun p : ℂ × ℝ => (foldH (circleMap p.1 ρ p.2)).im) =
        fun p : ℂ × ℝ => |(circleMap p.1 ρ p.2).im| := by
      funext p; exact TwoPoint.im_foldH _
    rw [this]
    refine (Complex.continuous_im.comp ?_).abs
    unfold circleMap
    fun_prop
  exact measurableSet_le hc.measurable measurable_const

/-- The slice of the strip set over one circle is the strip mass of that folded circle. -/
theorem angMeas_slice_stripPar (z : ℂ) (ρ τ : ℝ) :
    E6.XAreaPC.angMeas (Prod.mk z ⁻¹' stripPar ρ τ) =
      foldedCircle z ρ {u : ℂ | |u.im| ≤ τ} := by
  have hG : MeasurableSet {u : ℂ | |u.im| ≤ τ} :=
    measurableSet_le (Complex.continuous_im.abs.measurable) measurable_const
  rw [E6.XAreaPC.foldedCircle_eq_map_angMeas,
    Measure.map_apply (show Measurable (fun θ => foldH (circleMap z ρ θ)) from
      measurable_foldH.comp (measurable_circleMap z ρ)) hG]
  congr 1
  ext θ
  simp only [stripPar, mem_preimage, mem_setOf_eq, TwoPoint.im_foldH, abs_abs]

/-- **Strip bound for the smoothed measure**, uniformly in the smoothing radius. -/
theorem prod_strip_le {μ : Measure ℂ} [IsProbabilityMeasure μ] (hH : ∀ᵐ z ∂μ, 0 ≤ z.im)
    {C : ℝ} (hC : 0 ≤ C) (hmass : ∀ δ : ℝ, 0 < δ → μ.real {z : ℂ | z.im ≤ δ} ≤ C * δ ^ (1 / 2 : ℝ))
    {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (μ.prod E6.XAreaPC.angMeas).real (stripPar ρ τ) ≤ (2 * C + 2) * τ ^ (1 / 4 : ℝ) := by
  have hq : 0 ≤ τ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hτ.le _
  have hsq : Real.sqrt τ = τ ^ (1 / 4 : ℝ) * τ ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hτ, Real.sqrt_eq_rpow]; norm_num
  have hS := measurableSet_stripPar ρ τ
  have hprod := Measure.prod_apply (μ := μ) (ν := E6.XAreaPC.angMeas) hS
  rcases le_or_gt ρ (Real.sqrt τ) with hsm | hbig
  · -- small smoothing radius: only low centres contribute
    have hslice : ∀ᵐ z ∂μ, E6.XAreaPC.angMeas (Prod.mk z ⁻¹' stripPar ρ τ) ≤
        {z : ℂ | z.im ≤ τ + ρ}.indicator 1 z := by
      filter_upwards [hH] with z hz
      by_cases hlow : z.im ≤ τ + ρ
      · rw [indicator_of_mem (show z ∈ {z : ℂ | z.im ≤ τ + ρ} from hlow)]
        exact prob_le_one
      · rw [indicator_of_notMem (show z ∉ {z : ℂ | z.im ≤ τ + ρ} from hlow)]
        refine le_of_eq (measure_eq_zero_iff_ae_notMem.2 (Eventually.of_forall fun θ hθ => ?_))
        simp only [stripPar, mem_preimage, mem_setOf_eq, TwoPoint.im_foldH,
          RTBeur.circleMap_im_eq] at hθ
        have hs := Real.neg_one_le_sin θ
        have h1 : ρ * (-1) ≤ ρ * Real.sin θ := mul_le_mul_of_nonneg_left hs hρ
        rw [abs_le] at hθ
        push Not at hlow
        linarith [hθ.2]
    have hle : (μ.prod E6.XAreaPC.angMeas) (stripPar ρ τ) ≤ μ {z : ℂ | z.im ≤ τ + ρ} := by
      rw [hprod]
      refine (lintegral_mono_ae hslice).trans (le_of_eq ?_)
      exact lintegral_indicator_one
        (measurableSet_le Complex.continuous_im.measurable measurable_const)
    have hreal : (μ.prod E6.XAreaPC.angMeas).real (stripPar ρ τ) ≤ μ.real {z : ℂ | z.im ≤ τ + ρ} :=
      ENNReal.toReal_mono (measure_ne_top _ _) hle
    refine hreal.trans ((hmass _ (by linarith)).trans ?_)
    -- `(τ + ρ)^{1/2} ≤ (2√τ)^{1/2} ≤ 2 τ^{1/4}`
    have hst : τ ≤ Real.sqrt τ := by
      rw [Real.le_sqrt hτ.le hτ.le]; nlinarith
    have h1 : (τ + ρ) ^ (1 / 2 : ℝ) ≤ (2 * Real.sqrt τ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have h2 : (2 * Real.sqrt τ) ^ (1 / 2 : ℝ) ≤ 2 * τ ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hτ.le]
      have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      norm_num
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hC
    nlinarith
  · -- large smoothing radius: each circle gives a small strip mass
    have hρ0 : 0 < ρ := lt_of_le_of_lt (Real.sqrt_nonneg _) hbig
    have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
    have h1 : τ / ρ ≤ Real.sqrt τ := by
      rw [div_le_iff₀ hρ0]
      have := Real.mul_self_sqrt hτ.le
      nlinarith [mul_lt_mul_of_pos_left hbig hsτ]
    have h2 : Real.sqrt (Real.sqrt τ) = τ ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hτ.le]; norm_num
    have hbound : Real.sqrt (τ / ρ) ≤ τ ^ (1 / 4 : ℝ) := (Real.sqrt_le_sqrt h1).trans h2.le
    have hslice : ∀ z : ℂ, E6.XAreaPC.angMeas (Prod.mk z ⁻¹' stripPar ρ τ) ≤
        ENNReal.ofReal (3 / 2 * Real.sqrt (τ / ρ)) := fun z => by
      rw [angMeas_slice_stripPar]
      exact A1R.foldedCircle_strip_le z hρ0 hτ.le
    have hle : (μ.prod E6.XAreaPC.angMeas) (stripPar ρ τ) ≤
        ENNReal.ofReal (3 / 2 * Real.sqrt (τ / ρ)) := by
      rw [hprod]
      refine (lintegral_mono fun z => hslice z).trans (le_of_eq ?_)
      rw [lintegral_const, measure_univ, mul_one]
    have hreal : (μ.prod E6.XAreaPC.angMeas).real (stripPar ρ τ) ≤ 3 / 2 * Real.sqrt (τ / ρ) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hle
    nlinarith

end A1RS
end R18
end QuantumZipper
