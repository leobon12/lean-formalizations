import MatedCRTHarmonic.IGLaw.ORotLaw
import MatedCRTHarmonic.LQGCoord.WPCirc

/-!
# The dilated IG input is not a shift of the IG input in law (counterexample)

The bundle's imaginary-geometry map `Φ` reads the **full** circle-average process
`H = circleAvg hIG₀ + U : ℝ → ℂ → ℝ`, including the radius `0`, where `circleAvg h 0 w` is the junk limit of
the mollified point values: a.s. `H(0, w) = limJunk + U` at every fixed `w` (`ODiverge`). The dilated input
`igPullback γ 0 s 0 H = H(s ·, s ·)` keeps that slice, `H(0, 0)`, but its positive radii see the field at the new
scale. So the coordinate functional `junkGap K = K(0,0) − K(1,0)` is

* a.s. equal to the constant `limJunk` for every constant shift `H + k` (`junkGap_addIn`), but
* a.s. equal to `limJunk − circleAvg hIG₀ s 0` for the dilated input, which has no atoms when `s ≠ 1`
  (a centred Gaussian of variance `|log s|`, the `hasLaw_cInc_same`).

Hence `law(igPullback γ 0 s 0 H) ≠ law(H + k)` for **every** random shift `k`
(`map_igPullback_dilation_ne_shift`); in particular the input-law identity
`P.map (igPullback γ 0 s 0 ∘ H) = P.map H` that `IGLaw.map_eq_of_coordinate_change` (and the adapter
`igcFixedAffineRerootInvariant_of_coordinateChange`) would need is false for `s ≠ 1`
(`IsMatingOfTreesCoupling.map_igPullback_dilation_ne_input`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MatedCRTHarmonic.IGLaw

open LQGMetric MatedCRTHarmonic.MatedCRT

/-- The radius-`0` slice against the unit circle: `K ↦ K(0, 0) − K(1, 0)`. -/
def junkGap (K : ℝ → ℂ → ℝ) : ℝ := K 0 0 - K 1 0

lemma measurable_junkGap : Measurable junkGap := by
  have h0 : Measurable fun K : ℝ → ℂ → ℝ => K 0 0 :=
    (measurable_pi_apply (0 : ℂ)).comp (measurable_pi_apply (0 : ℝ))
  have h1 : Measurable fun K : ℝ → ℂ → ℝ => K 1 0 :=
    (measurable_pi_apply (0 : ℂ)).comp (measurable_pi_apply (1 : ℝ))
  exact h0.sub h1

lemma junkGap_addIn (c : ℝ) (K : ℝ → ℂ → ℝ) : junkGap (addIn c K) = junkGap K := by
  simp only [junkGap, addIn]
  ring

lemma measurable_igPullback (γ : ℝ) (z₀ : ℂ) (s φ : ℝ) : Measurable (igPullback γ z₀ s φ) :=
  measurable_pi_iff.2 fun ρ => measurable_pi_iff.2 fun w => by
    show Measurable fun K : ℝ → ℂ → ℝ =>
      K (s * ρ) (z₀ + (s : ℂ) * Complex.exp (φ * Complex.I) * w) - igChi γ * φ
    have h1 : Measurable fun K : ℝ → ℂ → ℝ => K (s * ρ) := measurable_pi_apply (s * ρ)
    have h2 : Measurable fun f : ℂ → ℝ => f (z₀ + (s : ℂ) * Complex.exp (φ * Complex.I) * w) :=
      measurable_pi_apply _
    exact (h2.comp h1).sub_const _

lemma junkGap_igPullback_dilation (γ s : ℝ) (K : ℝ → ℂ → ℝ) :
    junkGap (igPullback γ 0 s 0 K) = K 0 0 - K s 0 := by
  simp [junkGap, igPullback]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field}

/-- For a normalized whole-plane GFF and `s ≠ 1`, the circle average `h_s(0)` has no atoms. -/
theorem measure_circleAvg_eq (hh : IsNormalizedWPGFF h P) {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1)
    (x : ℝ) : P {ω | circleAvg (h ω) s 0 = x} = 0 := by
  rcases lt_or_gt_of_ne hs1 with hlt | hgt
  · -- `s < 1`: `h_s(0) = h_s(0) − h_1(0)` has law `N(0, log (1/s))`
    have hL := MatedCRTHarmonic.LQGCoord.hasLaw_cInc_same hh.1 (z := 0) hs hlt.le
    have hv : (Real.log (1 / s)).toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]
      exact Real.log_pos (by rw [lt_div_iff₀ hs]; linarith)
    have hnull := nullSingletonClass_gaussianReal (μ := 0) hv
    have hset : {ω | circleAvg (h ω) s 0 = x} =ᵐ[P]
        (CircleAvg.cInc h s 0 1 0) ⁻¹' {x} := by
      filter_upwards [hh.2] with ω hω
      change (circleAvg (h ω) s 0 = x) = (circleAvg (h ω) s 0 - circleAvg (h ω) 1 0 = x)
      rw [hω, sub_zero]
    rw [measure_congr hset, ← Measure.map_apply_of_aemeasurable hL.aemeasurable
      (measurableSet_singleton x), hL.map_eq]
    exact measure_singleton x
  · -- `s > 1`: `−h_s(0) = h_1(0) − h_s(0)` has law `N(0, log s)`
    have hL := MatedCRTHarmonic.LQGCoord.hasLaw_cInc_same hh.1 (z := 0) one_pos hgt.le
    have hv : (Real.log (s / 1)).toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le, div_one]
      exact Real.log_pos hgt
    have hnull := nullSingletonClass_gaussianReal (μ := 0) hv
    have hset : {ω | circleAvg (h ω) s 0 = x} =ᵐ[P]
        (CircleAvg.cInc h 1 0 s 0) ⁻¹' {-x} := by
      filter_upwards [hh.2] with ω hω
      change (circleAvg (h ω) s 0 = x) = (circleAvg (h ω) 1 0 - circleAvg (h ω) s 0 = -x)
      rw [hω, zero_sub, neg_inj]
    rw [measure_congr hset, ← Measure.map_apply_of_aemeasurable hL.aemeasurable
      (measurableSet_singleton _), hL.map_eq]
    exact measure_singleton _

end MatedCRTHarmonic.IGLaw
