import QuantumZipper.Proofs.Thm18.G1SideDil
import QuantumZipper.Proofs.Thm18.G1RegRepScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (5): the offset identity for the pulled-back canonical field

For the pulled-back canonical field `x = coordChange (rescale w Q s) ψ Q` and the dilation-family
member `Z = coordChange w (z ↦ s ψ(a z)) Q`, the hypothesis of
`G1Side.integral_bdryR_offset_of_avg` at a point `t`,

  `evalReg x (fc(t, a 2^{-k})) = avgReg Z k (t/a) − Q log a`,

follows from three per-circle facts (`evalReg_offset_eq_avg_family`):
* RC3 of `x` at the circle `fc(t, a 2^{-k})` (regularized value = raw value),
* scale consistency of `w` at the pushed circle `ψ_* fc(t, a 2^{-k})` (`G1.ScaleConsistentAt`),
* exactness of `Z` at the dyadic circle `fc(t/a, 2^{-k})` (dyadic average = raw value),
plus nonvanishing and integrability of `log |ψ'|` on the circle. The rest is the chain rule
`(s ψ(a ·))' = s a ψ'(a ·)` and `(a ·)_* fc(t/a, r) = fc(t, a r)`. Coordinate-change rule (1.3) of
Sheffield, arXiv:1012.4797, for the composition with a dilation. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

theorem measurable_log_norm_deriv (ψ : ℂ → ℂ) :
    Measurable fun z => Real.log ‖deriv ψ z‖ :=
  Real.measurable_log.comp (measurable_deriv ψ).norm

/-- **The offset identity for the pulled-back canonical field.** -/
theorem evalReg_offset_eq_avg_family {γ : ℝ} {w : FieldSample} {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) {s a : ℝ} (hs : 0 < s) (ha : 0 < a) {k : ℕ} {t : ℝ}
    (hRC3 : evalReg (coordChange (rescale w (Qc γ) s) ψ (Qc γ))
        (foldedCircle (t : ℂ) (a * radius k)) =
      coordChange (rescale w (Qc γ) s) ψ (Qc γ) (foldedCircle (t : ℂ) (a * radius k)))
    (hsc : Thm18Asm.G1.ScaleConsistentAt w (Qc γ) s
      ((foldedCircle (t : ℂ) (a * radius k)).map ψ))
    (hd : ∀ᵐ z ∂foldedCircle (t : ℂ) (a * radius k), deriv ψ z ≠ 0)
    (hi : Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle (t : ℂ) (a * radius k)))
    (hex : avgReg (coordChange w (fun z => (s : ℂ) * ψ ((a : ℂ) * z)) (Qc γ)) k
        ((t / a : ℝ) : ℂ) =
      coordChange w (fun z => (s : ℂ) * ψ ((a : ℂ) * z)) (Qc γ)
        (foldedCircle ((t / a : ℝ) : ℂ) (radius k))) :
    evalReg (coordChange (rescale w (Qc γ) s) ψ (Qc γ)) (foldedCircle (t : ℂ) (a * radius k)) =
      avgReg (coordChange w (fun z => (s : ℂ) * ψ ((a : ℂ) * z)) (Qc γ)) k ((t / a : ℝ) : ℂ) -
        Qc γ * Real.log a := by
  have hmA : Measurable fun z : ℂ => (a : ℂ) * z := measurable_const_mul _
  have hfc : (foldedCircle ((t / a : ℝ) : ℂ) (radius k)).map (fun z => (a : ℂ) * z) =
      foldedCircle (t : ℂ) (a * radius k) := by
    rw [WedgeTK.fc_map_mul _ _ ha]
    congr 1
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
  rw [hRC3, Thm18Asm.G1Meas.coordChange_rescale_apply w hψm (Qc γ) hs _ hsc hd hi, hex]
  unfold coordChange
  -- the pushed measures agree
  have hmap : (foldedCircle ((t / a : ℝ) : ℂ) (radius k)).map
      (fun z => (s : ℂ) * ψ ((a : ℂ) * z)) =
      (foldedCircle (t : ℂ) (a * radius k)).map (fun z => (s : ℂ) * ψ z) := by
    have hsψ : Measurable fun z => (s : ℂ) * ψ z := measurable_const.mul hψm
    rw [← hfc, Measure.map_map hsψ hmA]
    rfl
  rw [hmap]
  -- the log-derivative terms
  have hd' : ∀ᵐ z ∂foldedCircle ((t / a : ℝ) : ℂ) (radius k), deriv ψ ((a : ℂ) * z) ≠ 0 := by
    rw [← hfc] at hd
    exact (ae_map_iff hmA.aemeasurable
      ((measurableSet_singleton 0).compl.preimage (measurable_deriv ψ))).1 hd
  have hlog : ∫ z, Real.log ‖deriv (fun z => (s : ℂ) * ψ ((a : ℂ) * z)) z‖
        ∂foldedCircle ((t / a : ℝ) : ℂ) (radius k) =
      Real.log s + Real.log a + ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle (t : ℂ) (a * radius k) := by
    have e : (fun z => Real.log ‖deriv (fun z => (s : ℂ) * ψ ((a : ℂ) * z)) z‖) =ᵐ[
        foldedCircle ((t / a : ℝ) : ℂ) (radius k)]
        fun z => Real.log s + Real.log a + Real.log ‖deriv ψ ((a : ℂ) * z)‖ := by
      filter_upwards [hd'] with z hz
      have h1 : deriv (fun z => (s : ℂ) * ψ ((a : ℂ) * z)) z =
          (s : ℂ) * deriv (fun z => ψ ((a : ℂ) * z)) z := by
        rw [deriv_const_mul_field']
      have h2 : deriv (fun z => ψ ((a : ℂ) * z)) z = (a : ℂ) • deriv ψ ((a : ℂ) * z) :=
        deriv_comp_mul_left (f := ψ) (c := (a : ℂ)) (x := z)
      rw [h1, h2, smul_eq_mul, norm_mul, norm_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs.le,
        Real.norm_of_nonneg ha.le, ← mul_assoc, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hz),
        Real.log_mul hs.ne' ha.ne']
    have hi' : Integrable (fun z => Real.log ‖deriv ψ ((a : ℂ) * z)‖)
        (foldedCircle ((t / a : ℝ) : ℂ) (radius k)) := by
      rw [← hfc] at hi
      exact (integrable_map_measure (measurable_log_norm_deriv ψ).aestronglyMeasurable
        hmA.aemeasurable).1 hi
    rw [integral_congr_ae e, integral_add (integrable_const _) hi', integral_const,
      probReal_univ, one_smul]
    congr 1
    rw [← hfc, integral_map hmA.aemeasurable
      (measurable_log_norm_deriv ψ).aestronglyMeasurable]
  rw [hlog, Thm18Asm.G1Meas.integral_log_deriv_const_mul hs hd hi]
  ring

end G1Side
end QuantumZipper
