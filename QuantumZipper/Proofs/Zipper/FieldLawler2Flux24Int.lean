import QuantumZipper.Proofs.Zipper.FieldLawler2Flux24
import QuantumZipper.Proofs.Zipper.FieldLawler2Radial

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 2: FL (2.4) in flux form, `ℰ(C_R, ·) ≤ c ε/R`

Field–Lawler, EJP 20 (2015), p. 6, (2.3)–(2.4): the excursion flux through `C_R` (from inside) of
a harmonic measure of `C_ε`-arcs in a subdomain of the half-annulus is `≤ c ε/R`. From the
pointwise majorant `fl2_outer_majorant` (`w ≤ M := 32π ε Im z (|z|⁻² − R⁻²)` near `C_R`), the
flux comparison `fl2_fluxR_le_of_majorant`, and `∂ᵣ⁻ M(Re^{iθ}) = 64π ε sin θ / R²`.
Own elementary computation.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.Thm18Asm.LWFar

theorem fl2Pt_im (R θ s : ℝ) : (fl2Pt R θ s).im = (R - s) * Real.sin θ := by
  simp [fl2Pt, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.mul_im]

theorem fl2Pt_norm {R θ s : ℝ} (hs : s ≤ R) : ‖fl2Pt R θ s‖ = R - s := by
  rw [fl2Pt, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- The radial derivative of the majorant. -/
theorem fl2_maj_rDer_tendsto {ε R θ : ℝ} (hR : 0 < R) :
    Tendsto (fun s : ℝ => (32 * π * ε * (fl2Pt R θ s).im *
      (1 / ‖fl2Pt R θ s‖ ^ 2 - 1 / R ^ 2)) / s) (𝓝[>] 0)
      (𝓝 (32 * π * ε * Real.sin θ * (2 * R - 0) / ((R - 0) * R ^ 2))) := by
  have hc : ContinuousAt (fun s : ℝ => 32 * π * ε * Real.sin θ * (2 * R - s) / ((R - s) * R ^ 2))
      0 := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simp only [sub_zero]; positivity
  refine (tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < R by linarith)] with s hs
  rw [fl2Pt_im, fl2Pt_norm hs.2.le]
  have h1 : R - s ≠ 0 := by linarith [hs.2]
  have h2 : s ≠ 0 := hs.1.ne'
  field_simp
  ring

end FieldLawler
end QuantumZipper
