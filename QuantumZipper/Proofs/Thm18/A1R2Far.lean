import QuantumZipper.Proofs.Thm18.A1R2Growth
import QuantumZipper.Proofs.Thm18.A1RMass
import QuantumZipper.Proofs.GFF.CoordRegHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1R2 (far): `A1RFarStmt` from its random part

Decision D90. Above height `√ρ` (with `ρ < 1`), the smoothing circle `fc(z, ρ)` lies inside `ℍ`.
By RC3 of the unzipped field at every time (`R18.a1r2_ae_exactAll`) its witness there is
`F_t(z, ρ) = evalReg Y ((f_t⁻¹)_* fc(z, ρ)) + Q ∫ log |(f_t⁻¹)'| dfc(z, ρ)`.
`log |(f_t⁻¹)'|` is harmonic on `ℍ`, so the last integral is `log |(f_t⁻¹)'(z)|` (Jensen's formula
for zero-free functions, `CoordReg.integral_log_norm_circleUnif_of_analytic`). Its integral over
the far part of `μ = (f_t ∘ ψ)_* fc(d, s)` converges to `∫ log |(f_t⁻¹)'| dμ` by dominated
convergence: the bound `2 |log Im| + const` comes from A1R2LogD, and `|log Im|` is `μ`-integrable
by the Schwarz–Pick lower bound `Im (f_t ψ(u)) ≥ c Im u` (A1RPick).

What remains is the random part:
* `A1R2FarYStmt` (open): the far-part smoothings `∫_{Im z > √ρ} evalReg Y ((f_t⁻¹)_* fc(z, ρ)) dμ(z)`
  converge to `evalReg Y ((f_t⁻¹)_* μ) = evalReg Y (ψ_* fc(d, s))`. This is the continuum limit of
  the pairings of `Y` along the pushed side circle, smoothed by pulled-back circles that stay
  inside `ℍ ∖ η` (Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1).
* **`a1rFarStmt_of_farY : A1R2FarYStmt → A1RFarStmt`**.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

namespace A1R2

variable {W : ℝ → ℝ}

instance isFiniteMeasure_a1rMu (W : ℝ → ℝ) (t : ℝ) (left : Bool) (d : ℂ) (s : ℝ) :
    IsFiniteMeasure (a1rMu W t left d s) := by
  unfold a1rMu; infer_instance

/-- Mean value property of `log |(f_t⁻¹)'|` on circles inside `ℍ`. -/
theorem integral_log_deriv_fc_eq (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρz : ρ < z.im) :
    ∫ u, Real.log ‖deriv (fwdMapInv W t) u‖ ∂foldedCircle z ρ =
      Real.log ‖deriv (fwdMapInv W t) z‖ := by
  rw [SmoothConv.foldedCircle_eq_circleUnif_sc hρ.le hρz.le]
  have hsub : closedBall z ρ ⊆ H := by
    intro w hw
    show 0 < w.im
    have h1 : |w.im - z.im| ≤ ρ := by
      have := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im] at this
      exact this.trans (by rw [← dist_eq_norm]; exact hw)
    linarith [(abs_le.1 h1).1]
  have hd : DifferentiableOn ℂ (fwdMapInv W t) H := fun u hu =>
    (RS.differentiableAt_fwdMapInv hW hW0 ht hu).differentiableWithinAt
  have hA : AnalyticOnNhd ℂ (deriv (fwdMapInv W t)) H := (hd.analyticOnNhd isOpen_H).deriv
  refine CoordReg.integral_log_norm_circleUnif_of_analytic (measurable_deriv _) hρ.le
    (hA.mono hsub) fun u hu => ?_
  have huH := hsub hu
  have h1 := le_norm_deriv_fwdMapInv hW hW0 ht huH
  have h2 : 0 < u.im / (fwdMapInv W t u).im :=
    div_pos huH (RS.fwdMapInv_mem_H hW hW0 ht huH)
  exact norm_pos_iff.1 (lt_of_lt_of_le h2 h1)

/-- The pushed side circles live in `ℍ`, a.e. -/
theorem ae_mem_H_a1rMu (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) (left : Bool) (d : ℂ) {s : ℝ}
    (hs : 0 < s) : ∀ᵐ z ∂a1rMu W t left d s, z ∈ H := by
  obtain ⟨-, hmaps, g, hgm, hEq⟩ := A1R.sidePush_props hG ht left
  have hmapeq : a1rMu W t left d s = (foldedCircle d s).map g := by
    unfold a1rMu
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
    exact hEq hu
  rw [hmapeq]
  refine (ae_map_iff hgm.aemeasurable isOpen_H.measurableSet).2 ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
  rw [← hEq hu]
  exact hmaps hu

/-- `|log Im|` is integrable along the pushed side circles (Schwarz–Pick). -/
theorem integrable_abs_log_im_a1rMu (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) (left : Bool)
    (d : ℂ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun z : ℂ => |Real.log z.im|) (a1rMu W t left d s) := by
  obtain ⟨hdiff, hmaps, g, hgm, hEq⟩ := A1R.sidePush_props hG ht left
  set Φ : ℂ → ℂ := fun w => fwdMap W t (g1zSideMap left W w) with hΦ
  obtain ⟨Rr, hsupp⟩ := A1R.exists_ae_bdd_a1rMu hG ht left d hs
  have hmapeq : a1rMu W t left d s = (foldedCircle d s).map g := by
    unfold a1rMu
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
    exact hEq hu
  have hmeas : Measurable fun z : ℂ => |Real.log z.im| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)
  rw [hmapeq]
  refine (integrable_map_measure hmeas.aestronglyMeasurable hgm.aemeasurable).2 ?_
  -- the Schwarz–Pick constant on the bounded support of the folded circle
  set R := ‖d‖ + s with hR
  have hIH : Complex.I ∈ H := by show 0 < Complex.I.im; simp
  have hp : 0 < (Φ Complex.I).im := hmaps hIH
  set c := (Φ Complex.I).im / (R + 1) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hsupp' : ∀ᵐ u ∂foldedCircle d s, ‖g u‖ ≤ Rr := by
    have := (ae_map_iff hgm.aemeasurable (measurableSet_le measurable_norm measurable_const)).1
      (by rw [← hmapeq]; exact hsupp.mono fun z hz => hz.2)
    exact this
  have hb : ∀ᵐ u ∂foldedCircle d s,
      |Real.log (g u).im| ≤ |Real.log u.im| + |Real.log c| + |Real.log (Rr + 1)| := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs, TwoPoint.foldedCircle_ae_norm_le d hs.le,
      hsupp'] with u hu hun hgR
    have hu' : 0 < u.im := hu
    have hgu : g u = Φ u := (hEq hu).symm
    have hlow : c * u.im ≤ (Φ u).im := by
      have h1 := A1R.im_ge_of_mapsTo_H hdiff hmaps hu
      have huI : ‖u + Complex.I‖ ≤ R + 1 := by
        calc ‖u + Complex.I‖ ≤ ‖u‖ + ‖Complex.I‖ := norm_add_le _ _
          _ ≤ R + 1 := by rw [Complex.norm_I]; linarith
      have huI0 : 0 < ‖u + Complex.I‖ := by
        refine norm_pos_iff.2 fun h => ?_
        have := congrArg Complex.im h
        simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
        linarith
      refine le_trans ?_ h1
      rw [hc, div_mul_eq_mul_div, mul_comm ((Φ Complex.I).im) u.im]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ huI0.le huI 2)
    have hpos : 0 < (Φ u).im := hmaps hu
    have hup : (Φ u).im ≤ Rr + 1 := by
      have := Complex.im_le_norm (Φ u)
      rw [← hgu] at this ⊢
      linarith
    rw [hgu]
    rcases le_or_gt (Φ u).im 1 with h1 | h1
    · rw [abs_of_nonpos (Real.log_nonpos hpos.le h1)]
      have h2 := Real.log_le_log (mul_pos hc0 hu') hlow
      rw [Real.log_mul hc0.ne' hu'.ne'] at h2
      linarith [neg_abs_le (Real.log c), neg_abs_le (Real.log u.im),
        abs_nonneg (Real.log (Rr + 1))]
    · rw [abs_of_pos (Real.log_pos h1)]
      have h2 := Real.log_le_log hpos hup
      linarith [le_abs_self (Real.log (Rr + 1)), abs_nonneg (Real.log c),
        abs_nonneg (Real.log u.im)]
  refine Integrable.mono' (((TwoPoint.integrable_log_im_foldedCircle d hs).abs.add
    (integrable_const |Real.log c|)).add (integrable_const |Real.log (Rr + 1)|)) ?_ ?_
  · exact (hmeas.comp_aemeasurable hgm.aemeasurable).aestronglyMeasurable
  · filter_upwards [hb] with u hu
    simp only [comp_apply, Real.norm_eq_abs, abs_abs, Pi.add_apply]
    linarith

/-- `log |(f_t⁻¹)'|` is integrable along the pushed side circles. -/
theorem integrable_log_deriv_a1rMu (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) (left : Bool)
    (d : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ L : ℝ, Integrable (fun z : ℂ => Real.log ‖deriv (fwdMapInv W t) z‖)
      (a1rMu W t left d s) ∧ ∀ᵐ z ∂a1rMu W t left d s,
        |Real.log ‖deriv (fwdMapInv W t) z‖| ≤ 2 * |Real.log z.im| + L := by
  obtain ⟨C, hC⟩ := G1ZA1a.exists_bound_fwdMapInv hG ht
  obtain ⟨Rr, hsupp⟩ := A1R.exists_ae_bdd_a1rMu hG ht left d hs
  have hWc := hG.1
  have hW0 := hG.2.1
  have hint := integrable_abs_log_im_a1rMu hG ht left d hs
  have hb : ∀ᵐ z ∂a1rMu W t left d s,
      |Real.log ‖deriv (fwdMapInv W t) z‖| ≤ 2 * |Real.log z.im| + |Real.log (Rr + C + 1)| := by
    filter_upwards [hsupp, ae_mem_H_a1rMu hG ht left d hs] with z hz hzH
    exact abs_log_norm_deriv_fwdMapInv_le hWc hW0 ht.le hC hzH hz.2
  refine ⟨_, Integrable.mono' ((hint.const_mul 2).add
    (integrable_const |Real.log (Rr + C + 1)|)) ?_ ?_, hb⟩
  · exact (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable
  · filter_upwards [hb] with z hz
    simpa [Real.norm_eq_abs] using hz

end A1R2

end R18
end QuantumZipper
