import QuantumZipper.Proofs.Zipper.FieldLawler2Semi
import QuantumZipper.Proofs.Thm18.LWHarmConf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 3: excursion between two real intervals in `ℍ` (explicit, symmetric)

Base case of the symmetry `ℰ(V, W) = ℰ(W, V)` of Brownian excursion measure (Field–Lawler,
EJP 20 (2015), §2, p. 5: "the measure is symmetric"; Lawler, *Conformally Invariant Processes in
the Plane*, §5.2): in `ℍ`, the harmonic measure of `(c, d)` is `π⁻¹ Im log((p − d)/(p − c))`, its
vertical derivative at `x ∉ [c, d]` is `(d − c)/(π (x − c)(x − d))`, and the flux into `(a, b)`
(`a < b < c < d`) is `π⁻¹ log((c − a)(d − b)/((c − b)(d − a)))`, symmetric in the two intervals.
Own elementary computation.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- `log ((p − d)/(p − c))`; its imaginary part is `π ×` the harmonic measure of `(c, d)`. -/
def fl3IntF (c d : ℝ) (p : ℂ) : ℂ := Complex.log ((p - d) / (p - c))

/-- The harmonic measure of the interval `(c, d)` in `ℍ`. -/
def fl3IntHarm (c d : ℝ) (p : ℂ) : ℝ := (fl3IntF c d p).im / π

/-- Derivative of `fl3IntF` at a real point outside `[c, d]`. -/
theorem fl3_hasDerivAt_F {c d x : ℝ} (hcd : c < d) (hx : x < c ∨ d < x) :
    HasDerivAt (fl3IntF c d) (((d - c) / ((x - c) * (x - d)) : ℝ) : ℂ) (x : ℂ) := by
  have hxc : (x : ℂ) - c ≠ 0 := by
    rw [← ofReal_sub, ofReal_ne_zero, sub_ne_zero]
    rcases hx with h | h <;> [exact h.ne; exact (hcd.trans h).ne']
  have hxd : (x : ℂ) - d ≠ 0 := by
    rw [← ofReal_sub, ofReal_ne_zero, sub_ne_zero]
    rcases hx with h | h <;> [exact (h.trans hcd).ne; exact h.ne']
  have hpos : 0 < (x - d) / (x - c) := by
    rcases hx with h | h
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact div_pos (by linarith) (by linarith)
  have hg : HasDerivAt (fun p : ℂ => (p - d) / (p - c))
      ((1 * ((x : ℂ) - c) - ((x : ℂ) - d) * 1) / ((x : ℂ) - c) ^ 2) (x : ℂ) :=
    ((hasDerivAt_id _).sub_const _).div ((hasDerivAt_id _).sub_const _) hxc
  have hmem : ((x : ℂ) - d) / ((x : ℂ) - c) ∈ slitPlane := by
    rw [← ofReal_sub, ← ofReal_sub, ← ofReal_div]
    exact ofReal_mem_slitPlane.2 hpos
  have hl := hg.clog hmem
  have he : (((d - c) / ((x - c) * (x - d)) : ℝ) : ℂ) =
      (1 * ((x : ℂ) - c) - ((x : ℂ) - d) * 1) / ((x : ℂ) - c) ^ 2 /
        (((x : ℂ) - d) / ((x : ℂ) - c)) := by
    push_cast
    field_simp
    ring
  rw [he]
  exact hl

/-- **Vertical derivative of the interval harmonic measure** at a real point outside `[c, d]`. -/
theorem fl3_yDer_intHarm {c d x : ℝ} (hcd : c < d) (hx : x < c ∨ d < x) :
    yDer (fl3IntHarm c d) x = (d - c) / (π * ((x - c) * (x - d))) := by
  have hF := fl3_hasDerivAt_F hcd hx
  have hL : HasFDerivAt (fl3IntHarm c d)
      ((π⁻¹ : ℝ) • (Complex.imCLM.comp
        ((ContinuousLinearMap.toSpanSingleton ℂ
          (((d - c) / ((x - c) * (x - d)) : ℝ) : ℂ)).restrictScalars ℝ))) (x : ℂ) := by
    have h1 := (Complex.imCLM.hasFDerivAt.comp (x : ℂ) (hF.hasFDerivAt.restrictScalars ℝ))
    have h2 := h1.const_smul (π⁻¹ : ℝ)
    have hfe : fl3IntHarm c d = (π⁻¹ : ℝ) • (⇑Complex.imCLM ∘ fl3IntF c d) := by
      funext p
      simp [fl3IntHarm, div_eq_inv_mul, smul_eq_mul]
    rw [hfe]
    exact h2
  have h0 : fl3IntHarm c d (x : ℂ) = 0 := by
    have hpos : 0 < (x - d) / (x - c) := by
      rcases hx with h | h
      · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
      · exact div_pos (by linarith) (by linarith)
    simp only [fl3IntHarm, fl3IntF]
    rw [← ofReal_sub, ← ofReal_sub, ← ofReal_div, ← Complex.ofReal_log hpos.le, ofReal_im,
      zero_div]
  rw [lwHarm_yDer_of_hasFDerivAt hL h0]
  have hre : (I * (((d - c) / ((x - c) * (x - d)) : ℝ) : ℂ)).im = (d - c) / ((x - c) * (x - d)) := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.imCLM_apply, smul_eq_mul]
  rw [hre]
  field_simp

/-- `excR` over `(p, q)` of a function whose vertical derivative is a continuous nonnegative `f`
with antiderivative `F`. -/
theorem fl3_excR_eq_of_deriv {h : ℂ → ℝ} {p q : ℝ} (hpq : p < q) {f F : ℝ → ℝ}
    (hy : ∀ x ∈ Icc p q, yDer h x = f x) (hf0 : ∀ x ∈ Icc p q, 0 ≤ f x)
    (hfc : ContinuousOn f (Icc p q)) (hF : ∀ x ∈ Icc p q, HasDerivAt F (f x) x) :
    excR h (Ioo p q) = ENNReal.ofReal (F q - F p) := by
  unfold excR
  have h1 : ∫⁻ x in Ioo p q, ENNReal.ofReal (yDer h x) = ∫⁻ x in Ioo p q, ENNReal.ofReal (f x) :=
    setLIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [hy x (Ioo_subset_Icc_self hx)]
  rw [h1]
  have hint : IntegrableOn f (Ioo p q) :=
    (hfc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx =>
      hf0 x (Ioo_subset_Icc_self hx)))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpq.le]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
  · rw [uIcc_of_le hpq.le] at hx
    exact hF x hx
  · exact (hfc.mono (by rw [uIcc_of_le hpq.le])).intervalIntegrable

/-- **Flux into `(a, b)` of the harmonic measure of `(c, d)`** (`a < b < c < d`). -/
theorem fl3_excR_left {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    excR (fl3IntHarm c d) (Ioo a b) = ENNReal.ofReal
      ((Real.log (d - b) - Real.log (c - b) - (Real.log (d - a) - Real.log (c - a))) / π) := by
  have hmem : ∀ x ∈ Icc a b, x < c := fun x hx => lt_of_le_of_lt hx.2 hbc
  rw [show (Real.log (d - b) - Real.log (c - b) - (Real.log (d - a) - Real.log (c - a))) / π =
    (Real.log (d - b) - Real.log (c - b)) / π - (Real.log (d - a) - Real.log (c - a)) / π by ring]
  refine fl3_excR_eq_of_deriv hab (f := fun x => (d - c) / (π * ((x - c) * (x - d))))
    (F := fun x => (Real.log (d - x) - Real.log (c - x)) / π)
    (fun x hx => fl3_yDer_intHarm hcd (Or.inl (hmem x hx))) (fun x hx => ?_) ?_ (fun x hx => ?_)
  · have h1 : x - c < 0 := by linarith [hmem x hx]
    have h2 : x - d < 0 := by linarith [hmem x hx]
    have := Real.pi_pos
    exact div_nonneg (by linarith) (mul_nonneg this.le (mul_nonneg_of_nonpos_of_nonpos h1.le h2.le))
  · refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
    have h1 : x - c < 0 := by linarith [hmem x hx]
    have h2 : x - d < 0 := by linarith [hmem x hx]
    exact mul_ne_zero Real.pi_pos.ne' (mul_pos_of_neg_of_neg h1 h2).ne'
  · have h1 : 0 < c - x := by linarith [hmem x hx]
    have h2 : 0 < d - x := by linarith [hmem x hx]
    have hd := (((hasDerivAt_id x).const_sub d).log h2.ne').sub
      (((hasDerivAt_id x).const_sub c).log h1.ne')
    have hd3 : HasDerivAt (fun x => (Real.log (d - x) - Real.log (c - x)) / π)
        ((-1 / (d - x) - -1 / (c - x)) / π) x := hd.div_const π
    refine hd3.congr_deriv ?_
    have e1 : d - x ≠ 0 := h2.ne'
    have e2 : c - x ≠ 0 := h1.ne'
    have e3 : x - c ≠ 0 := by linarith
    have e4 : x - d ≠ 0 := by linarith
    field_simp
    ring

/-- **Flux into `(c, d)` of the harmonic measure of `(a, b)`** (`a < b < c < d`). -/
theorem fl3_excR_right {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    excR (fl3IntHarm a b) (Ioo c d) = ENNReal.ofReal
      ((Real.log (d - b) - Real.log (d - a) - (Real.log (c - b) - Real.log (c - a))) / π) := by
  have hmem : ∀ x ∈ Icc c d, b < x := fun x hx => lt_of_lt_of_le hbc hx.1
  rw [show (Real.log (d - b) - Real.log (d - a) - (Real.log (c - b) - Real.log (c - a))) / π =
    (Real.log (d - b) - Real.log (d - a)) / π - (Real.log (c - b) - Real.log (c - a)) / π by ring]
  refine fl3_excR_eq_of_deriv hcd (f := fun x => (b - a) / (π * ((x - a) * (x - b))))
    (F := fun x => (Real.log (x - b) - Real.log (x - a)) / π)
    (fun x hx => fl3_yDer_intHarm hab (Or.inr (hmem x hx))) (fun x hx => ?_) ?_ (fun x hx => ?_)
  · have h1 : 0 < x - a := by linarith [hmem x hx]
    have h2 : 0 < x - b := by linarith [hmem x hx]
    have := Real.pi_pos
    exact div_nonneg (by linarith) (by positivity)
  · refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
    have h1 : 0 < x - a := by linarith [hmem x hx]
    have h2 : 0 < x - b := by linarith [hmem x hx]
    exact mul_ne_zero Real.pi_pos.ne' (mul_pos h1 h2).ne'
  · have h1 : 0 < x - a := by linarith [hmem x hx]
    have h2 : 0 < x - b := by linarith [hmem x hx]
    have hd := (((hasDerivAt_id x).sub_const b).log h2.ne').sub
      (((hasDerivAt_id x).sub_const a).log h1.ne')
    have hd3 : HasDerivAt (fun x => (Real.log (x - b) - Real.log (x - a)) / π)
        ((1 / (x - b) - 1 / (x - a)) / π) x := hd.div_const π
    refine hd3.congr_deriv ?_
    have e3 : x - a ≠ 0 := h1.ne'
    have e4 : x - b ≠ 0 := h2.ne'
    field_simp
    ring

/-- **Symmetry of the excursion flux between two real intervals.** -/
theorem fl3_excR_symm {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    excR (fl3IntHarm c d) (Ioo a b) = excR (fl3IntHarm a b) (Ioo c d) := by
  rw [fl3_excR_left hab hbc hcd, fl3_excR_right hab hbc hcd]
  congr 2
  ring

end FieldLawler
end QuantumZipper
