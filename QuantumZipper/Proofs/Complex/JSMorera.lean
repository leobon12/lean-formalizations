import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Morera from absolute continuity on lines (EXT-JS node A4)

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 step 6 and §3 node A4.

If a continuous `e : ℂ → ℂ` and a locally integrable `g : ℂ → ℂ` satisfy, on almost every
horizontal line, `e (b + y i) - e (a + y i) = ∫_a^b g (t + y i) dt`, and on almost every vertical
line, `e (x + b i) - e (x + a i) = i ∫_a^b g (x + t i) dt`, then the integral of `e` around every
rectangle vanishes (Fubini), so `e` is entire by Morera's theorem
(`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`).

This is the classical "ACL + Cauchy–Riemann a.e. ⇒ conformal" step: Ahlfors, *Lectures on
Quasiconformal Mappings*, 2nd ed., AMS 2006, Ch. II §B, Corollary 1 (p. 17), in the special form
used by Jones–Smirnov, *Removability theorems for Sobolev functions and quasiconformal maps*,
Ark. Mat. 38 (2000) 263–279, deduction of Theorem 1 from Proposition 1 (pp. 269–270, citing
"Section II.B of [A]"). Here the conformality is derived directly by Morera instead of via the
quasiconformal machinery. The
blueprint's extra hypotheses (`volume K = 0`, holomorphy off `K`) are not needed here: they are
only used upstream to produce the line identities with `g = Kᶜ.indicator (deriv e)`.
-/

open MeasureTheory Set Complex intervalIntegral

namespace QuantumZipper.JS

/-- The function `g` pulled back to `ℝ × ℝ` is integrable on every product of intervals. -/
lemma integrableOn_uIoc_prod_of_locallyIntegrable {g : ℂ → ℂ} (hg : LocallyIntegrable g volume)
    (a b c d : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => g (p.1 + p.2 * I)) (uIoc a b ×ˢ uIoc c d) := by
  have hK : IsCompact ((uIcc a b) ×ℂ (uIcc c d)) := isCompact_uIcc.reProdIm isCompact_uIcc
  have h1 : IntegrableOn g ((uIcc a b) ×ℂ (uIcc c d)) volume := hg.integrableOn_isCompact hK
  rw [← (volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
    (MeasurableEquiv.measurableEmbedding _)] at h1
  have h2 : IntegrableOn (fun p : ℝ × ℝ => g (p.1 + p.2 * I)) ((uIcc a b) ×ˢ (uIcc c d)) := by
    have : (fun p : ℝ × ℝ => g (p.1 + p.2 * I)) = g ∘ measurableEquivRealProd.symm := by
      funext p
      simp only [Function.comp_apply, measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
    rw [this]
    exact h1
  exact h2.mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

/-- **Rectangle integrals vanish.** Under the line hypotheses, `e` is conservative on `ℂ`. -/
theorem isConservativeOn_univ_of_lineIntegrals {e g : ℂ → ℂ} (he : Continuous e)
    (hg : LocallyIntegrable g volume)
    (hh : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      e (b + y * I) - e (a + y * I) = ∫ t in a..b, g (t + y * I))
    (hv : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      e (x + b * I) - e (x + a * I) = I * ∫ t in a..b, g (x + t * I)) :
    IsConservativeOn e univ := by
  intro z w _
  rw [eq_neg_iff_add_eq_zero, wedgeIntegral_add_wedgeIntegral_eq]
  set a := z.re
  set b := w.re
  set c := z.im
  set d := w.im
  have hcont : ∀ s : ℝ, Continuous fun x : ℝ => e (x + s * I) := fun s => by fun_prop
  have hcont' : ∀ s : ℝ, Continuous fun y : ℝ => e (s + y * I) := fun s => by fun_prop
  -- horizontal sides
  have H1 : (∫ x : ℝ in a..b, e (x + c * I)) - (∫ x : ℝ in a..b, e (x + d * I)) =
      -(I * ∫ x : ℝ in a..b, ∫ y : ℝ in c..d, g (x + y * I)) := by
    rw [← integral_sub ((hcont c).intervalIntegrable _ _) ((hcont d).intervalIntegrable _ _),
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae (hv.mono fun x hx _ => ?_)
    rw [← hx c d]
    ring
  -- vertical sides
  have H2 : I • (∫ y : ℝ in c..d, e (b + y * I)) - I • (∫ y : ℝ in c..d, e (a + y * I)) =
      I * ∫ y : ℝ in c..d, ∫ x : ℝ in a..b, g (x + y * I) := by
    rw [smul_eq_mul, smul_eq_mul, ← mul_sub,
      ← integral_sub ((hcont' b).intervalIntegrable _ _) ((hcont' a).intervalIntegrable _ _)]
    congr 1
    exact intervalIntegral.integral_congr_ae (hh.mono fun y hy _ => hy a b)
  have hswap : (∫ x : ℝ in a..b, ∫ y : ℝ in c..d, g (x + y * I)) =
      ∫ y : ℝ in c..d, ∫ x : ℝ in a..b, g (x + y * I) :=
    intervalIntegral_intervalIntegral_swap
      (F := fun x y => g (x + y * I))
      (integrableOn_uIoc_prod_of_locallyIntegrable hg a b c d)
  rw [add_sub_assoc, H1, H2, hswap]
  ring

/-- **Morera from lines.** A continuous function satisfying the horizontal and vertical line
identities with a locally integrable density `g` is entire. -/
theorem differentiable_of_lineIntegrals {e g : ℂ → ℂ} (he : Continuous e)
    (hg : LocallyIntegrable g volume)
    (hh : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      e (b + y * I) - e (a + y * I) = ∫ t in a..b, g (t + y * I))
    (hv : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      e (x + b * I) - e (x + a * I) = I * ∫ t in a..b, g (x + t * I)) :
    Differentiable ℂ e := by
  have := (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).1
    ⟨isConservativeOn_univ_of_lineIntegrals he hg hh hv, he.continuousOn⟩
  exact differentiableOn_univ.1 this

/-- Blueprint form of node A4: the density is `Kᶜ.indicator (deriv e)`. -/
theorem differentiable_of_acl {e : ℂ → ℂ} {K : Set ℂ} (he : Continuous e)
    (hg : LocallyIntegrable (Kᶜ.indicator (deriv e)) volume)
    (hh : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      e (b + y * I) - e (a + y * I) = ∫ t in a..b, Kᶜ.indicator (deriv e) (t + y * I))
    (hv : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      e (x + b * I) - e (x + a * I) = I * ∫ t in a..b, Kᶜ.indicator (deriv e) (x + t * I)) :
    Differentiable ℂ e :=
  differentiable_of_lineIntegrals he hg hh hv

end QuantumZipper.JS
