import QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Poisson–Jensen bound for exponential boundary moments (task P16-BDRYMOM-A)

If `F ∘ foldH` is harmonic on a neighbourhood of `closedBall t s0` (`t ∈ ℝ`), then for every
`z ∈ Hbar` with `‖z - t‖ ≤ s0 / 2` and every `λ ∈ ℝ`,
`exp (λ F z) ≤ 4 ∫ exp (λ F) d(foldedCircle t s0)`.

Proof (classical): the half-disc Poisson formula (`K3.integral_halfDiscPoisson_of_harmonic`,
i.e. the disc Poisson integral, Axler–Bourdon–Ramey, *Harmonic Function Theory*, 2nd ed.,
Thm 1.17, applied to the even function `F ∘ foldH`) writes `F z` as the mean of `F ∘ foldH`
under the probability measure `halfDiscPoisson t s0 z`; Jensen's inequality for `exp`
(mathlib `ConvexOn.map_integral_le`) gives `exp (λ F z) ≤ ∫ exp (λ F ∘ foldH) dP_z`; finally the
Poisson density is at most `s0² / (s0 - s0/2)² = 4` on the circle (`K3.halfDiscPoisson_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter InnerProductSpace
open scoped Real ComplexConjugate ENNReal

namespace QuantumZipper

namespace Prop16Asm

theorem foldH_conj_bdryMom (z : ℂ) : foldH (conj z) = foldH z := by
  rw [CircleFubini.foldH_eq_mk, CircleFubini.foldH_eq_mk]
  simp [abs_neg]

theorem pBound_half_bdryMom {s0 : ℝ} (hs0 : 0 < s0) : K3.pBound s0 (s0 / 2) = 4 := by
  unfold K3.pBound
  have : s0 ^ 2 / (s0 - s0 / 2) ^ 2 = 4 := by
    field_simp
    ring
  rw [this]
  norm_num

theorem ofReal_exp_le_poissonJensen_bdryMom {F : ℂ → ℝ} {t s0 : ℝ} (hs0 : 0 < s0)
    (hF : InnerProductSpace.HarmonicOnNhd (fun z => F (foldH z)) (Metric.closedBall (t : ℂ) s0))
    (lam : ℝ) {z : ℂ} (hz : z ∈ Hbar) (hzt : ‖z - (t : ℂ)‖ ≤ s0 / 2) :
    ENNReal.ofReal (Real.exp (lam * F z)) ≤
      4 * ∫⁻ w, ENNReal.ofReal (Real.exp (lam * F w)) ∂foldedCircle (t : ℂ) s0 := by
  set f : ℂ → ℝ := fun z => F (foldH z) with hfdef
  have hzb : z ∈ ball (t : ℂ) s0 := mem_ball_iff_norm.2 (by linarith)
  have : IsProbabilityMeasure (K3.halfDiscPoisson t s0 z) :=
    K3.isProbabilityMeasure_halfDiscPoisson hs0 hzb
  set P := K3.halfDiscPoisson t s0 z with hP
  -- reproduction
  have hrep : ∫ x, f x ∂P = f z :=
    K3.integral_halfDiscPoisson_of_harmonic hs0 hzb hF
      (fun x _ => by simp only [hfdef, foldH_conj_bdryMom])
  have hfz : f z = F z := by simp only [hfdef, CircleFubini.foldH_of_mem' hz]
  -- integrability via continuity on the sphere
  have hSm : MeasurableSet (sphere (t : ℂ) s0) := isClosed_sphere.measurableSet
  have hcont : ContinuousOn f (sphere (t : ℂ) s0) := fun x hx =>
    (hF x (sphere_subset_closedBall hx)).1.continuousAt.continuousWithinAt
  have hconc : ∀ᵐ x ∂P, x ∈ sphere (t : ℂ) s0 :=
    (K3.ae_halfDiscPoisson_mem hs0 z).mono fun x hx => hx.1
  have hPr : P.restrict (sphere (t : ℂ) s0) = P := Measure.restrict_eq_self_of_ae_mem hconc
  have hfi : Integrable f P := by
    rw [← hPr]
    exact hcont.integrableOn_compact (isCompact_sphere _ _)
  have hgi : Integrable (fun x => Real.exp (lam * f x)) P := by
    rw [← hPr]
    exact (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul hcont)).integrableOn_compact (isCompact_sphere _ _)
  have hlfi : Integrable (fun x => lam * f x) P := hfi.const_mul lam
  -- Jensen
  have hJ : Real.exp (∫ x, lam * f x ∂P) ≤ ∫ x, Real.exp (lam * f x) ∂P :=
    ConvexOn.map_integral_le (s := Set.univ) (g := Real.exp) (f := fun x => lam * f x)
      convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hlfi hgi
  rw [integral_const_mul, hrep, hfz] at hJ
  have h1 : ENNReal.ofReal (Real.exp (lam * F z)) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * f x)) ∂P := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi
      (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hJ
  -- density bound
  have h2 : ∫⁻ x, ENNReal.ofReal (Real.exp (lam * f x)) ∂P ≤
      4 * ∫⁻ x, ENNReal.ofReal (Real.exp (lam * f x)) ∂foldedCircle (t : ℂ) s0 := by
    calc _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (lam * f x)) ∂(K3.pBound s0 (s0 / 2) •
          foldedCircle (t : ℂ) s0) :=
          lintegral_mono' (K3.halfDiscPoisson_le hs0 (by linarith) hzt) le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul, pBound_half_bdryMom hs0]
  -- f = F a.e. on the folded circle
  have h3 : ∫⁻ x, ENNReal.ofReal (Real.exp (lam * f x)) ∂foldedCircle (t : ℂ) s0 =
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * F x)) ∂foldedCircle (t : ℂ) s0 := by
    refine lintegral_congr_ae ?_
    have hH : ∀ᵐ x ∂foldedCircle (t : ℂ) s0, x ∈ Hbar := by
      unfold foldedCircle
      exact (ae_map_iff measurable_foldH.aemeasurable isClosed_Hbar.measurableSet).2
        (ae_of_all _ fun w => K3.foldH_mem_Hbar_k3 w)
    filter_upwards [hH] with x hx
    simp only [hfdef, CircleFubini.foldH_of_mem' hx]
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := by rw [h3]

end Prop16Asm

end QuantumZipper
