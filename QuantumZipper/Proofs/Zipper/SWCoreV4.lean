import QuantumZipper.Proofs.Zipper.SWCoreV2
import QuantumZipper.Proofs.Zipper.SWCoreVClassMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-V (4): the pushed-versus-round variance bound, uniformly over a boundary class

Task SWC-V (`handoff/SW-CORE.md` §5, item (i)). Sheffield–Wang, arXiv:1605.06171, Lemma 3.4
(3.17)–(3.19), p. 15 and (3.20): for a boundary class `BdryClass a b ρ M m` (`a < b`, `ρ, m > 0`)
there are `r₀ > 0` and `C` such that for every `ψ` of the class, every `t ∈ [a,b]` and every
`r ∈ (0, r₀)`,

  `|kernelCov2 neumannH (fc(t,r).map ψ, fc(ψ t, r ‖ψ'(t)‖)) (…)| ≤ C · r^{1/6}`
                                                               (`swcv_class_var`).

This is the variance of `X(fc(t,r).map ψ) − X(fc(ψ t, r‖ψ'(t)‖))` for the free field (for
admissible pairs, `IsFreeGFFModConstH.covariance_eq`). Combination of the class rescaling
`bdryClass_rescale` (Cauchy estimates, `SWCoreVClassMain`) with `swcv_kernelCov2_push`.
The exponent `1/6` (SW: `1`) comes from the Hölder modulus of Neumann potentials of `1/3`-Frostman
measures; it suffices for Borel–Cantelli along `r = 2^{-k}`. Own assembly.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace SWCore

open TwoPoint

/-- **SWC-V (i)**: pushed-versus-round variance bound, uniform over a boundary class. -/
theorem swcv_class_var (a b ρ M m : ℝ) (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ BdryClass a b ρ M m, ∀ t ∈ Icc a b,
      ∀ r ∈ Ioo 0 r₀,
        |kernelCov2 neumannH ((foldedCircle (t : ℂ) r).map ψ,
            foldedCircle (((ψ t).re : ℝ) : ℂ) (r * ‖deriv ψ t‖))
            ((foldedCircle (t : ℂ) r).map ψ,
              foldedCircle (((ψ t).re : ℝ) : ℂ) (r * ‖deriv ψ t‖))| ≤
          C * r ^ ((1 / 3 : ℝ) / 2) := by
  obtain ⟨r₁, hr₁, C₁, hC₁, hres⟩ := bdryClass_rescale a b ρ M m hab hρ hm
  set r₀ := min r₁ (min (ρ / 2) (1 / (C₁ + 1))) with hr₀
  have hr₀p : 0 < r₀ := lt_min hr₁ (lt_min (by linarith) (by positivity))
  have hK0 : 0 ≤ holderK 24 2 := holderK_nonneg (by norm_num) (by norm_num)
  refine ⟨r₀, hr₀p, 2 * (holderK 24 2 * C₁ ^ ((1 / 3 : ℝ) / 2)), by positivity,
    fun ψ hψ t ht r hr => ?_⟩
  have hrr₁ : r < r₁ := lt_of_lt_of_le hr.2 (min_le_left _ _)
  have hrρ : r < ρ / 2 := lt_of_lt_of_le hr.2 ((min_le_right _ _).trans (min_le_left _ _))
  have hrC : r < 1 / (C₁ + 1) := lt_of_lt_of_le hr.2 ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨⟨hDe, hmD, -⟩, hdisp, hlip, him, -⟩ := hres ψ hψ t ht r ⟨hr.1, hrr₁⟩
  set D : ℝ := (deriv ψ t).re with hD
  have hDpos : 0 < D := lt_of_lt_of_le hm hmD
  have hnorm : ‖deriv ψ t‖ = D := by
    rw [hDe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDpos]
  rw [hnorm]
  have hψt : (ψ t).im = 0 := hψ.2.2.1 t ht
  have hball : closedBall (t : ℂ) r ⊆ thickening ρ (segC a b) := fun z hz => by
    rw [mem_thickening_iff]
    refine ⟨(t : ℂ), ⟨t, ht, rfl⟩, ?_⟩
    have := mem_closedBall.1 hz
    linarith
  have hψc : ContinuousOn ψ (closedBall (t : ℂ) r) := (hψ.1.mono hball).continuousOn
  have hΔ1 : C₁ * r ≤ 1 := by
    have h1 : r * (C₁ + 1) < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hrC; exact hrC
    nlinarith [hr.1]
  have hmain := swcv_kernelCov2_push (ψ := ψ) (t := t) (r := r) (D := D) (Δ := C₁ * r) hr.1
    hDpos hψt hψc (mul_nonneg hC₁ hr.1.le) hΔ1 (fun u hu => hdisp u hu)
    (fun u hu v hv => (hlip u hu v hv).1) (fun u hu hui => him u hu hui)
  refine hmain.trans (le_of_eq ?_)
  rw [Real.mul_rpow hC₁ hr.1.le]
  ring

end SWCore
end QuantumZipper
