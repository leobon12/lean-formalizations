import QuantumZipper.Proofs.Thm18.G1Z2ReflLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-REFL (2): the boundary order isomorphism of the inverse left uniformizer

Continuation of `G1Z2ReflLeft.lean`. On `(−∞,0)` the inverse `Ψ` of the reflected
left-normalized uniformizer is real with derivative `c` that is real (the imaginary part vanishes
on the axis) and has `Re c ≥ 0` (difference quotients along `iℝ₊`, since `Ψ(ℍ) ⊆ ℍ`; the
computation of `G1PkgLeft.lean`), and `c ≠ 0`; so it is strictly increasing, and onto `(−∞,0)`
because `Φ` maps `(−∞,0)` into `(−∞,0)`. Extended by the identity on `[0,∞)` it is an order
isomorphism of `ℝ` fixing `0`. Own elementary argument.

Main result: `sideReflGood_left_of_leftUniformizer`.
-/

noncomputable section

open Set Metric Filter Topology Complex Function
open QuantumZipper.CA QuantumZipper.CA.Uniformizer QuantumZipper.CA.Kernel
open scoped ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z2

variable {η : ℝ → ℂ} {φ Φ : ℂ → ℂ}

namespace ReflData

variable (R : ReflData η φ Φ)
include R

theorem inv_mem_H {w : ℂ} (hw : w ∈ H) : invFunOn Φ (leftDoubled η) w ∈ H := by
  rw [← R.eqOn_inv hw]
  have h : ∃ z ∈ leftComponent η, φ z = w := R.hφ.surjOn hw
  exact leftComponent_subset_H η (invFunOn_mem h)

theorem inv_eq_ofReal {t : ℝ} (ht : t < 0) :
    invFunOn Φ (leftDoubled η) t = (((invFunOn Φ (leftDoubled η) t).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(R.inv_real ht).1])

/-- The derivative of `Ψ` at a negative real point is a positive real number. -/
theorem deriv_inv_pos {t : ℝ} (ht : t < 0) :
    (deriv (invFunOn Φ (leftDoubled η)) t).im = 0 ∧
      0 < (deriv (invFunOn Φ (leftDoubled η)) t).re := by
  set Ψ := invFunOn Φ (leftDoubled η)
  set c := deriv Ψ t
  have hts : (t : ℂ) ∈ slitNeg := ofReal_mem_slitNeg ht
  have hΨ : HasDerivAt Ψ c t := (R.hasDerivAt_inv hts).differentiableAt.hasDerivAt
  have hne : c ≠ 0 := R.deriv_inv_ne hts
  -- imaginary part
  have him : c.im = 0 := by
    have h1 : HasDerivAt (fun x : ℝ => (-I * Ψ x).re) (-I * c).re t :=
      (hΨ.const_mul (-I)).real_of_complex
    have h2 : HasDerivAt (fun x : ℝ => (-I * Ψ x).re) 0 t := by
      refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds ht] with x hx
      have := (R.inv_real hx).1

      simp
      exact this
    have := h1.unique h2
    simpa using this
  -- real part is nonnegative
  have hre : 0 ≤ c.re := by
    have hl : HasDerivAt (fun s : ℝ => (t : ℂ) + (s : ℂ) * I) I 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const I).const_add (t : ℂ)
    have hc' : HasDerivAt Ψ c ((fun s : ℝ => (t : ℂ) + (s : ℂ) * I) 0) := by simpa using hΨ
    have h := hasDerivAt_iff_tendsto_slope.1 (hc'.comp (0 : ℝ) hl)
    have h' := h.mono_left (nhdsWithin_mono _ fun s (hs : s ∈ Ioi (0 : ℝ)) => ne_of_gt hs)
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), slope (Ψ ∘ fun s : ℝ => (t : ℂ) + (s : ℂ) * I) 0 s ∈
        {w : ℂ | 0 ≤ w.im} := by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      have hH : (t : ℂ) + (s : ℂ) * I ∈ H := show 0 < ((t : ℂ) + (s : ℂ) * I).im by simpa using hs
      have hpos' : 0 < (Ψ ((t : ℂ) + (s : ℂ) * I)).im := R.inv_mem_H hH
      have h0 : (Ψ ((t : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0 := by
        simpa using (R.inv_real ht).1
      simp only [slope_def_module, Function.comp_apply, smul_im, sub_im, smul_eq_mul, h0,
        sub_zero, sub_zero]
      exact mul_nonneg (inv_nonneg.2 hs.le) hpos'.le
    have := (isClosed_le continuous_const continuous_im).mem_of_tendsto h' hev
    simpa using this
  refine ⟨him, lt_of_le_of_ne hre fun h0 => hne ?_⟩
  exact Complex.ext h0.symm him

/-- The boundary function `b t = Re Ψ(t)`. -/
def bF (_R : ReflData η φ Φ) (t : ℝ) : ℝ := (invFunOn Φ (leftDoubled η) t).re

theorem hasDerivAt_bF {t : ℝ} (ht : t < 0) :
    HasDerivAt R.bF (deriv (invFunOn Φ (leftDoubled η)) t).re t :=
  ((R.hasDerivAt_inv (ofReal_mem_slitNeg ht)).differentiableAt.hasDerivAt).real_of_complex

theorem strictMonoOn_bF : StrictMonoOn R.bF (Iio 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Iio 0)
    (fun t ht => (R.hasDerivAt_bF ht).continuousAt.continuousWithinAt) fun t ht => ?_
  rw [interior_Iio] at ht
  rw [(R.hasDerivAt_bF ht).deriv]
  exact (R.deriv_inv_pos ht).2

theorem exists_bF_eq {y : ℝ} (hy : y < 0) : ∃ s : ℝ, s < 0 ∧ R.bF s = y := by
  obtain ⟨him, hre⟩ := R.fwd_real hy
  have hyL : (y : ℂ) ∈ leftDoubled η := Or.inr ⟨by simp, by simpa using hy⟩
  have hΦy : Φ y = (((Φ y).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨(Φ y).re, hre, ?_⟩
  unfold bF
  rw [← hΦy, R.inv_of_mem hyL]
  simp

/-- The global boundary function: `b` on `(−∞,0)`, the identity on `[0,∞)`. -/
def gF (t : ℝ) : ℝ := if t < 0 then R.bF t else t

theorem gF_strictMono : StrictMono R.gF := by
  intro x y hxy
  unfold gF
  by_cases hy : y < 0
  · have hx : x < 0 := hxy.trans hy
    rw [if_pos hx, if_pos hy]
    exact R.strictMonoOn_bF hx hy hxy
  · rw [if_neg hy]
    by_cases hx : x < 0
    · rw [if_pos hx]
      have := (R.inv_real hx).2
      unfold bF
      linarith [not_lt.1 hy]
    · rw [if_neg hx]; exact hxy

theorem gF_surjective : Surjective R.gF := by
  intro y
  by_cases hy : y < 0
  · obtain ⟨s, hs, hsy⟩ := R.exists_bF_eq hy
    exact ⟨s, by unfold gF; rw [if_pos hs, hsy]⟩
  · exact ⟨y, by unfold gF; rw [if_neg hy]⟩

/-- The boundary order isomorphism. -/
def isoF : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective R.gF R.gF_strictMono R.gF_surjective

theorem isoF_apply (t : ℝ) : R.isoF t = R.gF t := rfl

theorem sideReflGood : SideReflGood true (invFunOn φ (leftComponent η)) R.isoF := by
  refine ⟨by rw [isoF_apply]; unfold gF; simp, fun p q _ hIcc => ?_⟩
  have hneg : ∀ t ∈ Icc p q, t < 0 := fun t ht => by
    have := hIcc ht
    simpa [g1SideHalf] using this
  refine ⟨slitNeg, invFunOn Φ (leftDoubled η), isOpen_slitNeg,
    fun t ht => ofReal_mem_slitNeg (hneg t ht),
    fun w hw => (R.hasDerivAt_inv hw).differentiableAt.differentiableWithinAt,
    fun t ht => ?_, fun t ht => R.deriv_inv_ne (ofReal_mem_slitNeg (hneg t ht)), R.eqOn_inv⟩
  rw [isoF_apply]
  unfold gF
  rw [if_pos (hneg t ht)]
  exact R.inv_eq_ofReal (hneg t ht)

end ReflData

/-- **Reflection data of the inverse left-normalized uniformizer.** -/
theorem sideReflGood_left_of_leftUniformizer {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsLeftUniformizer η φ) :
    ∃ Φg : ℝ ≃o ℝ, SideReflGood true (invFunOn φ (leftComponent η)) Φg := by
  obtain ⟨Φ, hLo, hΦd, hΦb, -, -, hΦeq⟩ := leftReflection η φ hη hφ
  exact ⟨_, (ReflData.mk hη hφ.1.1 hLo hΦd hΦb hΦeq).sideReflGood⟩

end G1Z2
end Thm18Asm
end QuantumZipper
