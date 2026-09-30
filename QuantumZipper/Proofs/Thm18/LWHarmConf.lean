import QuantumZipper.Proofs.Thm18.LWExcDefs
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route (D60): conformal invariance of the excursion integral

Task LW-HARM (C). Source: G. F. Lawler, *Conformally Invariant Processes in the Plane*, AMS 2005,
§5.2 (the boundary excursion measure `ℰ_D(V₁, V₂) = ∫_{V₂} ∂_n h_{V₁}` and its conformal
invariance, proved there from the transformation rule `∂_n (h ∘ f) = |f'| (∂_n h) ∘ f` and the
change of variables on the boundary arc), as used by Lawler–Werness, Ann. Probab. 41 (2013),
p. 23. We formalize exactly these two steps for the half-plane form `excR`:

* `lwHarm_yDer_of_hasFDerivAt`: `yDer f x = Df(x)[i]` when `f` is real-differentiable at the
  real point `x` with `f(x) = 0`;
* `lwHarm_yDer_comp`: for `ψ` holomorphic at the real point `x`, real there, with real
  derivative `d`, and `h` real-differentiable at `ψ(x)` with `h(ψ x) = 0`:
  `yDer (h ∘ ψ) x = d · yDer h (ψ x)`;
* `lwHarm_excR_comp`: `excR (h ∘ ψ) S = excR h (ψ(S))` for `ψ` injective and increasing on the
  real set `S` (change of variables, mathlib `lintegral_image_eq_lintegral_abs_deriv_mul`).

Differentiability of a harmonic measure at a real boundary point where it vanishes on a real
interval is the reflection principle (`harmReflectStmt_holds`, LWExc2Refl.lean): apply the lemmas
to the odd reflection `lwOddExt h`, which agrees with `h` on `ℍ̄` and hence has the same `yDer`.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- `yDer f x = Df(x)[i]` for `f` real-differentiable at a real zero `x`. -/
theorem lwHarm_yDer_of_hasFDerivAt {f : ℂ → ℝ} {x : ℝ} {L : ℂ →L[ℝ] ℝ}
    (hf : HasFDerivAt f L (x : ℂ)) (h0 : f x = 0) : yDer f x = L I := by
  have hl : HasDerivAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) I 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const I).const_add (x : ℂ)
  have hk : HasDerivAt (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (L I) 0 :=
    hf.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hT : Tendsto (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 (L I)) := by
    have h1 := (hasDerivAt_iff_tendsto_slope.1 hk).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
    refine h1.congr fun y => ?_
    simp [slope_def_field, h0]
  unfold yDer
  rw [if_pos ⟨_, hT⟩]
  exact hT.limUnder_eq

/-- **Transformation rule** `∂_y (h ∘ ψ)(x) = ψ'(x) ∂_y h(ψ x)` at a real point. -/
theorem lwHarm_yDer_comp {h : ℂ → ℝ} {ψ : ℂ → ℂ} {x d : ℝ} (hψ : HasDerivAt ψ (d : ℂ) (x : ℂ))
    (hre : (ψ x).im = 0) (hh : DifferentiableAt ℝ h (ψ x)) (h0 : h (ψ x) = 0) :
    yDer (h ∘ ψ) x = d * yDer h (ψ x).re := by
  have hpt : (((ψ x).re : ℝ) : ℂ) = ψ x := Complex.ext (by simp) (by simp [hre])
  set L := fderiv ℝ h (ψ x)
  have hL : HasFDerivAt h L (ψ x) := hh.hasFDerivAt
  have e1 : yDer h (ψ x).re = L I :=
    lwHarm_yDer_of_hasFDerivAt (by rw [hpt]; exact hL) (by rw [hpt]; exact h0)
  have hc := hL.comp (x : ℂ) (hψ.hasFDerivAt.restrictScalars ℝ)
  rw [lwHarm_yDer_of_hasFDerivAt hc (by simpa using h0), e1]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply]
  rw [show I • (d : ℂ) = (d : ℝ) • I by rw [Complex.real_smul, smul_eq_mul, mul_comm],
    L.map_smul, smul_eq_mul]

/-- **Conformal invariance of the excursion integral** (Lawler, §5.2): for `ψ` holomorphic, real
and increasing along the real set `S`, and `h` real-differentiable and vanishing on `ψ(S)`,
`∫_S ∂_y (h ∘ ψ) = ∫_{ψ(S)} ∂_y h`. -/
theorem lwHarm_excR_comp {h : ℂ → ℝ} {ψ : ℂ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    {d : ℝ → ℝ} (hψ : ∀ x ∈ S, HasDerivAt ψ (d x : ℂ) (x : ℂ)) (hd : ∀ x ∈ S, 0 ≤ d x)
    (hre : ∀ x ∈ S, (ψ x).im = 0) (hinj : InjOn (fun x : ℝ => (ψ x).re) S)
    (hh : ∀ x ∈ S, DifferentiableAt ℝ h (ψ x)) (h0 : ∀ x ∈ S, h (ψ x) = 0) :
    excR (h ∘ ψ) S = excR h ((fun x : ℝ => (ψ x).re) '' S) := by
  unfold excR
  have hder : ∀ x ∈ S, HasDerivWithinAt (fun x : ℝ => (ψ x).re) (d x) S x := fun x hx => by
    simpa using ((hψ x hx).real_of_complex).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hS hder hinj]
  refine setLIntegral_congr_fun hS fun x hx => ?_
  rw [lwHarm_yDer_comp (hψ x hx) (hre x hx) (hh x hx) (h0 x hx), abs_of_nonneg (hd x hx),
    ENNReal.ofReal_mul (hd x hx)]

end LWFar
end Thm18Asm
end QuantumZipper
