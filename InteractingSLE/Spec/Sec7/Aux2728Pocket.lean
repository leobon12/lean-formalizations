/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61BGlobal
import InteractingSLE.Spec.Sec7.Lemma71MChart
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# Aux. lemmas 27–28 in a pocket chart: side limits make the mean the bounded Poisson extension

Packet PROVE-STRIPSYS25. Specification §7.4, the proof of Aux. lemma 119 (`source/spec/p385-432.md` L52, p. 387):

> The only exceptions are `x₀`, `y₀` and the finitely many angle-change points on the selected arcs. Apply the retained
> local-set subpower estimate of **Aux.** 27 and the conformal finite-exception uniqueness argument of **Aux.** 28.
> These remove any additional singular harmonic term. The mean is therefore the bounded finite-piece Poisson extension
> of (PW13.1) […]

and its restatement in supplement §2.3 (`source/spec/p433-480.md` L515–L522, pp. 454–455: "The bounded Poisson
extension of these heights, pulled back and corrected by `−χ Im L_φ`, is the conditional mean: the boundary comparison
identifies it away from the two endpoints and finitely many angle marks, and Aux. 28 excludes a remaining singular
harmonic term").

A pocket chart is a conformal `Chart` `c` whose domain is a component of `ℍ ∖ A` (`c.1 : C → ℍ`, `c.2.1` its inverse,
`c.2.2` the imaginary part of a logarithm `ℓ` of `c.1′`, shifted by `2πn`). Its **coordinate mean** of a harmonic
function `v` is `v ∘ c⁻¹ + u₀ ∘ c⁻¹ + χ (c.2.2 ∘ c⁻¹ + 2πn)` (the coordinate rule (1.4) applied to the mean, as in
`Aux119Own`). If at every real chart point outside a finite set `J` the coordinate mean of the local-set mean has the
boundary value `b(ξ)`, and `G` is a bounded harmonic extension of `b` off `J`, then the coordinate mean is `G` on the
whole component: `v + u₀ = G ∘ c.1 − χ (c.2.2 + 2πn)`.

The proof reads the side limits at the prime ends of the component through the disc chart `c⁻¹ ∘ cayleyInv` (every
prime end but `1` is a real chart point, `Lemma71M.cayleyInv_boundary`) and applies Proposition 6.1's identification
step on every component, `Sec6.ae_eqOn_component_of_tendsto_global` (Aux. lemma 27's subpower bound in Wang–Wu's global
form, and Aux. lemma 28's finite-exception uniqueness).

## Main results

* `isConformalBijection_fwd`, `isConformalBijection_disc`: the two charts of Aux. lemma 28 from a conformal `Chart`;
* `deriv_fwd_eq`: the shifted lift is an argument of `c.1′`;
* `tendsto_disc_of_sideLimit`: side limits at the real chart points give the prime-end limits in the disc;
* **`ae_eqOn_of_sideLimit`**: Aux. lemmas 27–28 in a pocket chart.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux2728Pocket

open QuantumZipper (H)
open QuantumZipper.CA (cayley cayleyInv)
open LocalSets

/-! ### The two charts of Aux. lemma 28 -/

section Chart

variable {c : Chart}

/-- The forward map of a conformal chart is a conformal bijection of its domain onto `ℍ`. -/
theorem isConformalBijection_fwd (hc : c.IsConformal) : IsConformalBijection c.1 c.dom H := by
  refine ⟨hc.differentiableOn_fwd, fun z hz => hc.fwd_mem hz, fun z₁ h₁ z₂ h₂ he => ?_, fun w hw => ?_⟩
  · rw [← hc.inv_fwd h₁, ← hc.inv_fwd h₂, he]
  · exact ⟨c.2.1 w, hc.inv_mem_dom hw, hc.2.2 w hw⟩

/-- **The disc chart**: `q ↦ c⁻¹(cayleyInv q)` is a conformal bijection of the unit disc onto the chart domain. -/
theorem isConformalBijection_disc (hc : c.IsConformal) :
    IsConformalBijection (fun q => c.2.1 (cayleyInv q)) (ball 0 1) c.dom :=
  isConformalBijection_comp hc.isConformalBijection isConformalBijection_cayleyInv

/-- **The shifted lift is an argument of `c.1′`**: if `c.2.2 = Im ℓ` for a logarithm `ℓ` of `c.1′`, then
`c.1′ = |c.1′| e^{i (c.2.2 + 2πn)}` on the domain. -/
theorem deriv_fwd_eq {ℓ : ℂ → ℂ} {D : Set ℂ} (hℓ : IsDerivLog c.1 ℓ D) (hlift : ∀ z ∈ D, c.2.2 z = (ℓ z).im)
    (n : ℤ) : ∀ z ∈ D, deriv c.1 z = ‖deriv c.1 z‖ * exp (((c.2.2 z + 2 * π * n : ℝ) : ℂ) * I) := by
  intro z hz
  rw [← hℓ.2 z hz, Complex.norm_exp, hlift z hz]
  have h2 : exp ((((ℓ z).im + 2 * π * n : ℝ) : ℂ) * I) = exp (((ℓ z).im : ℂ) * I) := by
    have e : (((ℓ z).im + 2 * π * n : ℝ) : ℂ) * I = ((ℓ z).im : ℂ) * I + n * (2 * π * I) := by
      push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h2]
  conv_lhs => rw [← Complex.re_add_im (ℓ z)]
  rw [Complex.exp_add, Complex.ofReal_exp]

/-- The shifted lift is continuous on the domain of the logarithm. -/
theorem continuousOn_shift {ℓ : ℂ → ℂ} {D : Set ℂ} (hℓ : IsDerivLog c.1 ℓ D)
    (hlift : ∀ z ∈ D, c.2.2 z = (ℓ z).im) (n : ℤ) : ContinuousOn (fun z => c.2.2 z + 2 * π * n) D := by
  have h : ContinuousOn (fun z => (ℓ z).im + 2 * π * n) D :=
    (Complex.continuous_im.comp_continuousOn hℓ.1.continuousOn).add continuousOn_const
  exact h.congr fun z hz => by simp only [hlift z hz]

/-- **Side limits give the prime-end limits.** If at every real chart point `ξ ∉ J` the coordinate mean
`v ∘ c⁻¹ + u₀ ∘ c⁻¹ + χ (c.2.2 ∘ c⁻¹ + 2πn)` and `G` have the same limit `b ξ` from `ℍ`, then along the disc chart the
difference `(v + u₀) − (G ∘ c.1 − χ (c.2.2 + 2πn))` tends to `0` at every prime end outside `1` and the Cayley images
of `J`. -/
theorem tendsto_disc_of_sideLimit (hc : c.IsConformal) {v u₀ G : ℂ → ℝ} {b : ℝ → ℝ} {J : Set ℝ} {χ : ℝ} {n : ℤ}
    (hside : ∀ ξ : ℝ, ξ ∉ J → Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + χ * (c.2.2 (c.2.1 y) + 2 * π * n))
      (𝓝[H] (ξ : ℂ)) (𝓝 (b ξ)))
    (hG : ∀ ξ : ℝ, ξ ∉ J → Tendsto G (𝓝[H] (ξ : ℂ)) (𝓝 (b ξ))) :
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ insert 1 ((fun x : ℝ => cayley (x : ℂ)) '' J) →
      Tendsto (fun ζ => (v (c.2.1 (cayleyInv ζ)) + u₀ (c.2.1 (cayleyInv ζ))) -
        (G (c.1 (c.2.1 (cayleyInv ζ))) - χ * (c.2.2 (c.2.1 (cayleyInv ζ)) + 2 * π * n)))
        (𝓝[ball 0 1] q) (𝓝 0) := by
  intro q hq hqE
  have hq1 : q ≠ 1 := fun h => hqE (Set.mem_insert_iff.2 (Or.inl h))
  obtain ⟨hre, hlim⟩ := Lemma71M.cayleyInv_boundary hq hq1
  set x : ℝ := (cayleyInv q).re with hx
  have hxJ : x ∉ J := fun h => hqE (mem_insert_of_mem _ ⟨x, h, by
    simp only
    rw [hre, QuantumZipper.CA.cayley_cayleyInv hq1]⟩)
  rw [← hre] at hlim
  have hdiff := ((hside x hxJ).sub (hG x hxJ)).comp hlim
  rw [sub_self] at hdiff
  refine hdiff.congr' (eventually_nhdsWithin_of_forall fun ζ hζ => ?_)
  have hy : cayleyInv ζ ∈ H := QuantumZipper.CA.cayleyInv_mem_H hζ
  simp only [Function.comp_apply, hc.2.2 _ hy]
  ring

end Chart

/-! ### Aux. lemmas 27–28 in a pocket chart -/

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ} {g : Ω → DistOn upperHalfPlaneOpens}

/-- **Aux. lemmas 27–28 in a pocket chart** (proof of Aux. lemma 119, p. 387: "Apply the retained local-set subpower
estimate of Aux. 27 and the conformal finite-exception uniqueness argument of Aux. 28. These remove any additional
singular harmonic term. The mean is therefore the bounded finite-piece Poisson extension of (PW13.1)"). Let `A` be a
local set of the zero-boundary GFF `X` on `ℍ` with local-set mean `g`, and `u₀` a bounded harmonic function on `ℍ` (the
deterministic mean; the field is `X + u₀`). Almost surely, for every harmonic representative `v` of `g` on `ℍ ∖ A`,
every conformal chart `c` whose domain is a component of `ℍ ∖ A`, with lift `c.2.2 = Im ℓ` for a logarithm `ℓ` of
`c.1′` and an integer shift `n`, every finite set `J ⊆ ℝ`, every boundary function `b` and every bounded harmonic
extension `G` of `b` off `J`: if the coordinate mean of `v` has the boundary value `b(ξ)` at every real chart point
`ξ ∉ J`, then `v + u₀ = G ∘ c.1 − χ (c.2.2 + 2πn)` on the component. -/
theorem ae_eqOn_of_sideLimit (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A X P) (hg : IsLocalSetMean A X P g)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ x, v x * φ x) →
      ∀ (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (b : ℝ → ℝ) (J : Set ℝ) (G : ℂ → ℝ), c.IsConformal →
      (∃ z₀ ∈ H \ A ω, (c.dom : Set ℂ) = connectedComponentIn (H \ A ω) z₀) →
      IsDerivLog c.1 ℓ c.dom → (∀ z ∈ c.dom, c.2.2 z = (ℓ z).im) → J.Finite →
      IsBoundedHarmonicExtension b J G →
      (∀ ξ : ℝ, ξ ∉ J → Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + χ * (c.2.2 (c.2.1 y) + 2 * π * n))
        (𝓝[H] (ξ : ℂ)) (𝓝 (b ξ))) →
      ∀ z ∈ c.dom, v z + u₀ z = G (c.1 z) - χ * (c.2.2 z + 2 * π * n) := by
  filter_upwards [Sec6.ae_eqOn_component_of_tendsto_global hh hA hloc hg hu₀ hu₀b χ] with ω hω v hv hgv c ℓ n b J G
    hc hcomp hℓ hlift hJ hGext hside
  obtain ⟨z₀, hz₀, hdom⟩ := hcomp
  have hf := isConformalBijection_disc hc
  have hφ := isConformalBijection_fwd hc
  rw [hdom] at hf hφ
  have hLc := continuousOn_shift hℓ hlift n
  have hder := deriv_fwd_eq hℓ hlift n
  rw [hdom] at hLc hder
  have hbd := tendsto_disc_of_sideLimit hc (G := G) hside fun ξ hξ => hGext.2.2 ξ hξ
  have key := hω z₀ hz₀ v hv hgv (fun q => c.2.1 (cayleyInv q)) c.1 G (fun z => c.2.2 z + 2 * π * n)
    (insert 1 ((fun x : ℝ => cayley (x : ℂ)) '' J)) hf hφ hGext.1 hGext.2.1 hLc hder ((hJ.image _).insert 1) hbd
  intro z hz
  exact key z (by rw [← hdom]; exact hz)

end Prob

end InteractingSLE.Sec7.Aux2728Pocket
