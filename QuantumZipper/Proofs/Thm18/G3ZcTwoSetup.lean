import QuantumZipper.Proofs.Thm18.G3ZcChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C (c), step 4: D3⁺ setups at two points for one free field

`exists_g0Setup_two`: for admissible local maps `ψ₁`, `ψ₂` of G0 (`IsG0Map`), `0 < γ < 2` and a
real point `x₂`, on one probability space there is **one** free field `W` with

* a D3⁺ `Setup` (`α = 0`) at `0` whose model agrees a.s. near `0` with the normalized zoom of `W`
  through `ψ₁` (as in `exists_g0Setup`), and whose conditioning variables `Ξ₁` determine the field
  far from `0`: there is `R₁ > 0` such that every balanced increment `W(α) − W(α')` of measures
  carried by `{‖y‖ > R₁}` is a.s. a measurable function of `Ξ₁` (the domain Markov property,
  `FarPair`, G3ZcFar);
* a D3⁺ `Setup` at `0` whose model agrees a.s. near `0` with the normalized zoom of the translated
  field `rawTranslate W x₂` through `ψ₂` (the zoom of `W` at `x₂`; `ae_coordChange_translate`
  identifies it with the `translate` form).

This is the joint coupling of ZOOM-C (c) (Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71:
two small half-discs, the inside fields independent given the outside). Own assembly of
`exists_twoCouplings` (G3ZcJoint) and the parametrized G0 chain (G3ZcChain).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm D3Plus

/-- A local conformal datum translated by a real constant is again a local conformal datum. -/
theorem PullData.addReal {Ψ : ℂ → ℂ} {r₀ ρ r₁ m M : ℝ} (hD : PullData Ψ 0 r₀ ρ r₁ m M)
    (x : ℝ) : PullData (fun z => Ψ z + (x : ℂ)) 0 r₀ ρ r₁ m M := by
  obtain ⟨⟨hpos, hdiff, hinj, hder, hsymm, hmeas⟩, hρ, hρr, ⟨hm, hM, hbl⟩, hr₁, hup⟩ := hD
  refine ⟨⟨hpos, hdiff.add_const _, fun z hz w hw h => hinj hz hw (add_right_cancel h),
    fun z hz => ?_, fun z hz => ?_, hmeas.add_const _⟩, hρ, hρr, ⟨hm, hM, fun z hz w hw => ?_⟩,
    hr₁, fun z hz => ?_⟩
  · rw [deriv_add_const]; exact hder z hz
  · rw [hsymm z hz, map_add, Complex.conj_ofReal]
  · simpa only [add_sub_add_right_eq_sub] using hbl z hz w hw
  · have := hup z hz
    simp only [Hbar, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero] at this ⊢
    exact this

end G3Cv
end QuantumZipper
