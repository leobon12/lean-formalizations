import SmallGammaGeodesics.Probes.Defs
import SmallGammaGeodesics.Core.Interfaces
import GaussianLQG.Frozen.MeasPairing
import GaussianLQG.Frozen.SegMeasure

/-!
# Interface of Lemma 4.2′ (the local Gaussian coupling for the probe maps)

Blueprint `lem:coupling` (§4.2), GA2 Details D5 with the corrections of rulings G20 and G24:
- clause (b5), the pairing identity with `λ`;
- joint measurability of `K`;
- the normalization `K(1/2) = 0`;
- the `L²` sup bound stated as a lower Lebesgue integral, so that a non-integrable supremum cannot make it vacuous.

`Lemma42` is proved: `lemma42_holds` (`Upper/Lemma42Holds.lean`) derives it from `NIC.nicInput_holds` (packets
P-G2, P-G3). The §5 packets take it as an interface hypothesis (ruling G10), and the providers of the main
theorems discharge it with `lemma42_holds`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric

/-- The inverse of the probe map on its strip of injectivity (junk off the image). -/
def probeInv (j : ℕ) (a θ : ℝ) : ℂ → ℂ := Function.invFunOn (probeMap j a θ) (probeStrip j)

/-- **Lemma 4.2′** (blueprint `lem:coupling`): for the probe maps `ϕ = z + iθH_{j,a}` with `|θ| ≤ ε₀ ℓ_j`, a
coupling of two whole-plane GFFs `h, h̄` with `h ∘ ϕ⁻¹ = h̄ + K` on `U_j`, where `K` is harmonic on `U_j`,
`K(1/2) = 0`, `E sup_{V_j} K² ≤ (C_K (|θ|/ℓ_j)(1 + log(1/ℓ_j)))²`, and
`(h̄, λ) = (h, ψ_*λ) − ∫ K dλ` for the pairings with the uniform measure `λ` on `[0,1]`. -/
def Lemma42 : Prop :=
  ∃ ε₀ CK : ℝ, 0 < ε₀ ∧ 0 < CK ∧ ∀ (j : ℕ) (a θ : ℝ), a ∈ Icc (0 : ℝ) 1 → |θ| ≤ ε₀ * ell j →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ),
      IsWholePlaneGFF h P ∧ IsWholePlaneGFF hbar P ∧
      Measurable (fun p : Ω × ℂ => K p.1 p.2) ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (K ω) (probeRectU j)) ∧
      (∀ ω, K ω (1 / 2) = 0) ∧
      (∀ᵐ ω ∂P, ∀ f g : TestC, tsupport (f : ℂ → ℝ) ⊆ probeRectU j →
        (∀ z ∈ probeStrip j, g z = ‖deriv (probeMap j a θ) z‖ ^ 2 * f (probeMap j a θ z)) →
        (∀ z ∉ probeStrip j, g z = 0) →
        h ω g = hbar ω f + ∫ w, K ω w * f w) ∧
      Measurable (fun ω => ⨆ w ∈ probeRectV j, |K ω w|) ∧
      (∫⁻ ω, ENNReal.ofReal ((⨆ w ∈ probeRectV j, |K ω w|) ^ 2) ∂P ≤
        ENNReal.ofReal ((CK * (|θ| / ell j) * (1 + Real.log (1 / ell j))) ^ 2)) ∧
      (∀ᵐ ω ∂P, GaussianLQG.measPairing (hbar ω) (GaussianLQG.segMeasure 0 1) =
        GaussianLQG.measPairing (h ω) ((GaussianLQG.segMeasure 0 1).map (probeInv j a θ)) -
          ∫ w, K ω w ∂(GaussianLQG.segMeasure 0 1))

end SmallGammaGeodesics
