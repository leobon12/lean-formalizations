import SmallGammaGeodesics.CC.Pullback
import SmallGammaGeodesics.Lower.MobiusLaw

/-!
# P-L2's Möbius transport is a conformal pullback (track CC, packet CC1)

Bridge between the general conformal pullback `confPullFun` (`CC/Pullback.lean`, D1.1) and P-L2's
Möbius transport `mobTransportFun` (`Lower/MobiusLaw.lean`, GA4 A3), for use by CC12 (the (MC)
export, which combines the law statement `map_mobTransport0_eq` with the coupling `confPull`).

For `|θ| ≤ 1/10`, `W₀ ⊆ B₅(0)` and any set `W` on which `φ_θ = mobPhi θ` has no pole and which
contains `ψ_θ(W₀)` (`ψ_θ = mobPhi (-θ)`), the transport of `f` supported in `W₀` is the pullback
`1_W |φ_θ'|² (f ∘ φ_θ)`: `mobTransportFun_eq_confPullFun`, `isConfPull_mobTransport`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace SmallGammaGeodesics.CC

open LQGMetric

variable {θ : ℝ} {W₀ W : Set ℂ}

/-- **P-L2's Möbius transport is the conformal pullback by `φ_θ`.** -/
theorem mobTransportFun_eq_confPullFun (hsub : mobPhi (-θ) '' W₀ ⊆ W)
    (hden : ∀ x ∈ W, 1 + (Complex.exp (θ * Complex.I) - 1) * x ≠ 0) {f : ℂ → ℝ}
    (hf : tsupport f ⊆ W₀) : mobTransportFun θ W₀ f = confPullFun (mobPhi θ) W f := by
  funext x
  by_cases hx : x ∈ W
  · rw [mobTransportFun_eq hf (hden x hx), confPullFun_of_mem hx, mul_comm]
  · rw [confPullFun_of_notMem hx, mobTransportFun,
      indicator_of_notMem fun h => hx (hsub h)]

/-- **P-L2's transported test function is the conformal pullback** (`IsConfPull`). -/
theorem isConfPull_mobTransport (hθ : |θ| ≤ 1 / 10) (hW₀ : W₀ ⊆ Metric.ball 0 5)
    (hsub : mobPhi (-θ) '' W₀ ⊆ W)
    (hden : ∀ x ∈ W, 1 + (Complex.exp (θ * Complex.I) - 1) * x ≠ 0) (f : TestC)
    (hf : tsupport (f : ℂ → ℝ) ⊆ W₀) :
    IsConfPull (mobPhi θ) W f (mobTransport hθ hW₀ f hf) := by
  rw [isConfPull_iff, coe_mobTransport]
  exact mobTransportFun_eq_confPullFun hsub hden hf

end SmallGammaGeodesics.CC
