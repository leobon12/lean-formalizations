import SupercriticalConformalCovariance.Frozen.ConfPushTest

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `confPullbackField`. Declaration unchanged from the candidate `CandConfPullbackField.lean` (sha256 6fe3dc08cc3c9dfe…). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped Distributions
open LQGMetric (DistOn TestOn)

namespace SupercriticalConformalCovariance

/-- Paper l. 26 (the field `h ∘ ϕ + Q log |ϕ′|` of Theorem 1.1) and (2), l. 34, the LQG coordinate change
(Gwynne–Miller 1905.00384v2 (1.8), (1.11) and l. 356–361; DG (1.14)): for a conformal bijection
`φ : U → V` and a distribution `h` on `V`, the distribution `h ∘ φ + Q log |φ′|` on `U`,
`⟨h ∘ φ + Q log |φ′|, ψ⟩ = ⟨h, 1_V |(φ⁻¹)′|² (ψ ∘ φ⁻¹)⟩ + ∫ ψ(x) · Q log |φ′(x)| dx` for `ψ ∈ 𝓓(U)`.
The first term is `h ∘ confPushTest` (mathlib's precomposition of a distribution by a continuous linear
map of test functions, `ContinuousLinearMap.precompCompactConvergenceCLM`); the second is mathlib's
`Distribution.ofFun` of `x ↦ Q log ‖φ′ x‖`, which is continuous on `U` because `φ′` does not vanish there,
hence locally integrable on `U`, so `ofFun` is the honest integral (`Distribution.ofFun_apply`). -/
def confPullbackField (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
    (h : DistOn V) : DistOn U :=
  (confPushTest hφ).precompCompactConvergenceCLM ℝ h +
    Distribution.ofFun U (fun x => Q * Real.log ‖deriv φ x‖) volume ⊤

end SupercriticalConformalCovariance
