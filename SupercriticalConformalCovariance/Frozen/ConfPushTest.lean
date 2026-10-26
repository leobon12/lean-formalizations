import SupercriticalConformalCovariance.Frozen.IsConformalBijection
import SmallGammaGeodesics.CC.LocalPull

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `confPushTest`. Declaration unchanged from the candidate `CandConfPushTest.lean` (sha256 5462cdc4ba63111f…). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Set Function
open scoped Distributions
open LQGMetric (TestOn)
open SmallGammaGeodesics.CC (confPullFun confPullK confK confK_subset confPullFun_add
  confPullFun_smul contDiff_confPullFun hasCompactSupport_confPullFun tsupport_confPullFun_subset
  differentiableOn_leftInv injOn_leftInv image_leftInv_image apply_leftInv)

namespace SupercriticalConformalCovariance

/-- Paper l. 26 and (2), l. 34 (the test-function side of `h ∘ φ`; Gwynne–Miller 1905.00384v2 l. 544,
`(h ∘ φ⁻¹, f) = (h, |φ′|² (f ∘ φ))`): for a conformal
bijection `φ : U → V` with inverse `φ⁻¹ = invFunOn φ U`, the change-of-variables transport of test
functions `ψ ↦ 1_V · |(φ⁻¹)′|² · (ψ ∘ φ⁻¹)`, from `𝓓(U)` to `𝓓(V)`. It is the adjoint of `u ↦ u ∘ φ`:
`∫ u · (confPushTest ψ) = ∫ (u ∘ φ) · ψ` (substitution `y = φ x`, Jacobian `|φ′|²`), so that a field `h`
on `V` pairs as `⟨h ∘ φ, ψ⟩ = ⟨h, confPushTest ψ⟩`. The function is written out below; it is definitionally
SmallGammaGeodesics' conformal pullback `confPullFun (invFunOn φ U) V ψ` along `φ⁻¹` (holomorphic and injective on
the open set `V`), whose lemmas are used only for the proof obligations; continuity on each `𝓓_K(U)` is `confPullK`. -/
def confPushTest {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V) :
    TestOn U →L[ℝ] TestOn V :=
  have hψφ : ∀ z ∈ (U : Set ℂ), invFunOn φ U (φ z) = z := fun _ hz =>
    hφ.2.injOn.leftInvOn_invFunOn hz
  have hd : DifferentiableOn ℂ (invFunOn φ U) V := by
    have h := differentiableOn_leftInv U.isOpen hφ.1 hφ.2.injOn hψφ
    rwa [hφ.2.image_eq] at h
  have hi : InjOn (invFunOn φ U) V := by
    have h := injOn_leftInv hψφ
    rwa [hφ.2.image_eq] at h
  have hU : (U : Set ℂ) ⊆ invFunOn φ U '' V := by
    rw [← hφ.2.image_eq, image_leftInv_image hψφ subset_rfl]
  have hφψ : ∀ y ∈ (V : Set ℂ), φ (invFunOn φ U y) = y := fun _ hy =>
    apply_leftInv hψφ (hφ.2.image_eq.symm ▸ hy)
  TestFunction.mkCLM ℝ
    (fun g : TestOn U => (⟨(V : Set ℂ).indicator fun y => ‖deriv (invFunOn φ U) y‖ ^ 2 * g (invFunOn φ U y),
      contDiff_confPullFun V.isOpen hd hi g.contDiff g.hasCompactSupport (g.tsupport_subset.trans hU),
      hasCompactSupport_confPullFun V.isOpen hd hi g.hasCompactSupport (g.tsupport_subset.trans hU),
      (tsupport_confPullFun_subset V.isOpen hd hi hφψ g.hasCompactSupport
        (g.tsupport_subset.trans hU)).trans
        ((image_mono g.tsupport_subset).trans hφ.2.image_eq.subset)⟩ : TestOn V))
    (fun g₁ g₂ => by
      ext x
      change confPullFun (invFunOn φ U) V (⇑g₁ + ⇑g₂) x = _
      rw [confPullFun_add]
      rfl)
    (fun c g => by
      ext x
      change confPullFun (invFunOn φ U) V (c • ⇑g) x = _
      rw [confPullFun_smul]
      rfl)
    (fun K hK => by
      have hKψ : (K : Set ℂ) ⊆ invFunOn φ U '' V := hK.trans hU
      have he : (fun g : TestOn U => (⟨(V : Set ℂ).indicator fun y => ‖deriv (invFunOn φ U) y‖ ^ 2 * g (invFunOn φ U y),
          contDiff_confPullFun V.isOpen hd hi g.contDiff g.hasCompactSupport
            (g.tsupport_subset.trans hU),
          hasCompactSupport_confPullFun V.isOpen hd hi g.hasCompactSupport
            (g.tsupport_subset.trans hU),
          (tsupport_confPullFun_subset V.isOpen hd hi hφψ g.hasCompactSupport
            (g.tsupport_subset.trans hU)).trans
            ((image_mono g.tsupport_subset).trans hφ.2.image_eq.subset)⟩ : TestOn V)) ∘
            TestFunction.ofSupportedIn hK =
          TestFunction.ofSupportedInCLM ℝ (confK_subset V.isOpen hd hi K hKψ) ∘
            confPullK V.isOpen hd hi K hKψ := by
        funext g
        ext x
        rfl
      rw [he]
      exact (TestFunction.ofSupportedInCLM ℝ (confK_subset V.isOpen hd hi K hKψ)).continuous.comp
        (confPullK V.isOpen hd hi K hKψ).continuous)

end SupercriticalConformalCovariance
