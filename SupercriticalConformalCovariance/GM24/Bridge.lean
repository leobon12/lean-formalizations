import SupercriticalConformalCovariance.GM24.AsConv
import SupercriticalConformalCovariance.ZBConformal.Pullback

/-!
# Bridge from GM Lemma 2.4 (2.5) to the candidate `confPushTest`

The working definitions in `SupercriticalConformalCovariance.ZBConformal.Setup` (not the frozen statement) define
`h ∘ φ` for a conformal bijection `φ : U → V` and `h ∈ 𝒟'(V)` as `distPullback hφ h = h ∘ confPushTest hφ`.
GM's field `h ∘ φ_n⁻¹` is the pullback by the inverse bijection `φ_n⁻¹ : V_n → U_n`. This file proves:

* `isConformalBijection_invFunOn`: `φ⁻¹ = invFunOn φ U` is a conformal bijection `V → U`;
* `coe_confPushTest_inv`: `confPushTest (φ⁻¹) g = |φ'|² (g ∘ φ)` on `U`, i.e. `confPullFun φ U g`;
* `distPullback_inv_eq`: `distPullback (φ⁻¹) (h|_U) = invPullDist … V … h` (the GM-side field);
* `tendsto_distPullback_inv`: display (2.5) in the candidate form.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Function TopologicalSpace
open scoped Distributions

namespace SupercriticalConformalCovariance.GM24

open LQGMetric SupercriticalConformalCovariance SupercriticalConformalCovariance.ZBConformal
open SmallGammaGeodesics.CC (confPullFun confPullFun_of_mem confPullFun_of_notMem
  differentiableOn_leftInv injOn_leftInv apply_leftInv coe_confPullOnCLM confPullOnCLM)

variable {φ : ℂ → ℂ} {U V : Opens ℂ}

/-- The inverse `φ⁻¹ = invFunOn φ U` of a conformal bijection `φ : U → V` is a conformal bijection
`V → U`. -/
theorem isConformalBijection_invFunOn (hφ : IsConformalBijection φ U V) :
    IsConformalBijection (invFunOn φ (U : Set ℂ)) V U := by
  have hψφ : ∀ z ∈ (U : Set ℂ), invFunOn φ U (φ z) = z := fun _ hz =>
    hφ.2.injOn.leftInvOn_invFunOn hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := differentiableOn_leftInv U.isOpen hφ.1 hφ.2.injOn hψφ
    rwa [hφ.2.image_eq] at h
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hφ.2.surjOn hy
    rw [hψφ x hx]
    exact hx
  · have h := injOn_leftInv hψφ
    rwa [hφ.2.image_eq] at h
  · intro x hx
    exact ⟨φ x, hφ.2.mapsTo hx, hψφ x hx⟩

/-- `(φ⁻¹)⁻¹ = φ` on `U`. -/
theorem invFunOn_invFunOn_eq (hφ : IsConformalBijection φ U V) {x : ℂ} (hx : x ∈ (U : Set ℂ)) :
    invFunOn (invFunOn φ (U : Set ℂ)) (V : Set ℂ) x = φ x := by
  have hinv := isConformalBijection_invFunOn hφ
  have hψφ : invFunOn φ (U : Set ℂ) (φ x) = x := hφ.2.injOn.leftInvOn_invFunOn hx
  have hex : ∃ y ∈ (V : Set ℂ), invFunOn φ (U : Set ℂ) y = x := ⟨φ x, hφ.2.mapsTo hx, hψφ⟩
  exact hinv.2.injOn (invFunOn_mem hex) (hφ.2.mapsTo hx) ((invFunOn_eq hex).trans hψφ.symm)

/-- **The transport bridge.** The candidate test transport of the inverse bijection is the GM-side
`|φ'|² (g ∘ φ)` (`confPullFun φ U g`). -/
theorem coe_confPushTest_inv (hφ : IsConformalBijection φ U V) (g : TestOn V) :
    ⇑(confPushTest (isConformalBijection_invFunOn hφ) g) = confPullFun φ U g := by
  funext x
  change confPullFun (invFunOn (invFunOn φ (U : Set ℂ)) (V : Set ℂ)) U g x = _
  by_cases hx : x ∈ (U : Set ℂ)
  · rw [confPullFun_of_mem hx, confPullFun_of_mem hx, invFunOn_invFunOn_eq hφ hx]
    have he : invFunOn (invFunOn φ (U : Set ℂ)) (V : Set ℂ) =ᶠ[𝓝 x] φ :=
      Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds hx) fun y hy => invFunOn_invFunOn_eq hφ hy
    rw [he.deriv_eq]
  · rw [confPullFun_of_notMem hx, confPullFun_of_notMem hx]

theorem subset_image_of_isConformalBijection (hφ : IsConformalBijection φ U V) :
    ((V : Opens ℂ) : Set ℂ) ⊆ φ '' (U : Set ℂ) :=
  hφ.2.image_eq.symm.subset

/-- **The field bridge.** For `h ∈ 𝒟'(ℂ)`, the candidate pullback of `h|_U` by `φ⁻¹ : V → U` is the
GM-side restricted field `h ∘ φ⁻¹` on `V` (`invPullDist`). -/
theorem distPullback_inv_eq (hφ : IsConformalBijection φ U V) (h : DistC) :
    distPullback (isConformalBijection_invFunOn hφ) (restrictTo U h) =
      invPullDist U.isOpen hφ.1 hφ.2.injOn V (subset_image_of_isConformalBijection hφ) h := by
  ext g
  rw [distPullback_apply]
  show h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤)
    (confPushTest (isConformalBijection_invFunOn hφ) g)) = h (confPullOnCLM _ _ _ V _ g)
  congr 1
  ext x
  rw [TestFunction.monoCLM_apply, ite_cond_eq_true _ _ (eq_true ⟨le_rfl, le_top⟩),
    coe_confPushTest_inv hφ, coe_confPullOnCLM]

open scoped Classical in
/-- **GM Lemma 2.4 (2.5), candidate form.** For conformal bijections `φ_n : U_n → V_n` with the
hypotheses of GM Lemma 2.3, every `h ∈ 𝒟'(ℂ)`, and every bounded open `O`: eventually `O ⊆ V_n`, and
`(h|_{U_n}) ∘ φ_n⁻¹` (candidate `distPullback`) converges to `h(α ·)` against every `g ∈ 𝓓(O)`. -/
theorem tendsto_distPullback_inv {U V : ℕ → Opens ℂ} {φ : ℕ → ℂ → ℂ} {α : ℂ}
    (hφ : ∀ n, IsConformalBijection (φ n) (U n) (V n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hzero : ∀ n, φ n 0 = 0) (hα : α ≠ 0)
    (hder : Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹)) (h : DistC) (O : Opens ℂ)
    (hO : Bornology.IsBounded (O : Set ℂ)) :
    (∀ᶠ n in atTop, O ≤ V n) ∧
    ∀ g : TestOn O, Tendsto (fun n => if hn : O ≤ V n then
        distPullback (isConformalBijection_invFunOn (hφ n)) (restrictTo (U n) h)
          (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := V n) g) else 0) atTop
      (𝓝 (restrictTo O (dilDist hα h) g)) := by
  have himg : ∀ n, (φ n) '' (U n : Set ℂ) = V n := fun n => (hφ n).2.image_eq
  obtain ⟨hsub, hconv⟩ := tendsto_invPullDist (fun n => (U n).isOpen) hzeroU hexhaust
    (fun n => (hφ n).1) (fun n => (hφ n).2.injOn) hzero hα hder h O hO
  have hsub' : ∀ᶠ n in atTop, O ≤ V n := by
    filter_upwards [hsub] with n hn
    rw [himg n] at hn
    exact hn
  refine ⟨hsub', fun g => (hconv g).congr' ?_⟩
  filter_upwards [hsub, hsub'] with n hn hn'
  rw [dif_pos hn, dif_pos hn', distPullback_inv_eq (hφ n), invPullDist, invPullDist]
  show h (confPullOnCLM _ _ _ O hn g) = h (confPullOnCLM _ _ _ (V n) _ _)
  congr 1
  ext x
  rw [coe_confPullOnCLM, coe_confPullOnCLM, TestFunction.monoCLM_apply,
    ite_cond_eq_true _ _ (eq_true ⟨le_rfl, hn'⟩)]

end SupercriticalConformalCovariance.GM24
