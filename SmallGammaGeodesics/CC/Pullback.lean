import SmallGammaGeodesics.Core.Interfaces
import QuantumZipper.Proofs.GFF.K3.Conformal
import QuantumZipper.Proofs.Analysis.Pushforward

/-!
# The conformal pullback of test functions (track CC, packet CC1; [3] (1.10), (1.12))

Source: Gwynne–Miller, *Conformal covariance of the Liouville quantum gravity metric for γ ∈ (0,2)*,
arXiv:1905.00384 ([3]), (1.10) and (1.12), as corrected and planned in
`planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D1** items 1–3.

Let `ϕ` be holomorphic and injective on an open set `W`, and let `ψ` be any left inverse of `ϕ` on
`W` (`∀ z ∈ W, ψ (ϕ z) = z`; e.g. `Function.invFunOn ϕ W`). The **conformal pullback** of a function
`g` is `τg = 1_W · |ϕ'|² · (g ∘ ϕ)` (`confPullFun`; `IsConfPull` of `Core/Interfaces.lean` is the
test-function form). Results:

* the inverse: `ψ` is holomorphic and injective on the open set `ϕ '' W`, with
  `ψ'(ϕ z) ϕ'(z) = 1` (`hasDerivAt_leftInv`, `deriv_leftInv_mul`);
* **T1** (D1.1) `exists_confPull : ExistsConfPull`, with the explicit pullback `confPullTest`, and
  `IsConfPull.tsupport_subset`: `tsupport τg ⊆ ψ '' tsupport g ⊆ V`;
* **T2** (D1.2) the change of variables `IsConfPull.integral_mul`:
  `∫ τg · u = ∫ g · (u ∘ ψ)` for **every** `u` (no integrability or continuity needed), hence
  `∫ τg = ∫ g` and `∫ log|ϕ'| · τg = -∫ log|ψ'| · g`;
* **T3** (D1.3) composition: `confPullFun ϕ W (confPullFun ψ (ϕ '' W) g) = 1_W · g` and
  `confPullFun ψ (ϕ '' W) (confPullFun ϕ W g) = 1_{ϕ(W)} · g`; for test functions,
  `IsConfPull.comp_inv`.

The proofs generalize P-L2's Möbius transport (`Lower/MobiusLaw.lean`): smoothness by
`QuantumZipper.K3.contDiff_of_contDiffOn_of_support_subset`, and the change of variables by
Mathlib's `integral_image_eq_integral_abs_det_fderiv_smul` with Jacobian `|ϕ'|²`
(`QuantumZipper.abs_det_fderiv_eq_normSq`), here along `ϕ` on `W` itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## 1. The inverse of an injective holomorphic map -/

section Inverse

variable {ϕ ψ : ℂ → ℂ} {W : Set ℂ}

/-- The image of an open set under an injective holomorphic map is open. -/
theorem isOpen_image_conf (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) :
    IsOpen (ϕ '' W) :=
  QuantumZipper.CA.isOpen_image_of_injOn' hW hd hi

/-- A left inverse on `W` is a right inverse on `ϕ '' W`. -/
theorem apply_leftInv (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {y : ℂ} (hy : y ∈ ϕ '' W) : ϕ (ψ y) = y := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [hψ z hz]

theorem leftInv_mem (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {y : ℂ} (hy : y ∈ ϕ '' W) : ψ y ∈ W := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [hψ z hz]
  exact hz

/-- `ψ '' (ϕ '' S) = S` for `S ⊆ W`. -/
theorem image_leftInv_image (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {S : Set ℂ} (hS : S ⊆ W) :
    ψ '' (ϕ '' S) = S := by
  rw [image_image]
  exact (image_congr fun z hz => hψ z (hS hz)).trans (image_id' S)

/-- Any left inverse agrees with QuantumZipper's holomorphic inverse on `ϕ '' W`. -/
theorem eqOn_univalentOPH_symm (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) :
    EqOn ψ (QuantumZipper.CA.univalentOPH hW hd hi).symm (ϕ '' W) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [hψ z hz, QuantumZipper.CA.univalentOPH_symm_apply_apply hW hd hi hz]

/-- **The inverse is holomorphic**, with `ψ'(y) = 1 / ϕ'(ψ y)` on `ϕ '' W`. -/
theorem hasDerivAt_leftInv (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {y : ℂ} (hy : y ∈ ϕ '' W) :
    HasDerivAt ψ (deriv ϕ (ψ y))⁻¹ y := by
  have h := QuantumZipper.CA.hasDerivAt_univalentOPH_symm hW hd hi hy
  rw [← eqOn_univalentOPH_symm hW hd hi hψ hy] at h
  refine h.congr_of_eventuallyEq ?_
  exact Filter.eventuallyEq_of_mem ((isOpen_image_conf hW hd hi).mem_nhds hy)
    (eqOn_univalentOPH_symm hW hd hi hψ)

theorem differentiableOn_leftInv (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) : DifferentiableOn ℂ ψ (ϕ '' W) := fun _ hy =>
  (hasDerivAt_leftInv hW hd hi hψ hy).differentiableAt.differentiableWithinAt

theorem continuousOn_leftInv (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) : ContinuousOn ψ (ϕ '' W) :=
  (differentiableOn_leftInv hW hd hi hψ).continuousOn

theorem injOn_leftInv (hψ : ∀ z ∈ W, ψ (ϕ z) = z) : InjOn ψ (ϕ '' W) := by
  intro y₁ hy₁ y₂ hy₂ h
  rw [← apply_leftInv hψ hy₁, ← apply_leftInv hψ hy₂, h]

/-- `ϕ` is a left inverse of `ψ` on `ϕ '' W`. -/
theorem leftInv_leftInv (hψ : ∀ z ∈ W, ψ (ϕ z) = z) : ∀ y ∈ ϕ '' W, ϕ (ψ y) = y :=
  fun _ hy => apply_leftInv hψ hy

/-- **The chain rule for the inverse**: `ψ'(ϕ z) ϕ'(z) = 1` on `W`. -/
theorem deriv_leftInv_mul (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {z : ℂ} (hz : z ∈ W) : deriv ψ (ϕ z) * deriv ϕ z = 1 := by
  rw [(hasDerivAt_leftInv hW hd hi hψ (mem_image_of_mem ϕ hz)).deriv, hψ z hz]
  exact inv_mul_cancel₀ (QuantumZipper.CA.deriv_ne_zero_of_injOn hW hd hi hz)

theorem norm_deriv_leftInv_mul (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {z : ℂ} (hz : z ∈ W) :
    ‖deriv ψ (ϕ z)‖ * ‖deriv ϕ z‖ = 1 := by
  rw [← norm_mul, deriv_leftInv_mul hW hd hi hψ hz, norm_one]

/-- `ψ'(y) ϕ'(ψ y) = 1` on `ϕ '' W`. -/
theorem deriv_mul_deriv_leftInv (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {y : ℂ} (hy : y ∈ ϕ '' W) : deriv ϕ (ψ y) * deriv ψ y = 1 := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [hψ z hz, mul_comm]
  exact deriv_leftInv_mul hW hd hi hψ hz

end Inverse

/-! ## 2. The pullback of functions -/

/-- **The conformal pullback** `τg = 1_W · |ϕ'|² · (g ∘ ϕ)` of a function. -/
def confPullFun (ϕ : ℂ → ℂ) (W : Set ℂ) (g : ℂ → ℝ) : ℂ → ℝ :=
  W.indicator fun y => ‖deriv ϕ y‖ ^ 2 * g (ϕ y)

theorem isConfPull_iff {ϕ : ℂ → ℂ} {W : Set ℂ} {g τg : TestC} :
    IsConfPull ϕ W g τg ↔ ⇑τg = confPullFun ϕ W g :=
  ⟨fun h => funext h, fun h x => congrFun h x⟩

section PullFun

variable {ϕ ψ : ℂ → ℂ} {W : Set ℂ} {g : ℂ → ℝ}

theorem confPullFun_of_mem {x : ℂ} (hx : x ∈ W) :
    confPullFun ϕ W g x = ‖deriv ϕ x‖ ^ 2 * g (ϕ x) := by
  rw [confPullFun, indicator_of_mem hx]

theorem confPullFun_of_notMem {x : ℂ} (hx : x ∉ W) : confPullFun ϕ W g x = 0 := by
  rw [confPullFun, indicator_of_notMem hx]

/-- `τg` vanishes off `ψ '' tsupport g`. -/
theorem confPullFun_eq_zero (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {x : ℂ} (hx : x ∉ ψ '' tsupport g) :
    confPullFun ϕ W g x = 0 := by
  by_cases hxW : x ∈ W
  · rw [confPullFun_of_mem hxW]
    have : g (ϕ x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ⟨ϕ x, h, hψ x hxW⟩
    rw [this, mul_zero]
  · exact confPullFun_of_notMem hxW

/-- `ψ '' tsupport g ⊆ S` when `tsupport g ⊆ ϕ '' S` and `S ⊆ W`. -/
theorem leftInv_image_tsupport_subset (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {S : Set ℂ} (hS : S ⊆ W)
    (hg : tsupport g ⊆ ϕ '' S) : ψ '' tsupport g ⊆ S := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hg hy
  rw [hψ z (hS hz)]
  exact hz

theorem isCompact_leftInv_image_tsupport (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) (hgc : HasCompactSupport g)
    (hg : tsupport g ⊆ ϕ '' W) :
    IsCompact (ψ '' tsupport g) :=
  hgc.isCompact.image_of_continuousOn ((continuousOn_leftInv hW hd hi hψ).mono hg)

theorem hasCompactSupport_confPullFun (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hgc : HasCompactSupport g) (hg : tsupport g ⊆ ϕ '' W) :
    HasCompactSupport (confPullFun ϕ W g) :=
  HasCompactSupport.intro
    (isCompact_leftInv_image_tsupport hW hd hi (fun _ hz => hi.leftInvOn_invFunOn hz) hgc hg)
    fun _ hx => confPullFun_eq_zero (fun _ hz => hi.leftInvOn_invFunOn hz) hx

/-- **`tsupport τg ⊆ ψ '' tsupport g`** (D1.1). -/
theorem tsupport_confPullFun_subset (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) (hgc : HasCompactSupport g)
    (hg : tsupport g ⊆ ϕ '' W) : tsupport (confPullFun ϕ W g) ⊆ ψ '' tsupport g :=
  closure_minimal (fun _ hx => by_contra fun h => hx (confPullFun_eq_zero hψ h))
    (isCompact_leftInv_image_tsupport hW hd hi hψ hgc hg).isClosed

/-- **`τg` is smooth** when `g` is smooth with compact support in `ϕ '' W` (D1.1). -/
theorem contDiff_confPullFun (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hgd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g)
    (hg : tsupport g ⊆ ϕ '' W) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (confPullFun ϕ W g) := by
  have hψ : ∀ z ∈ W, invFunOn ϕ W (ϕ z) = z := fun _ hz => hi.leftInvOn_invFunOn hz
  have hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϕ W :=
    (hd.contDiffOn hW).restrict_scalars ℝ
  have hφ' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv ϕ) W :=
    ((hd.deriv hW).contDiffOn hW).restrict_scalars ℝ
  have hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ‖deriv ϕ y‖ ^ 2 * g (ϕ y)) W :=
    ((contDiff_norm_sq ℝ).comp_contDiffOn hφ').mul (hgd.comp_contDiffOn hφ)
  refine QuantumZipper.K3.contDiff_of_contDiffOn_of_support_subset hW
    (isCompact_leftInv_image_tsupport hW hd hi hψ hgc hg)
    ((leftInv_image_tsupport_subset hψ subset_rfl) hg) ?_ fun x hx => confPullFun_eq_zero hψ hx
  exact hF.congr fun x hx => confPullFun_of_mem hx

/-! ### Change of variables (D1.2) -/

/-- **Change of variables** `y = ϕ x` (D1.2): `∫ τg · u = ∫ g · (u ∘ ψ)` for **every** `u`, when `g`
vanishes off `ϕ '' W`. No integrability is needed: Mathlib's formula
`integral_image_eq_integral_abs_det_fderiv_smul` holds for every integrand, and the Jacobian of `ϕ`
is `|ϕ'|²`. -/
theorem integral_confPullFun_mul (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) (hg : ∀ y ∉ ϕ '' W, g y = 0) (u : ℂ → ℝ) :
    ∫ x, confPullFun ϕ W g x * u x = ∫ y, g y * u (ψ y) := by
  have hWm : MeasurableSet W := hW.measurableSet
  have h1 : ∫ x, confPullFun ϕ W g x * u x = ∫ x in W, confPullFun ϕ W g x * u x := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [confPullFun_of_notMem hx, zero_mul]
  have hderiv : ∀ x ∈ W, HasFDerivWithinAt ϕ (fderiv ℝ ϕ x) W x := fun x hx =>
    ((hd.differentiableAt (hW.mem_nhds hx)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have h2 := integral_image_eq_integral_abs_det_fderiv_smul volume hWm hderiv hi
    (fun y => g y * u (ψ y))
  have h3 : ∫ y in ϕ '' W, g y * u (ψ y) = ∫ y, g y * u (ψ y) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [hg y hy, zero_mul]
  rw [h1, ← h3, h2]
  refine setIntegral_congr_fun hWm fun x hx => ?_
  rw [QuantumZipper.abs_det_fderiv_eq_normSq (hd.differentiableAt (hW.mem_nhds hx)), smul_eq_mul,
    confPullFun_of_mem hx, hψ x hx]
  ring

/-- `∫ τg = ∫ g` (D1.2). -/
theorem integral_confPullFun (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hg : ∀ y ∉ ϕ '' W, g y = 0) : ∫ x, confPullFun ϕ W g x = ∫ y, g y := by
  have h := integral_confPullFun_mul hW hd hi (fun _ hz => hi.leftInvOn_invFunOn hz) hg
    (fun _ => 1)
  simpa only [mul_one] using h

/-- `log|ϕ'(ψ y)| = -log|ψ'(y)|` on `ϕ '' W`. -/
theorem log_norm_deriv_leftInv (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {y : ℂ} (hy : y ∈ ϕ '' W) :
    Real.log ‖deriv ϕ (ψ y)‖ = -Real.log ‖deriv ψ y‖ := by
  have h1 : ‖deriv ϕ (ψ y)‖ * ‖deriv ψ y‖ = 1 := by
    rw [← norm_mul, deriv_mul_deriv_leftInv hW hd hi hψ hy, norm_one]
  rw [← Real.log_inv, eq_inv_of_mul_eq_one_left h1]

/-- `∫ log|ϕ'| · τg = -∫ log|ψ'| · g` (D1.2): the Liouville term of the coupling. -/
theorem integral_log_mul_confPullFun (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) (hg : ∀ y ∉ ϕ '' W, g y = 0) :
    ∫ x, Real.log ‖deriv ϕ x‖ * confPullFun ϕ W g x = -∫ y, Real.log ‖deriv ψ y‖ * g y := by
  have h := integral_confPullFun_mul hW hd hi hψ hg (fun x => Real.log ‖deriv ϕ x‖)
  simp_rw [mul_comm (Real.log _) (confPullFun ϕ W g _)]
  rw [h, ← integral_neg]
  congr 1
  funext y
  by_cases hy : y ∈ ϕ '' W
  · rw [log_norm_deriv_leftInv hW hd hi hψ hy]
    ring
  · rw [hg y hy]
    ring

/-! ### Composition (D1.3) -/

/-- **Composition** (D1.3): `τ_ϕ (τ_ψ g) = 1_W · g`, where `τ_ψ g = 1_{ϕ(W)} |ψ'|² (g ∘ ψ)`. -/
theorem confPullFun_confPullFun_leftInv (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) (g : ℂ → ℝ) :
    confPullFun ϕ W (confPullFun ψ (ϕ '' W) g) = W.indicator g := by
  funext x
  by_cases hx : x ∈ W
  · rw [confPullFun_of_mem hx, confPullFun_of_mem (mem_image_of_mem ϕ hx), hψ x hx,
      indicator_of_mem hx]
    have h1 := norm_deriv_leftInv_mul hW hd hi hψ hx
    calc ‖deriv ϕ x‖ ^ 2 * (‖deriv ψ (ϕ x)‖ ^ 2 * g x)
        = (‖deriv ψ (ϕ x)‖ * ‖deriv ϕ x‖) ^ 2 * g x := by ring
      _ = g x := by rw [h1, one_pow, one_mul]
  · rw [confPullFun_of_notMem hx, indicator_of_notMem hx]

/-- **Composition, other order**: `τ_ψ (τ_ϕ g) = 1_{ϕ(W)} · g`. -/
theorem confPullFun_leftInv_confPullFun (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) (g : ℂ → ℝ) :
    confPullFun ψ (ϕ '' W) (confPullFun ϕ W g) = (ϕ '' W).indicator g := by
  funext y
  by_cases hy : y ∈ ϕ '' W
  · rw [confPullFun_of_mem hy, confPullFun_of_mem (leftInv_mem hψ hy), apply_leftInv hψ hy,
      indicator_of_mem hy]
    have h1 : ‖deriv ϕ (ψ y)‖ * ‖deriv ψ y‖ = 1 := by
      rw [← norm_mul, deriv_mul_deriv_leftInv hW hd hi hψ hy, norm_one]
    calc ‖deriv ψ y‖ ^ 2 * (‖deriv ϕ (ψ y)‖ ^ 2 * g y)
        = (‖deriv ϕ (ψ y)‖ * ‖deriv ψ y‖) ^ 2 * g y := by ring
      _ = g y := by rw [h1, one_pow, one_mul]
  · rw [confPullFun_of_notMem hy, indicator_of_notMem hy]

end PullFun

/-! ## 3. The inverse neighbourhood (D1.4, setup) -/

section Nbhd

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ}

theorem IsConfNbhd.subset (hϕ : IsConfNbhd ϕ W V) : V ⊆ W :=
  subset_closure.trans hϕ.closure_subset

theorem IsConfNbhd.image_subset (hϕ : IsConfNbhd ϕ W V) : ϕ '' V ⊆ ϕ '' W :=
  image_mono hϕ.subset

theorem IsConfNbhd.isCompact_closure (hϕ : IsConfNbhd ϕ W V) : IsCompact (closure V) :=
  hϕ.isBounded_V.isCompact_closure

/-- `ϕ (closure V)` is compact. -/
theorem IsConfNbhd.isCompact_image_closure (hϕ : IsConfNbhd ϕ W V) :
    IsCompact (ϕ '' closure V) :=
  hϕ.isCompact_closure.image_of_continuousOn (hϕ.differentiableOn.continuousOn.mono
    hϕ.closure_subset)

theorem IsConfNbhd.closure_image_subset (hϕ : IsConfNbhd ϕ W V) :
    closure (ϕ '' V) ⊆ ϕ '' closure V :=
  closure_minimal (image_mono subset_closure) hϕ.isCompact_image_closure.isClosed

theorem IsConfNbhd.isOpen_image (hϕ : IsConfNbhd ϕ W V) : IsOpen (ϕ '' V) :=
  QuantumZipper.CA.isOpen_image_of_injOn hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hϕ.isOpen_V
    hϕ.subset

/-- **The inverse neighbourhood** (D1.4): the left inverse `ψ` is conformal on `ϕ '' W ⊇
closure (ϕ '' V)`, and `ϕ '' V` is a bounded open set. -/
theorem IsConfNbhd.inv (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) :
    IsConfNbhd ψ (ϕ '' W) (ϕ '' V) where
  isOpen_W := isOpen_image_conf hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn
  isOpen_V := hϕ.isOpen_image
  isBounded_V := hϕ.isCompact_image_closure.isBounded.subset (image_mono subset_closure)
  closure_subset := hϕ.closure_image_subset.trans (image_mono hϕ.closure_subset)
  differentiableOn := differentiableOn_leftInv hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ
  injOn := injOn_leftInv hψ

/-- `ψ '' (ϕ '' V) = V`. -/
theorem IsConfNbhd.image_inv_image (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) :
    ψ '' (ϕ '' V) = V :=
  image_leftInv_image hψ hϕ.subset

end Nbhd

/-! ## 4. Test functions (T1–T3) -/

section TestFunctions

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ}

/-- **The conformal pullback of a test function** supported in `ϕ '' W` (D1.1). -/
def confPullTest (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (g : TestC)
    (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' W) : TestC where
  toFun := confPullFun ϕ W g
  contDiff' := contDiff_confPullFun hW hd hi g.contDiff g.hasCompactSupport hg
  hasCompactSupport' := hasCompactSupport_confPullFun hW hd hi g.hasCompactSupport hg
  tsupport_subset' := subset_univ _

theorem coe_confPullTest (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (g : TestC) (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' W) :
    ⇑(confPullTest hW hd hi g hg) = confPullFun ϕ W g :=
  rfl

theorem isConfPull_confPullTest (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (g : TestC) (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' W) :
    IsConfPull ϕ W g (confPullTest hW hd hi g hg) :=
  fun _ => rfl

/-- **T1** (D1.1): pullbacks of test functions supported in `ϕ(V)` are test functions. -/
theorem exists_confPull : ExistsConfPull := fun _ _ _ hϕ g hg =>
  ⟨confPullTest hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn g (hg.trans hϕ.image_subset),
    isConfPull_confPullTest _ _ _ _ _⟩

/-- The pullback is unique. -/
theorem IsConfPull.eq {g τ₁ τ₂ : TestC} (h₁ : IsConfPull ϕ W g τ₁) (h₂ : IsConfPull ϕ W g τ₂) :
    τ₁ = τ₂ :=
  TestFunction.ext fun x => (h₁ x).trans (h₂ x).symm

/-- The chosen pullback `confPull` (`Core/Interfaces.lean`) is the pullback. -/
theorem isConfPull_confPull (hϕ : IsConfNbhd ϕ W V) {g : TestC}
    (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' V) : IsConfPull ϕ W g (confPull ϕ W g) := by
  have hex : ∃ τg : TestC, IsConfPull ϕ W g τg := exists_confPull ϕ W V hϕ g hg
  unfold confPull
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem confPull_eq (hϕ : IsConfNbhd ϕ W V) {g τg : TestC} (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' V)
    (hτ : IsConfPull ϕ W g τg) : confPull ϕ W g = τg :=
  (isConfPull_confPull hϕ hg).eq hτ

/-- **T1, supports** (D1.1): `tsupport τg ⊆ ψ '' tsupport g`. -/
theorem IsConfPull.tsupport_subset (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z)
    {g τg : TestC} (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' V) (hτ : IsConfPull ϕ W g τg) :
    tsupport (τg : ℂ → ℝ) ⊆ ψ '' tsupport g := by
  rw [isConfPull_iff.1 hτ]
  exact tsupport_confPullFun_subset hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ
    g.hasCompactSupport (hg.trans hϕ.image_subset)

/-- **T1, supports** (D1.1): `ψ '' tsupport g ⊆ V`. -/
theorem IsConfNbhd.image_tsupport_subset (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z)
    {g : ℂ → ℝ} (hg : tsupport g ⊆ ϕ '' V) : ψ '' tsupport g ⊆ V :=
  leftInv_image_tsupport_subset hψ hϕ.subset hg

/-- `tsupport τg ⊆ V`. -/
theorem IsConfPull.tsupport_subset_V (hϕ : IsConfNbhd ϕ W V) {g τg : TestC}
    (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' V) (hτ : IsConfPull ϕ W g τg) :
    tsupport (τg : ℂ → ℝ) ⊆ V :=
  (hτ.tsupport_subset hϕ (fun _ hz => hϕ.injOn.leftInvOn_invFunOn hz) hg).trans
    (hϕ.image_tsupport_subset (fun _ hz => hϕ.injOn.leftInvOn_invFunOn hz) hg)

theorem IsConfNbhd.eq_zero_of_notMem_image (hϕ : IsConfNbhd ϕ W V) {g : ℂ → ℝ}
    (hg : tsupport g ⊆ ϕ '' V) {y : ℂ} (hy : y ∉ ϕ '' W) : g y = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hy (hϕ.image_subset (hg h))

/-- **T2** (D1.2): `∫ τg · u = ∫ g · (u ∘ ψ)` for every `u`. -/
theorem IsConfPull.integral_mul (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z)
    {g τg : TestC} (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' V) (hτ : IsConfPull ϕ W g τg)
    (u : ℂ → ℝ) : ∫ x, τg x * u x = ∫ y, g y * u (ψ y) := by
  rw [isConfPull_iff.1 hτ]
  exact integral_confPullFun_mul hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ
    (fun _ hy => hϕ.eq_zero_of_notMem_image hg hy) u

/-- **T2** (D1.2): `∫ τg = ∫ g`. -/
theorem IsConfPull.integral_eq (hϕ : IsConfNbhd ϕ W V) {g τg : TestC}
    (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' V) (hτ : IsConfPull ϕ W g τg) :
    ∫ x, τg x = ∫ y, g y := by
  rw [isConfPull_iff.1 hτ]
  exact integral_confPullFun hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn
    (fun _ hy => hϕ.eq_zero_of_notMem_image hg hy)

/-- **T2** (D1.2): `∫ log|ϕ'| · τg = -∫ log|ψ'| · g`. -/
theorem IsConfPull.integral_log_mul (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z)
    {g τg : TestC} (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' V) (hτ : IsConfPull ϕ W g τg) :
    ∫ x, Real.log ‖deriv ϕ x‖ * τg x = -∫ y, Real.log ‖deriv ψ y‖ * g y := by
  rw [isConfPull_iff.1 hτ]
  exact integral_log_mul_confPullFun hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ
    (fun _ hy => hϕ.eq_zero_of_notMem_image hg hy)

/-- **T3** (D1.3): if `τ_ψ g` is the `ψ`-pullback of `g` (supported in `W`) on `ϕ '' W`, then `g`
is the `ϕ`-pullback of `τ_ψ g`. -/
theorem IsConfPull.of_inv (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {g τψg : TestC} (hg : ∀ x ∉ W, g x = 0)
    (h₁ : IsConfPull ψ (ϕ '' W) g τψg) : IsConfPull ϕ W τψg g := by
  intro x
  have h := congrFun (confPullFun_confPullFun_leftInv hW hd hi hψ g) x
  rw [← isConfPull_iff.1 h₁] at h
  change g x = confPullFun ϕ W τψg x
  rw [h]
  by_cases hx : x ∈ W
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hg x hx]

/-- **T3** (D1.3): `τ_ϕ (τ_ψ g) = g` for `g` supported in `V`. -/
theorem IsConfPull.comp_inv (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z)
    {g τψg ττg : TestC} (hg : tsupport (g : ℂ → ℝ) ⊆ V) (h₁ : IsConfPull ψ (ϕ '' W) g τψg)
    (h₂ : IsConfPull ϕ W τψg ττg) : ττg = g :=
  h₂.eq (h₁.of_inv hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ fun _ hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hϕ.subset (hg h)))

/-- **T3, other order**: if `τg` is the `ϕ`-pullback of `g` (supported in `ϕ '' W`), then `g` is
the `ψ`-pullback of `τg` on `ϕ '' W`. -/
theorem IsConfPull.inv_of (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {g τg : TestC} (hg : ∀ y ∉ ϕ '' W, g y = 0)
    (h₁ : IsConfPull ϕ W g τg) : IsConfPull ψ (ϕ '' W) τg g := by
  intro y
  have h := congrFun (confPullFun_leftInv_confPullFun hW hd hi hψ g) y
  rw [← isConfPull_iff.1 h₁] at h
  change g y = confPullFun ψ (ϕ '' W) τg y
  rw [h]
  by_cases hy : y ∈ ϕ '' W
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, hg y hy]

end TestFunctions

end SmallGammaGeodesics.CC
