import SmallGammaGeodesics.NIC.Transport
import LQGMetric.Field.Green
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# NIC, part 1: conformal covariance of the Laplacian and `τ ρ_χ = ρ_{χ ∘ Φ}`

Packet P-G1, input to the key identity of T3 (GA2 D5 Step 4). GA2 proves `G φ_χ = φ_χ` with the
`E_θ`-Riesz representative of `ψ`. We use a shorter route: on the region where `Ψ = Φ⁻¹` is
holomorphic the transport of `ρ_χ = −Δχ/(2π)` (`LQGMetric.cmTest χ`) is again a Green density,

  `τ ρ_χ = ρ_{χ ∘ Φ}`   (`NearIdPair.transport_cmTest`, `tsupport χ ⊆ U`),

because the Laplacian is conformally covariant:

  `Δ(F ∘ Ψ)(z) = ‖Ψ'(z)‖² · (ΔF)(Ψ z)`   (`laplacian_comp_holomorphic`)

for `Ψ` holomorphic near `z`. Proof: the second derivative of a composition
(`fderiv_fderiv_comp`), `DΨ(z) m = m Ψ'(z)`, `ΔΨ = 0` (`AnalyticAt.harmonicAt`, so the
`DF(Ψz)(D²Ψ(z)(m, m))` terms cancel), and the identity
`B(a, a) + B(ia, ia) = ‖a‖² (B(1,1) + B(i,i))` for every real bilinear form (`bilin_scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Laplacian

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric

/-! ## A bilinear identity -/

theorem bilin_scale' (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (p q : ℝ) :
    B (p • (1 : ℂ) + q • Complex.I) (p • (1 : ℂ) + q • Complex.I) +
      B ((-q) • (1 : ℂ) + p • Complex.I) ((-q) • (1 : ℂ) + p • Complex.I) =
      (p ^ 2 + q ^ 2) * (B 1 1 + B Complex.I Complex.I) := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

/-- `B(a, a) + B(ia, ia) = ‖a‖² (B(1,1) + B(i,i))` for a real bilinear form `B` on `ℂ`. -/
theorem bilin_scale (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    B a a + B (Complex.I * a) (Complex.I * a) = ‖a‖ ^ 2 * (B 1 1 + B Complex.I Complex.I) := by
  have ea : a = a.re • (1 : ℂ) + a.im • Complex.I := by apply Complex.ext <;> simp
  have eb : Complex.I * a = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    apply Complex.ext <;> simp
  have hn : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  calc B a a + B (Complex.I * a) (Complex.I * a)
      = B (a.re • (1 : ℂ) + a.im • Complex.I) (a.re • (1 : ℂ) + a.im • Complex.I) +
        B ((-a.im) • (1 : ℂ) + a.re • Complex.I) ((-a.im) • (1 : ℂ) + a.re • Complex.I) := by
          rw [← ea, ← eb]
    _ = (a.re ^ 2 + a.im ^ 2) * (B 1 1 + B Complex.I Complex.I) := bilin_scale' B a.re a.im
    _ = ‖a‖ ^ 2 * (B 1 1 + B Complex.I Complex.I) := by rw [hn]

/-! ## Second derivative of a composition -/

lemma two_ne_zero' : (2 : WithTop ℕ∞) ≠ 0 := by norm_num

lemma one_add_one_le_two : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num

/-- `D²(F ∘ Ψ)(z)(m₀, m₁) = D²F(Ψ z)(DΨ(z) m₀, DΨ(z) m₁) + DF(Ψ z)(D²Ψ(z)(m₀, m₁))` -/
theorem fderiv_fderiv_comp {F : ℂ → ℝ} {Ψ : ℂ → ℂ} (hF : ContDiff ℝ 2 F) (hΨ : ContDiff ℝ 2 Ψ)
    (z m₀ m₁ : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => F (Ψ y))) z m₀ m₁ =
      fderiv ℝ (fderiv ℝ F) (Ψ z) (fderiv ℝ Ψ z m₀) (fderiv ℝ Ψ z m₁) +
        fderiv ℝ F (Ψ z) (fderiv ℝ (fderiv ℝ Ψ) z m₀ m₁) := by
  have hd1 : fderiv ℝ (fun y => F (Ψ y)) = fun y => (fderiv ℝ F (Ψ y)).comp (fderiv ℝ Ψ y) :=
    funext fun y => fderiv_comp (g := F) (f := Ψ) y (hF.differentiable two_ne_zero' (Ψ y))
      (hΨ.differentiable two_ne_zero' y)
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right one_add_one_le_two
  have hΨ1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right one_add_one_le_two
  have hc : HasFDerivAt (fun y => fderiv ℝ F (Ψ y))
      ((fderiv ℝ (fderiv ℝ F) (Ψ z)).comp (fderiv ℝ Ψ z)) z :=
    ((hF1.differentiable one_ne_zero (Ψ z)).hasFDerivAt).comp z
      ((hΨ.differentiable two_ne_zero' z).hasFDerivAt)
  have hd : HasFDerivAt (fun y => fderiv ℝ Ψ y) (fderiv ℝ (fderiv ℝ Ψ) z) z :=
    (hΨ1.differentiable one_ne_zero z).hasFDerivAt
  rw [hd1, (hc.clm_comp hd).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  rw [add_comm]

/-- `Δ f z = D²f(z)(1, 1) + D²f(z)(i, i)` -/
lemma laplacian_eq_fderiv_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z : ℂ) :
    Δ f z = fderiv ℝ (fderiv ℝ f) z 1 1 + fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp [iteratedFDeriv_two_apply]

/-- **Conformal covariance of the Laplacian**: `Δ(F ∘ Ψ)(z) = ‖Ψ'(z)‖² (ΔF)(Ψ z)` if `Ψ` is
holomorphic on an open `U ∋ z`. -/
theorem laplacian_comp_holomorphic {F : ℂ → ℝ} {Ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ContDiff ℝ 2 F) (hΨ2 : ContDiff ℝ 2 Ψ) (hΨ : DifferentiableOn ℂ Ψ U) {z : ℂ}
    (hz : z ∈ U) :
    Δ (fun y => F (Ψ y)) z = ‖deriv Ψ z‖ ^ 2 * Δ F (Ψ z) := by
  have hdz : HasDerivAt Ψ (deriv Ψ z) z :=
    ((hΨ z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hD : ∀ m : ℂ, fderiv ℝ Ψ z m = Complex.I ^ 0 * (m * deriv Ψ z) := fun m => by
    rw [(hdz.hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  have hD1 : fderiv ℝ Ψ z 1 = deriv Ψ z := by rw [hD]; simp
  have hDI : fderiv ℝ Ψ z Complex.I = Complex.I * deriv Ψ z := by rw [hD]; simp
  have hharm : Δ Ψ z = 0 :=
    ((hΨ.analyticAt (hU.mem_nhds hz)).harmonicAt).2.self_of_nhds
  rw [laplacian_eq_fderiv_fderiv] at hharm
  rw [laplacian_eq_fderiv_fderiv, laplacian_eq_fderiv_fderiv, fderiv_fderiv_comp hF hΨ2,
    fderiv_fderiv_comp hF hΨ2, hD1, hDI]
  have hlin : fderiv ℝ F (Ψ z) (fderiv ℝ (fderiv ℝ Ψ) z 1 1) +
      fderiv ℝ F (Ψ z) (fderiv ℝ (fderiv ℝ Ψ) z Complex.I Complex.I) = 0 := by
    rw [← map_add, hharm, map_zero]
  have key := bilin_scale (fderiv ℝ (fderiv ℝ F) (Ψ z)) (deriv Ψ z)
  linear_combination key + hlin

/-! ## The transport of a Green density -/

namespace NearIdPair

variable (D : NearIdPair)

lemma tsupport_compTest_subset (f : TestC) :
    tsupport (D.compTest f : ℂ → ℝ) ⊆ D.Ψ '' tsupport (f : ℂ → ℝ) := by
  refine closure_minimal ?_ (f.hasCompactSupport.isCompact.image D.continuous_inv).isClosed
  intro x hx
  exact ⟨D.Φ x, subset_tsupport _ hx, D.left_inv x⟩

/-- the Laplacian vanishes off the topological support -/
lemma laplacian_eq_zero_of_notMem_tsupport {f : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport f) :
    Δ f x = 0 := by
  have h : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [(InnerProductSpace.laplacian_congr_nhds h).self_of_nhds, InnerProductSpace.laplacian_const]
  rfl

/-- `jac Ψ (Φ x) = ‖Ψ'(Φ x)‖²` where `Ψ` is holomorphic -/
lemma jac_inv_eq_norm_deriv_sq {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U)
    {y : ℂ} (hy : y ∈ U) : jac D.Ψ y = ‖deriv D.Ψ y‖ ^ 2 := by
  have hdz : HasDerivAt D.Ψ (deriv D.Ψ y) y :=
    ((hΨ y hy).differentiableAt (hU.mem_nhds hy)).hasDerivAt
  rw [jac, (hdz.hasFDerivAt.restrictScalars ℝ).fderiv, det_restrictScalars_toSpanSingleton,
    abs_of_nonneg (sq_nonneg _)]

/-- **`τ ρ_χ = ρ_{χ ∘ Φ}`** for `χ` supported in the region `U` where `Ψ` is holomorphic. -/
theorem transport_cmTest {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U)
    (χ : TestC) (hχ : tsupport (χ : ℂ → ℝ) ⊆ U) :
    D.transport (cmTest χ) = cmTest (D.compTest χ) := by
  refine TestFunction.ext fun x => ?_
  rw [transport_apply, cmTest_apply, cmTest_apply]
  by_cases hx : D.Φ x ∈ U
  · -- `Δχ(Φ x) = ‖Ψ'(Φ x)‖² Δ(χ ∘ Φ)(x)` and `jac Φ x · ‖Ψ'(Φ x)‖² = 1`
    have hcov := laplacian_comp_holomorphic hU (contDiff_two_testC (D.compTest χ))
      (D.smooth_inv.of_le (by simp)) hΨ hx
    have e1 : (fun y => D.compTest χ (D.Ψ y)) = (χ : ℂ → ℝ) := funext fun y => by
      rw [compTest_apply, D.right_inv]
    rw [e1, D.left_inv] at hcov
    have hj : jac D.Ψ (D.Φ x) * jac D.Φ x = 1 := by
      simpa only [D.left_inv] using D.jac_inv_mul_jac (D.Φ x)
    rw [D.jac_inv_eq_norm_deriv_sq hU hΨ hx] at hj
    rw [hcov]
    have : jac D.Φ x * ‖deriv D.Ψ (D.Φ x)‖ ^ 2 = 1 := by rw [mul_comm]; exact hj
    linear_combination (-(2 * Real.pi)⁻¹ * Δ (⇑(D.compTest χ)) x) * this
  · have h1 : D.Φ x ∉ tsupport (χ : ℂ → ℝ) := fun h => hx (hχ h)
    have h2 : x ∉ tsupport (D.compTest χ : ℂ → ℝ) := by
      intro h
      obtain ⟨y, hy, hyx⟩ := D.tsupport_compTest_subset χ h
      apply h1
      rw [← hyx, D.right_inv]
      exact hy
    rw [laplacian_eq_zero_of_notMem_tsupport h1, laplacian_eq_zero_of_notMem_tsupport h2]
    ring

end NearIdPair

end NIC
end SmallGammaGeodesics
