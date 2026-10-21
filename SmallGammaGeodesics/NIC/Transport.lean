import LQGMetric.Statement.GFF
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Complex.Determinant
import SmallGammaGeodesics.Core.Interfaces

/-!
# NIC, part 1 (T1): transport of test functions by a near-identity diffeomorphism

Packet P-G1, target T1; GA2 `planning/audits/GA2-sections-3-4.md`, Details D5, Step 3, and
CC0 Details D5 (the general form `CC.NICInput`).

For a smooth diffeomorphism `Φ` of `ℂ` with smooth inverse `Ψ`, both within `δ` of the identity in
`C¹`, the **transport** of a test function is `τ g := |det DΦ| · (g ∘ Φ)`. Main results:

* `NearIdPair`: the symmetric bundle `(Φ, Ψ, δ)` with `‖DΦ − I‖, ‖DΨ − I‖ ≤ δ ≤ 1/16`;
  `NearIdPair.ofDiffeo` builds it with `δ = 2ε` from the interface hypothesis
  `CC.IsNearIdDiffeo Φ Ψ U ε`, `0 ≤ ε ≤ 1/32` (`norm_sub_id_le_of_comp_eq_id`:
  `‖DΨ − I‖ ≤ ε/(1 − ε) ≤ 2ε`);
* `NearIdPair.transport : TestC →ₗ[ℝ] TestC` and the linear equivalence `transportEquiv` whose
  inverse is the transport by `Ψ` (`transport_symm_transport`, `transport_transport_symm`);
* the change of variables `∫ τ g · u = ∫ g · (u ∘ Ψ)` for **every** `u : ℂ → ℝ`
  (`integral_transport_mul`), hence `∫ τ g = ∫ g` (`integral_transport`);
* `tsupport (τ g) ⊆ Ψ '' tsupport g` (`tsupport_transport_subset`);
* on `Ψ '' U`, where `Ψ` is holomorphic on the open `U`, `Φ` is holomorphic and
  `|det DΦ| = ‖Φ'‖²` (`differentiableOn_image`, `jac_eq_norm_deriv_sq`).

The determinant of a real-linear map of `ℂ` is computed in the basis `1, i` (`det_eq`), which gives
the bounds `1 − 2δ ≤ det DΦ ≤ 1 + 3δ` (`jac_mem_Icc`) and the smoothness of the Jacobian.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric

/-! ## Determinants of real-linear maps of `ℂ` -/

/-- `det L = Re(L 1) Im(L i) − Im(L 1) Re(L i)` (the matrix of `L` in the basis `1, i`). -/
theorem det_eq (L : ℂ →L[ℝ] ℂ) :
    L.det = (L 1).re * (L Complex.I).im - (L 1).im * (L Complex.I).re := by
  show LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]
  ring

/-- `det (A ∘ B) = det A · det B` -/
theorem det_comp (A B : ℂ →L[ℝ] ℂ) : (A.comp B).det = A.det * B.det := by
  show LinearMap.det ((A.comp B : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) *
    LinearMap.det (B : ℂ →ₗ[ℝ] ℂ)
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

theorem det_id : (ContinuousLinearMap.id ℝ ℂ).det = 1 := by
  show LinearMap.det ((ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = 1
  rw [ContinuousLinearMap.coe_id, LinearMap.det_id]

/-- Bounds for the determinant of a map `δ`-close to the identity. -/
theorem det_bounds {L : ℂ →L[ℝ] ℂ} {δ : ℝ} (hL : ‖L - ContinuousLinearMap.id ℝ ℂ‖ ≤ δ)
    (hδ : δ ≤ 1) : 1 - 2 * δ ≤ L.det ∧ L.det ≤ 1 + 2 * δ + 2 * δ ^ 2 := by
  set E := L - ContinuousLinearMap.id ℝ ℂ with hE
  have hv : ∀ v : ℂ, ‖v‖ = 1 → |(E v).re| ≤ δ ∧ |(E v).im| ≤ δ := fun v hv1 => by
    have h1 : ‖E v‖ ≤ δ := by
      calc ‖E v‖ ≤ ‖E‖ * ‖v‖ := E.le_opNorm v
        _ = ‖E‖ := by rw [hv1, mul_one]
        _ ≤ δ := hL
    exact ⟨(Complex.abs_re_le_norm _).trans h1, (Complex.abs_im_le_norm _).trans h1⟩
  obtain ⟨ha, hb⟩ := hv 1 (by simp)
  obtain ⟨hc, hd⟩ := hv Complex.I (by simp)
  have e1 : L 1 = 1 + E 1 := by simp [hE]
  have eI : L Complex.I = Complex.I + E Complex.I := by simp [hE]
  rw [det_eq, e1, eI]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im]
  set a := (E 1).re
  set b := (E 1).im
  set c := (E Complex.I).re
  set d := (E Complex.I).im
  rw [abs_le] at ha hb hc hd
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (abs_le.2 ha)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (show 1 - δ ≤ 1 + d by linarith)
      (show (0 : ℝ) ≤ 1 - δ by linarith), mul_le_mul_of_nonneg_right (show 1 - δ ≤ 1 + a by linarith)
      (show (0 : ℝ) ≤ 1 + d by linarith), mul_le_mul_of_nonneg_left hb.2 hδ0,
      mul_le_mul_of_nonneg_right hc.2 hδ0, abs_mul_abs_self b, abs_le.2 hb, abs_le.2 hc,
      abs_mul b c, mul_le_mul (abs_le.2 hb) (abs_le.2 hc) (abs_nonneg c) hδ0, le_abs_self (b * c)]
  · nlinarith [mul_le_mul (show 1 + a ≤ 1 + δ by linarith) (show 1 + d ≤ 1 + δ by linarith)
      (show (0 : ℝ) ≤ 1 + d by linarith) (show (0 : ℝ) ≤ 1 + δ by linarith),
      abs_mul b c, mul_le_mul (abs_le.2 hb) (abs_le.2 hc) (abs_nonneg c) hδ0, neg_abs_le (b * c)]

/-- If `L ∘ M = id` and `‖L − I‖ ≤ ε ≤ 1/2`, then `‖M − I‖ ≤ 2ε`. -/
theorem norm_sub_id_le_of_comp_eq_id {L M : ℂ →L[ℝ] ℂ}
    (hLM : L.comp M = ContinuousLinearMap.id ℝ ℂ) {ε : ℝ}
    (hL : ‖L - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε) (hε : ε ≤ 1 / 2) :
    ‖M - ContinuousLinearMap.id ℝ ℂ‖ ≤ 2 * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hL
  have key : M - ContinuousLinearMap.id ℝ ℂ = -((L - ContinuousLinearMap.id ℝ ℂ).comp M) := by
    ext1 v
    have hv : L (M v) = v := by
      simpa using congrArg (fun T : ℂ →L[ℝ] ℂ => T v) hLM
    simp only [sub_apply, ContinuousLinearMap.id_apply, neg_apply,
      ContinuousLinearMap.comp_apply, hv]
    abel
  have h1 : ‖M - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε * ‖M‖ := by
    rw [key, norm_neg]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have h2 : ‖M‖ ≤ ‖M - ContinuousLinearMap.id ℝ ℂ‖ + 1 := by
    calc ‖M‖ = ‖(M - ContinuousLinearMap.id ℝ ℂ) + ContinuousLinearMap.id ℝ ℂ‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖M - ContinuousLinearMap.id ℝ ℂ‖ + ‖ContinuousLinearMap.id ℝ ℂ‖ := norm_add_le _ _
      _ ≤ ‖M - ContinuousLinearMap.id ℝ ℂ‖ + 1 := by
          gcongr; exact ContinuousLinearMap.norm_id_le
  set x := ‖M - ContinuousLinearMap.id ℝ ℂ‖
  have hx : x ≤ ε * (x + 1) := h1.trans (mul_le_mul_of_nonneg_left h2 hε0)
  nlinarith [norm_nonneg (M - ContinuousLinearMap.id ℝ ℂ)]

/-! ## Near-identity diffeomorphism pairs -/

lemma smooth_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp

lemma smooth_succ_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  simp

/-- A smooth near-identity diffeomorphism pair in symmetric form: `Φ` and its inverse `Ψ` are
`C^∞`, and both derivatives are within `δ ≤ 1/16` of the identity. -/
structure NearIdPair where
  /-- the diffeomorphism -/
  Φ : ℂ → ℂ
  /-- its inverse -/
  Ψ : ℂ → ℂ
  /-- the `C¹` distance to the identity -/
  δ : ℝ
  δ_nonneg : 0 ≤ δ
  δ_le : δ ≤ 1 / 16
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  smooth_inv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ
  left_inv : ∀ z, Ψ (Φ z) = z
  right_inv : ∀ z, Φ (Ψ z) = z
  deriv_close : ∀ z, ‖fderiv ℝ Φ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ δ
  deriv_close_inv : ∀ z, ‖fderiv ℝ Ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ δ

namespace NearIdPair

variable (D : NearIdPair)

/-- the inverse pair `(Ψ, Φ)` -/
def symm : NearIdPair where
  Φ := D.Ψ
  Ψ := D.Φ
  δ := D.δ
  δ_nonneg := D.δ_nonneg
  δ_le := D.δ_le
  smooth := D.smooth_inv
  smooth_inv := D.smooth
  left_inv := D.right_inv
  right_inv := D.left_inv
  deriv_close := D.deriv_close_inv
  deriv_close_inv := D.deriv_close

@[simp] lemma symm_Φ : D.symm.Φ = D.Ψ := rfl
@[simp] lemma symm_Ψ : D.symm.Ψ = D.Φ := rfl
@[simp] lemma symm_δ : D.symm.δ = D.δ := rfl
@[simp] lemma symm_symm : D.symm.symm = D := rfl

lemma differentiable : Differentiable ℝ D.Φ := D.smooth.differentiable smooth_ne_zero

lemma continuous : Continuous D.Φ := D.smooth.continuous

lemma continuous_inv : Continuous D.Ψ := D.smooth_inv.continuous

lemma injective : Function.Injective D.Φ := fun x y h => by
  rw [← D.left_inv x, ← D.left_inv y, h]

lemma surjective : Function.Surjective D.Φ := fun y => ⟨D.Ψ y, D.right_inv y⟩

lemma range_eq : range D.Φ = univ := D.surjective.range_eq

lemma image_inv_eq_preimage (s : Set ℂ) : D.Ψ '' s = D.Φ ⁻¹' s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_preimage, D.right_inv]; exact hy
  · intro hx
    exact ⟨D.Φ x, hx, D.left_inv x⟩

/-- the chain rule for `Φ ∘ Ψ = id`: `DΦ(Ψ z) ∘ DΨ(z) = I` -/
lemma fderiv_comp_fderiv_inv (z : ℂ) :
    (fderiv ℝ D.Φ (D.Ψ z)).comp (fderiv ℝ D.Ψ z) = ContinuousLinearMap.id ℝ ℂ := by
  have h := fderiv_comp z (D.differentiable (D.Ψ z)) (D.symm.differentiable z)
  have hid : D.Φ ∘ D.Ψ = id := funext D.right_inv
  rw [hid, fderiv_id] at h
  exact h.symm

/-- `fderiv ℝ Φ` is smooth -/
lemma contDiff_fderiv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ D.Φ) :=
  D.smooth.fderiv_right smooth_succ_le

lemma det_mem_Icc (z : ℂ) : 1 - 2 * D.δ ≤ (fderiv ℝ D.Φ z).det ∧
    (fderiv ℝ D.Φ z).det ≤ 1 + 3 * D.δ := by
  obtain ⟨h1, h2⟩ := det_bounds (D.deriv_close z) (by linarith [D.δ_le])
  refine ⟨h1, h2.trans ?_⟩
  nlinarith [D.δ_le, D.δ_nonneg]

lemma det_pos (z : ℂ) : 0 < (fderiv ℝ D.Φ z).det := by
  linarith [(D.det_mem_Icc z).1, D.δ_le]

end NearIdPair

/-! ## The Jacobian -/

/-- the Jacobian `|det DΦ(x)|` -/
def jac (Φ : ℂ → ℂ) (x : ℂ) : ℝ := |(fderiv ℝ Φ x).det|

/-- the form used in `CC.NICInput` -/
lemma jac_def (Φ : ℂ → ℂ) (x : ℂ) :
    jac Φ x = |LinearMap.det (fderiv ℝ Φ x : ℂ →ₗ[ℝ] ℂ)| := rfl

namespace NearIdPair

variable (D : NearIdPair)

lemma jac_eq_det (x : ℂ) : jac D.Φ x = (fderiv ℝ D.Φ x).det := abs_of_pos (D.det_pos x)

lemma jac_mem_Icc (x : ℂ) : 1 - 2 * D.δ ≤ jac D.Φ x ∧ jac D.Φ x ≤ 1 + 3 * D.δ := by
  rw [D.jac_eq_det]; exact D.det_mem_Icc x

lemma jac_pos (x : ℂ) : 0 < jac D.Φ x := by rw [D.jac_eq_det]; exact D.det_pos x

lemma jac_le (x : ℂ) : jac D.Φ x ≤ 1 + 3 * D.δ := (D.jac_mem_Icc x).2

/-- `|det DΨ(y)| · |det DΦ(Ψ y)| = 1` -/
lemma jac_inv_mul_jac (y : ℂ) : jac D.Ψ y * jac D.Φ (D.Ψ y) = 1 := by
  rw [jac, jac, ← abs_mul, mul_comm, ← det_comp, D.fderiv_comp_fderiv_inv, det_id, abs_one]

lemma contDiff_jac : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (jac D.Φ) := by
  have e : jac D.Φ = fun x => (fderiv ℝ D.Φ x 1).re * (fderiv ℝ D.Φ x Complex.I).im -
      (fderiv ℝ D.Φ x 1).im * (fderiv ℝ D.Φ x Complex.I).re := by
    funext x; rw [D.jac_eq_det, det_eq]
  rw [e]
  have hv : ∀ v : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fderiv ℝ D.Φ x v) := fun v =>
    D.contDiff_fderiv.clm_apply contDiff_const
  have hre : ∀ v : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (fderiv ℝ D.Φ x v).re) :=
    fun v => Complex.reCLM.contDiff.comp (hv v)
  have him : ∀ v : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (fderiv ℝ D.Φ x v).im) :=
    fun v => Complex.imCLM.contDiff.comp (hv v)
  exact ((hre 1).mul (him Complex.I)).sub ((him 1).mul (hre Complex.I))

lemma continuous_jac : Continuous (jac D.Φ) := D.contDiff_jac.continuous

/-! ## Composition and transport of test functions -/

/-- `f ∘ Φ` as a test function (it is supported in `Ψ '' tsupport f`). -/
def compTest (f : TestC) : TestC where
  toFun := fun x => f (D.Φ x)
  contDiff' := f.contDiff.comp D.smooth
  hasCompactSupport' := by
    refine HasCompactSupport.intro (f.hasCompactSupport.isCompact.image D.continuous_inv) ?_
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun h => hx ⟨D.Φ x, h, D.left_inv x⟩
  tsupport_subset' := subset_univ _

@[simp] lemma compTest_apply (f : TestC) (x : ℂ) : D.compTest f x = f (D.Φ x) := rfl

end NearIdPair

/-- `τ g := |det DΦ| · (g ∘ Φ)` as a function -/
def transportFun (Φ : ℂ → ℂ) (g : ℂ → ℝ) (x : ℂ) : ℝ := jac Φ x * g (Φ x)

namespace NearIdPair

variable (D : NearIdPair)

/-- `τ g` as a test function -/
def transportTest (g : TestC) : TestC where
  toFun := transportFun D.Φ g
  contDiff' := D.contDiff_jac.mul (D.compTest g).contDiff
  hasCompactSupport' := (D.compTest g).hasCompactSupport.mul_left
  tsupport_subset' := subset_univ _

/-- **The transport** `τ g = |det DΦ| · (g ∘ Φ)` on `𝓓(ℂ)` (GA2 D5 Step 3). -/
def transport : TestC →ₗ[ℝ] TestC where
  toFun := D.transportTest
  map_add' f g := TestFunction.ext fun x => by
    show jac D.Φ x * (f (D.Φ x) + g (D.Φ x)) = jac D.Φ x * f (D.Φ x) + jac D.Φ x * g (D.Φ x)
    ring
  map_smul' c f := TestFunction.ext fun x => by
    show jac D.Φ x * (c * f (D.Φ x)) = c * (jac D.Φ x * f (D.Φ x))
    ring

lemma transport_apply (g : TestC) (x : ℂ) : D.transport g x = jac D.Φ x * g (D.Φ x) := rfl

lemma coe_transport (g : TestC) : (D.transport g : ℂ → ℝ) = transportFun D.Φ g := rfl

/-- the transport by `Ψ` inverts the transport by `Φ` -/
theorem transport_symm_transport (g : TestC) : D.symm.transport (D.transport g) = g :=
  TestFunction.ext fun y => by
    show jac D.Ψ y * (jac D.Φ (D.Ψ y) * g (D.Φ (D.Ψ y))) = g y
    rw [D.right_inv, ← mul_assoc, D.jac_inv_mul_jac, one_mul]

theorem transport_transport_symm (g : TestC) : D.transport (D.symm.transport g) = g :=
  D.symm.transport_symm_transport g

/-- **T1 (bijectivity)**: `τ` is a linear equivalence of `𝓓(ℂ)`, with inverse the transport by `Ψ`. -/
def transportEquiv : TestC ≃ₗ[ℝ] TestC :=
  { D.transport with
    invFun := D.symm.transport
    left_inv := D.transport_symm_transport
    right_inv := D.transport_transport_symm }

@[simp] lemma transportEquiv_apply (g : TestC) : D.transportEquiv g = D.transport g := rfl

@[simp] lemma transportEquiv_symm_apply (g : TestC) :
    D.transportEquiv.symm g = D.symm.transport g := rfl

/-- **T1 (change of variables)**: `∫ τ g · u = ∫ g · (u ∘ Ψ)` for all functions `g, u`. -/
theorem integral_transportFun_mul (g u : ℂ → ℝ) :
    ∫ x, transportFun D.Φ g x * u x = ∫ y, g y * u (D.Ψ y) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (f := D.Φ) (f' := fderiv ℝ D.Φ)
    (fun x _ => (D.differentiable x).hasFDerivAt.hasFDerivWithinAt) D.injective.injOn
    (fun y => g y * u (D.Ψ y))
  rw [image_univ, D.range_eq, Measure.restrict_univ] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, D.left_inv, transportFun, jac]
  ring

theorem integral_transport_mul (g : TestC) (u : ℂ → ℝ) :
    ∫ x, D.transport g x * u x = ∫ y, g y * u (D.Ψ y) :=
  D.integral_transportFun_mul g u

/-- **T1 (mass)**: `∫ τ g = ∫ g`; in particular `τ` preserves mean-zero test functions. -/
theorem integral_transport (g : TestC) : ∫ x, D.transport g x = ∫ x, g x := by
  simpa only [mul_one] using D.integral_transport_mul g (fun _ => 1)

/-- **T1 (support)**: `tsupport (τ g) ⊆ Ψ '' tsupport g`. -/
theorem tsupport_transport_subset (g : TestC) :
    tsupport (D.transport g : ℂ → ℝ) ⊆ D.Ψ '' tsupport (g : ℂ → ℝ) := by
  refine closure_minimal ?_ (g.hasCompactSupport.isCompact.image D.continuous_inv).isClosed
  intro x hx
  have hgx : g (D.Φ x) ≠ 0 := fun h0 => hx (by rw [transport_apply, h0, mul_zero])
  exact ⟨D.Φ x, subset_tsupport _ hgx, D.left_inv x⟩

/-! ## The holomorphic region -/

/-- `Ψ '' U = Φ⁻¹(U)` is open when `U` is. -/
lemma isOpen_image_inv {U : Set ℂ} (hU : IsOpen U) : IsOpen (D.Ψ '' U) := by
  rw [D.image_inv_eq_preimage]; exact hU.preimage D.continuous

/-- If `Ψ` is holomorphic on the open `U`, then `Φ` has complex derivative `1/Ψ'(Φ x)` at every
`x ∈ Ψ '' U`. -/
theorem hasDerivAt_of_mem_image {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U)
    {x : ℂ} (hx : x ∈ D.Ψ '' U) : HasDerivAt D.Φ (deriv D.Ψ (D.Φ x))⁻¹ x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [D.right_inv]
  have hd : HasDerivAt D.Ψ (deriv D.Ψ y) y :=
    ((hΨ y hy).differentiableAt (hU.mem_nhds hy)).hasDerivAt
  have hne : deriv D.Ψ y ≠ 0 := by
    intro h0
    have hf : fderiv ℝ D.Ψ y = 0 := by
      rw [(hd.hasFDerivAt.restrictScalars ℝ).fderiv]
      ext1 v
      simp [h0]
    have h1 := D.fderiv_comp_fderiv_inv y
    rw [hf, ContinuousLinearMap.comp_zero] at h1
    have h2 := congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) h1
    simp at h2
  have hd' : HasDerivAt D.Ψ (deriv D.Ψ y) (D.Φ (D.Ψ y)) := by rw [D.right_inv]; exact hd
  exact HasDerivAt.of_local_left_inverse D.continuous.continuousAt hd' hne
    (Eventually.of_forall D.left_inv)

/-- **T1 (holomorphy)**: `Φ` is holomorphic on `Ψ '' U`. -/
theorem differentiableOn_image {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U) :
    DifferentiableOn ℂ D.Φ (D.Ψ '' U) := fun _ hx =>
  (D.hasDerivAt_of_mem_image hU hΨ hx).differentiableAt.differentiableWithinAt

/-- `det L = ‖c‖²` for the real-linear map `z ↦ z c` -/
theorem det_restrictScalars_toSpanSingleton (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  rw [det_eq, Complex.sq_norm, Complex.normSq_apply]
  simp

/-- **T1 (conformal Jacobian)**: on `Ψ '' U`, `|det DΦ| = ‖Φ'‖²`. -/
theorem jac_eq_norm_deriv_sq {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U)
    {x : ℂ} (hx : x ∈ D.Ψ '' U) : jac D.Φ x = ‖deriv D.Φ x‖ ^ 2 := by
  have hc : HasDerivAt D.Φ (deriv D.Φ x) x :=
    (D.hasDerivAt_of_mem_image hU hΨ hx).differentiableAt.hasDerivAt
  rw [jac, (hc.hasFDerivAt.restrictScalars ℝ).fderiv, det_restrictScalars_toSpanSingleton,
    abs_of_nonneg (sq_nonneg _)]

end NearIdPair

/-! ## From the interface hypothesis -/

/-- the chain rule for a right inverse: `DΦ(Ψ z) ∘ DΨ(z) = I` -/
lemma fderiv_comp_fderiv_of_rightInverse {Φ Ψ : ℂ → ℂ}
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (h : ∀ z, Φ (Ψ z) = z) (z : ℂ) :
    (fderiv ℝ Φ (Ψ z)).comp (fderiv ℝ Ψ z) = ContinuousLinearMap.id ℝ ℂ := by
  have hc := fderiv_comp z (hΦ.differentiable smooth_ne_zero (Ψ z))
    (hΨ.differentiable smooth_ne_zero z)
  have hid : Φ ∘ Ψ = id := funext h
  rw [hid, fderiv_id] at hc
  exact hc.symm

/-- **The symmetric pair of a near-identity diffeomorphism** (`CC.IsNearIdDiffeo`, `0 ≤ ε ≤ 1/32`):
`δ = 2ε`, using `‖DΨ − I‖ ≤ ε/(1 − ε) ≤ 2ε`. -/
def NearIdPair.ofDiffeo {Φ Ψ : ℂ → ℂ} {U : Set ℂ} {ε : ℝ} (h : CC.IsNearIdDiffeo Φ Ψ U ε)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 32) : NearIdPair where
  Φ := Φ
  Ψ := Ψ
  δ := 2 * ε
  δ_nonneg := by linarith
  δ_le := by linarith
  smooth := h.contDiff
  smooth_inv := h.contDiff_inv
  left_inv := h.left_inv
  right_inv := h.right_inv
  deriv_close z := (h.deriv_close z).trans (by linarith)
  deriv_close_inv z := norm_sub_id_le_of_comp_eq_id
    (fderiv_comp_fderiv_of_rightInverse h.contDiff h.contDiff_inv h.right_inv z)
    (h.deriv_close (Ψ z)) (by linarith)

section ofDiffeo

variable {Φ Ψ : ℂ → ℂ} {U : Set ℂ} {ε : ℝ} (h : CC.IsNearIdDiffeo Φ Ψ U ε) (hε0 : 0 ≤ ε)
  (hε : ε ≤ 1 / 32)

@[simp] lemma NearIdPair.ofDiffeo_Φ : (NearIdPair.ofDiffeo h hε0 hε).Φ = Φ := rfl
@[simp] lemma NearIdPair.ofDiffeo_Ψ : (NearIdPair.ofDiffeo h hε0 hε).Ψ = Ψ := rfl
@[simp] lemma NearIdPair.ofDiffeo_δ : (NearIdPair.ofDiffeo h hε0 hε).δ = 2 * ε := rfl

/-- the transport of the interface: `τ g x = |det DΦ(x)| g(Φ x)` -/
lemma NearIdPair.ofDiffeo_transport_apply (g : TestC) (x : ℂ) :
    (NearIdPair.ofDiffeo h hε0 hε).transport g x =
      |LinearMap.det (fderiv ℝ Φ x : ℂ →ₗ[ℝ] ℂ)| * g (Φ x) := rfl

end ofDiffeo

end NIC
end SmallGammaGeodesics
