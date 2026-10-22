import HigherDimLQGMetric.Field.Basic
import HigherDimLQGMetric.Frozen.AffineComp
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# Affine pullbacks on `ℝ^d`: `testAffinePull`, `affineComp`, change of variables

Packet F1. Port of LQGMetric's 2D affine layer (`lqg_metric/LQGMetric/Statement/Field.lean`:
`affMap`, `affLin`, `affK`, `pullK`, `continuous_pullK`, `testAffinePull_apply`;
`Field/GFFInvariance.lean`: `integral_comp_aff`, `integral_testAffinePull`, `affineComp_apply`,
`pull0`; `Papers/GM/S1/Dilate.lean`: `affineComp_ofCont`, `affineComp_add`, `affineComp_addFun`,
`affineComp_comp`; `Papers/GM/S1/WeakStrong.lean`: `affineComp_one_zero`, `affineComp_inv_self`;
`Papers/DFGPS/MarkovNorm.lean`: `affInvC_affineComp`; `Field/ZeroBoundaryAffine.lean`,
`Field/ZeroBoundaryField.lean`: `affOpens`, `testPullOn`, `distAffine`) from `ℂ` to `Rd d`
(ruling M10). The factor `r⁻²` of the plane becomes `r^{-d}`.

For `r ≠ 0` the frozen `testAffinePull r z φ` is `φ((· - z)/r)` (`testAffinePull_apply`) and
`affineComp r z h` is `h(r · + z)`, `⟨h(r·+z), φ⟩ = r^{-d} ⟨h, φ((·-z)/r)⟩`:

* change of variables (`integral_comp_affinePt`, `integral_comp_affMap`,
  `integral_testAffinePull`, `integral_testAffinePull_mul`), which is exactly the `r^{-d}`
  normalization: `affineComp_ofCont` (`affineComp r z (ofCont f) = ofCont (f(r · + z))`, `r > 0`);
* composition and inverse: `testAffinePull_testAffinePull`, `affineComp_affineComp`
  (`h(r₂·+z₂)(r₁·+z₁) = h(r₂r₁·+r₂z₁+z₂)`, no hypothesis), `affineComp_one_zero`,
  `affineComp_inv_affineComp`, `affineComp_affineComp_inv`, `affineComp_bijective`;
* linearity in `h`, `affineComp_addFun`, `affineComp_addConst` (`r > 0`);
* supports: `tsupport_testAffinePull` (`= r · tsupport φ + z`), mean-zero test functions are
  preserved (`testAffinePull0`);
* the affine pullback between open sets: `preOpens r z V = {x | r x + z ∈ V}`, `testPullOn`,
  `distAffine`, and `restrictTo_affineComp`: `h(r·+z)|_{preOpens r z V}` is the affine image of
  `h|_V` (so the restriction of `h(r·+z)` to `preOpens r z V` only depends on `h|_V`).

Standard facts; own elementary proofs as in the 2D layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Function TopologicalSpace
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem finrank_rd (d : ℕ) : Module.finrank ℝ (Rd d) = d := finrank_euclideanSpace_fin

/-! ### The affine maps -/

/-- `x ↦ r x + z`, the map whose pullback is `affineComp r z`. -/
def affinePt (r : ℝ) (z : Rd d) : C(Rd d, Rd d) := ⟨fun x => r • x + z, by fun_prop⟩

@[simp]
theorem affinePt_apply (r : ℝ) (z x : Rd d) : affinePt r z x = r • x + z := rfl

/-- `x ↦ (x - z)/r`, written `r⁻¹ • (x + -z)` as in the frozen `testAffinePull`. -/
def affMap (r : ℝ) (z : Rd d) (x : Rd d) : Rd d := r⁻¹ • (x + -z)

theorem affMap_eq (r : ℝ) (z x : Rd d) : affMap r z x = r⁻¹ • (x - z) := by
  rw [affMap, sub_eq_add_neg]

theorem continuous_affMap (r : ℝ) (z : Rd d) : Continuous (affMap r z) := by
  unfold affMap; fun_prop

theorem affMap_affinePt {r : ℝ} (hr : r ≠ 0) (z x : Rd d) : affMap r z (r • x + z) = x := by
  rw [affMap_eq, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem affinePt_affMap {r : ℝ} (hr : r ≠ 0) (z x : Rd d) : r • affMap r z x + z = x := by
  rw [affMap_eq, smul_smul, mul_inv_cancel₀ hr, one_smul, sub_add_cancel]

/-- `x ↦ r x + z` as a homeomorphism (`r ≠ 0`). -/
def affineHomeomorph (r : ℝ) (hr : r ≠ 0) (z : Rd d) : Rd d ≃ₜ Rd d :=
  (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addRight z)

@[simp]
theorem affineHomeomorph_apply {r : ℝ} (hr : r ≠ 0) (z x : Rd d) :
    affineHomeomorph r hr z x = r • x + z := rfl

@[simp]
theorem affineHomeomorph_symm_apply {r : ℝ} (hr : r ≠ 0) (z x : Rd d) :
    (affineHomeomorph r hr z).symm x = affMap r z x := by
  rw [Homeomorph.symm_apply_eq, affineHomeomorph_apply, affinePt_affMap hr]

/-- The linear part `r⁻¹ • id` of `affMap`. -/
def affLin (r : ℝ) : Rd d →L[ℝ] Rd d := r⁻¹ • ContinuousLinearMap.id ℝ (Rd d)

theorem comp_affMap_eq (r : ℝ) (z : Rd d) (φ : Rd d → ℝ) :
    φ ∘ affMap r z = fun y => (φ ∘ affLin r) (y + -z) := by
  ext y; simp [affMap, affLin]

theorem contDiff_comp_affMap (r : ℝ) (z : Rd d) {φ : Rd d → ℝ} {n : ℕ∞}
    (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (φ ∘ affMap r z) := by
  rw [comp_affMap_eq]
  exact (hφ.comp (affLin r).contDiff).comp (contDiff_id.add contDiff_const)

theorem iteratedFDeriv_comp_affMap (r : ℝ) (z : Rd d) {φ : Rd d → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (i : ℕ) (x : Rd d) :
    iteratedFDeriv ℝ i (φ ∘ affMap r z) x =
      (iteratedFDeriv ℝ i φ (affMap r z x)).compContinuousLinearMap fun _ => affLin r := by
  rw [comp_affMap_eq, iteratedFDeriv_comp_add_right,
    (affLin r).iteratedFDeriv_comp_right hφ _ (by exact_mod_cast le_top)]
  rfl

theorem hasCompactSupport_comp_affMap {r : ℝ} (hr : r ≠ 0) (z : Rd d) {φ : Rd d → ℝ}
    (hφ : HasCompactSupport φ) : HasCompactSupport (φ ∘ affMap r z) := by
  have e : φ ∘ affMap r z = φ ∘ (affineHomeomorph r hr z).symm := by
    funext x; simp only [comp_apply, affineHomeomorph_symm_apply]
  rw [e]
  exact hφ.comp_homeomorph _

/-! ### `testAffinePull` -/

theorem testAffinePull_of_ne {r : ℝ} (hr : r ≠ 0) (z : Rd d) (φ : TestRd d) :
    ⇑(testAffinePull r z φ) = φ ∘ affMap r z := by
  rw [testAffinePull, dite_eq_right hr]
  rfl

/-- `testAffinePull r z φ = φ((· - z)/r)` for `r ≠ 0`. -/
theorem testAffinePull_apply {r : ℝ} (hr : r ≠ 0) (z : Rd d) (φ : TestRd d) (x : Rd d) :
    testAffinePull r z φ x = φ (r⁻¹ • (x - z)) := by
  rw [testAffinePull_of_ne hr, comp_apply, affMap_eq]

theorem testAffinePull_apply_affinePt {r : ℝ} (hr : r ≠ 0) (z : Rd d) (φ : TestRd d)
    (x : Rd d) : testAffinePull r z φ (r • x + z) = φ x := by
  rw [testAffinePull_of_ne hr, comp_apply, affMap_affinePt hr]

/-- The `r = 0` branch (never used by the frozen statements) is the zero map. -/
@[simp]
theorem testAffinePull_zero_left (z : Rd d) : testAffinePull 0 z = 0 := by
  rw [testAffinePull, dite_eq_left rfl]

theorem testAffinePull_one_apply (z : Rd d) (φ : TestRd d) (x : Rd d) :
    testAffinePull 1 z φ x = φ (x - z) := by
  rw [testAffinePull_apply one_ne_zero, inv_one, one_smul]

@[simp]
theorem testAffinePull_one_zero : testAffinePull (1 : ℝ) (0 : Rd d) = ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext fun φ => TestFunction.ext fun x => by
    rw [testAffinePull_one_apply, sub_zero, ContinuousLinearMap.id_apply]

/-- Composition: `φ((·-z₁)/r₁)((·-z₂)/r₂) = φ((· - (r₂z₁+z₂))/(r₂r₁))`; holds for all `r₁, r₂`
(both sides vanish if one of them is `0`). -/
theorem testAffinePull_testAffinePull (r₁ r₂ : ℝ) (z₁ z₂ : Rd d) (φ : TestRd d) :
    testAffinePull r₂ z₂ (testAffinePull r₁ z₁ φ) =
      testAffinePull (r₂ * r₁) (r₂ • z₁ + z₂) φ := by
  rcases eq_or_ne r₁ 0 with rfl | h₁
  · simp
  rcases eq_or_ne r₂ 0 with rfl | h₂
  · simp
  refine TestFunction.ext fun x => ?_
  rw [testAffinePull_apply h₂, testAffinePull_apply h₁, testAffinePull_apply (mul_ne_zero h₂ h₁)]
  congr 1
  have e1 : (r₂ * r₁)⁻¹ = r₁⁻¹ * r₂⁻¹ := mul_inv_rev r₂ r₁
  have e2 : (r₂ * r₁)⁻¹ * r₂ = r₁⁻¹ := by rw [e1, mul_assoc, inv_mul_cancel₀ h₂, mul_one]
  calc r₁⁻¹ • (r₂⁻¹ • (x - z₂) - z₁) = (r₁⁻¹ * r₂⁻¹) • (x - z₂) - r₁⁻¹ • z₁ := by
        rw [smul_sub r₁⁻¹ (r₂⁻¹ • (x - z₂)) z₁, smul_smul]
    _ = (r₂ * r₁)⁻¹ • (x - (r₂ • z₁ + z₂)) := by
        rw [show x - (r₂ • z₁ + z₂) = (x - z₂) - r₂ • z₁ by abel,
          smul_sub ((r₂ * r₁)⁻¹) (x - z₂) (r₂ • z₁), smul_smul, e2, e1]

/-- The support of `φ((·-z)/r)` is `r · tsupport φ + z`. -/
theorem tsupport_testAffinePull {r : ℝ} (hr : r ≠ 0) (z : Rd d) (φ : TestRd d) :
    tsupport (⇑(testAffinePull r z φ)) = affinePt r z '' tsupport (⇑φ) := by
  have e : ⇑(testAffinePull r z φ) = ⇑φ ∘ (affineHomeomorph r hr z).symm := by
    rw [testAffinePull_of_ne hr]
    funext x; simp only [comp_apply, affineHomeomorph_symm_apply]
  rw [e, tsupport_comp_eq_preimage, Homeomorph.preimage_symm]
  rfl

theorem support_testAffinePull {r : ℝ} (hr : r ≠ 0) (z : Rd d) (φ : TestRd d) :
    support (⇑(testAffinePull r z φ)) = affinePt r z '' support (⇑φ) := by
  have e : ⇑(testAffinePull r z φ) = ⇑φ ∘ (affineHomeomorph r hr z).symm := by
    rw [testAffinePull_of_ne hr]
    funext x; simp only [comp_apply, affineHomeomorph_symm_apply]
  rw [e, support_comp_eq_preimage, Homeomorph.preimage_symm]
  rfl

theorem tsupport_testAffinePull_subset_iff {r : ℝ} (hr : r ≠ 0) (z : Rd d) (φ : TestRd d)
    (V : Set (Rd d)) :
    tsupport (⇑(testAffinePull r z φ)) ⊆ V ↔ tsupport (⇑φ) ⊆ affinePt r z ⁻¹' V := by
  rw [tsupport_testAffinePull hr, image_subset_iff]

/-! ### Change of variables -/

/-- `∫ F(r x + z) dx = r^{-d} ∫ F` for `r > 0`. -/
theorem integral_comp_affinePt (F : Rd d → ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ∫ x, F (r • x + z) = (r ^ d)⁻¹ * ∫ y, F y := by
  have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure (Rd d))
    (fun w => F (w + z)) r (hR := hr.le)
  rw [finrank_rd, integral_add_right_eq_self (fun w => F w) z, smul_eq_mul] at h1
  exact h1

/-- `∫ F(r x + z) dx = |r|^{-d} ∫ F`, for every `r` (for `r = 0` and `d ≥ 1` both sides vanish:
Bochner's convention on the non-integrable constant, and `0⁻¹ = 0`). -/
theorem integral_comp_affinePt_abs (F : Rd d → ℝ) (r : ℝ) (z : Rd d) :
    ∫ x, F (r • x + z) = (|r| ^ d)⁻¹ * ∫ y, F y := by
  have h1 := Measure.integral_comp_smul (volume : Measure (Rd d)) (fun w => F (w + z)) r
  rw [finrank_rd, integral_add_right_eq_self (fun w => F w) z, smul_eq_mul, abs_inv,
    abs_pow] at h1
  exact h1

/-- `∫ F((x - z)/r) dx = r^d ∫ F` for `r > 0`. -/
theorem integral_comp_affMap (F : Rd d → ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ∫ x, F (r⁻¹ • (x - z)) = r ^ d * ∫ x, F x := by
  have h := integral_comp_affinePt (fun x => F (r⁻¹ • (x - z))) hr z
  simp only [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hr.ne'), one_mul]

/-- `∫ F((x - z)/r) dx = |r|^d ∫ F` for `r ≠ 0`. -/
theorem integral_comp_affMap_of_ne (F : Rd d → ℝ) {r : ℝ} (hr : r ≠ 0) (z : Rd d) :
    ∫ x, F (r⁻¹ • (x - z)) = |r| ^ d * ∫ x, F x := by
  have h := integral_comp_affinePt_abs (fun x => F (r⁻¹ • (x - z))) r z
  simp only [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr, one_smul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d (abs_ne_zero.2 hr)), one_mul]

/-- `∫ φ((x-z)/r) dx = r^d ∫ φ` (`r > 0`). -/
theorem integral_testAffinePull (φ : TestRd d) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ∫ x, testAffinePull r z φ x = r ^ d * ∫ x, φ x := by
  simp only [testAffinePull_apply hr.ne']
  exact integral_comp_affMap (fun x => φ x) hr z

theorem integral_testAffinePull_of_ne (φ : TestRd d) {r : ℝ} (hr : r ≠ 0) (z : Rd d) :
    ∫ x, testAffinePull r z φ x = |r| ^ d * ∫ x, φ x := by
  simp only [testAffinePull_apply hr]
  exact integral_comp_affMap_of_ne (fun x => φ x) hr z

/-- `∫ φ((x-z)/r) g(x) dx = r^d ∫ φ(x) g(rx + z) dx` (`r > 0`). -/
theorem integral_testAffinePull_mul (φ : TestRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (g : Rd d → ℝ) :
    ∫ x, testAffinePull r z φ x * g x = r ^ d * ∫ x, φ x * g (r • x + z) := by
  have h := integral_comp_affinePt (fun x => testAffinePull r z φ x * g x) hr z
  simp only [testAffinePull_apply_affinePt hr.ne'] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hr.ne'), one_mul]

/-- The integral of `testAffinePull r z φ` vanishes whenever that of `φ` does (all `r`). -/
theorem integral_testAffinePull_eq_zero (r : ℝ) (z : Rd d) {φ : TestRd d}
    (hφ : ∫ x, φ x = 0) : ∫ x, testAffinePull r z φ x = 0 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [integral_testAffinePull_of_ne φ hr, hφ, mul_zero]

/-- The affine pullback of mean-zero test functions. -/
def testAffinePull0 (r : ℝ) (z : Rd d) (φ : TestRd0 d) : TestRd0 d :=
  ⟨testAffinePull r z φ.1, integral_testAffinePull_eq_zero r z φ.2⟩

@[simp]
theorem testAffinePull0_val (r : ℝ) (z : Rd d) (φ : TestRd0 d) :
    (testAffinePull0 r z φ).1 = testAffinePull r z φ.1 := rfl

/-! ### `affineComp` -/

/-- `⟨h(r·+z), φ⟩ = r^{-d} ⟨h, φ((·-z)/r)⟩`. -/
theorem affineComp_apply (r : ℝ) (z : Rd d) (h : DistRd d) (φ : TestRd d) :
    affineComp r z h φ = (r ^ d)⁻¹ * h (testAffinePull r z φ) := rfl

theorem affineComp_one_apply (z : Rd d) (h : DistRd d) (φ : TestRd d) :
    affineComp 1 z h φ = h (testAffinePull 1 z φ) := by
  rw [affineComp_apply, one_pow, inv_one, one_mul]

theorem affineComp_add (r : ℝ) (z : Rd d) (h k : DistRd d) :
    affineComp r z (h + k) = affineComp r z h + affineComp r z k := by
  ext φ
  simp only [affineComp_apply, add_apply, mul_add]

theorem affineComp_neg (r : ℝ) (z : Rd d) (h : DistRd d) :
    affineComp r z (-h) = -affineComp r z h := by
  ext φ
  simp only [affineComp_apply, neg_apply, mul_neg]

theorem affineComp_sub (r : ℝ) (z : Rd d) (h k : DistRd d) :
    affineComp r z (h - k) = affineComp r z h - affineComp r z k := by
  ext φ
  simp only [affineComp_apply, sub_apply, mul_sub]

theorem affineComp_smul (r : ℝ) (z : Rd d) (c : ℝ) (h : DistRd d) :
    affineComp r z (c • h) = c • affineComp r z h := by
  ext φ
  simp only [affineComp_apply, smul_apply, smul_eq_mul]
  ring

@[simp]
theorem affineComp_zero (r : ℝ) (z : Rd d) : affineComp r z (0 : DistRd d) = 0 := by
  ext φ
  simp only [affineComp_apply, zero_apply, mul_zero]

/-- `h ↦ h(r·+z)` as a linear map. -/
def affineCompLM (r : ℝ) (z : Rd d) : DistRd d →ₗ[ℝ] DistRd d where
  toFun := affineComp r z
  map_add' := affineComp_add r z
  map_smul' := affineComp_smul r z

@[simp]
theorem affineCompLM_apply (r : ℝ) (z : Rd d) (h : DistRd d) :
    affineCompLM r z h = affineComp r z h := rfl

/-- `h(r₂ · + z₂)(r₁ · + z₁) = h(r₂ r₁ · + r₂ z₁ + z₂)`, for all `r₁, r₂`. -/
theorem affineComp_affineComp (r₁ r₂ : ℝ) (z₁ z₂ : Rd d) (h : DistRd d) :
    affineComp r₁ z₁ (affineComp r₂ z₂ h) = affineComp (r₂ * r₁) (r₂ • z₁ + z₂) h := by
  ext φ
  rw [affineComp_apply, affineComp_apply, affineComp_apply, testAffinePull_testAffinePull,
    mul_pow, mul_inv, ← mul_assoc, mul_comm (r₁ ^ d)⁻¹]

@[simp]
theorem affineComp_one_zero (h : DistRd d) : affineComp 1 0 h = h := by
  ext φ
  rw [affineComp_one_apply, testAffinePull_one_zero, ContinuousLinearMap.id_apply]

theorem affineComp_one_affineComp_one (z₁ z₂ : Rd d) (h : DistRd d) :
    affineComp 1 z₁ (affineComp 1 z₂ h) = affineComp 1 (z₁ + z₂) h := by
  rw [affineComp_affineComp, one_mul, one_smul]

theorem affineComp_one_neg_affineComp_one (z : Rd d) (h : DistRd d) :
    affineComp 1 (-z) (affineComp 1 z h) = h := by
  rw [affineComp_one_affineComp_one, neg_add_cancel, affineComp_one_zero]

/-- The inverse of `h ↦ h(r·+z)` is `h ↦ h((· - z)/r) = affineComp r⁻¹ (-(r⁻¹ • z))`. -/
theorem affineComp_inv_affineComp {r : ℝ} (hr : r ≠ 0) (z : Rd d) (h : DistRd d) :
    affineComp r⁻¹ (-(r⁻¹ • z)) (affineComp r z h) = h := by
  rw [affineComp_affineComp, mul_inv_cancel₀ hr, smul_neg, smul_smul, mul_inv_cancel₀ hr,
    one_smul, neg_add_cancel, affineComp_one_zero]

theorem affineComp_affineComp_inv {r : ℝ} (hr : r ≠ 0) (z : Rd d) (h : DistRd d) :
    affineComp r z (affineComp r⁻¹ (-(r⁻¹ • z)) h) = h := by
  rw [affineComp_affineComp, inv_mul_cancel₀ hr, add_neg_cancel, affineComp_one_zero]

theorem affineComp_bijective {r : ℝ} (hr : r ≠ 0) (z : Rd d) : Bijective (affineComp r z) :=
  ⟨LeftInverse.injective (g := affineComp r⁻¹ (-(r⁻¹ • z))) (affineComp_inv_affineComp hr z),
    RightInverse.surjective (g := affineComp r⁻¹ (-(r⁻¹ • z))) (affineComp_affineComp_inv hr z)⟩

/-- On continuous functions `affineComp r z` is precomposition with `x ↦ r x + z` (`r > 0`): the
factor `r^{-d}` is the Jacobian of the change of variables. -/
theorem affineComp_ofCont {r : ℝ} (hr : 0 < r) (z : Rd d) (f : C(Rd d, ℝ)) :
    affineComp r z (ofCont f) = ofCont (f.comp (affinePt r z)) := by
  ext φ
  rw [affineComp_apply, ofCont_apply, ofCont_apply, integral_testAffinePull_mul φ hr z,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hr.ne'), one_mul]
  rfl

theorem affineComp_addFun {r : ℝ} (hr : 0 < r) (z : Rd d) (h : DistRd d) (f : C(Rd d, ℝ)) :
    affineComp r z (addFun h f) = addFun (affineComp r z h) (f.comp (affinePt r z)) := by
  rw [addFun, addFun, affineComp_add, affineComp_ofCont hr]

theorem affineComp_addConst {r : ℝ} (hr : 0 < r) (z : Rd d) (h : DistRd d) (c : ℝ) :
    affineComp r z (addConst h c) = addConst (affineComp r z h) c := by
  rw [addConst, affineComp_addFun hr, ContinuousMap.const_comp]
  rfl

theorem affineComp_ofCont_const {r : ℝ} (hr : 0 < r) (z : Rd d) (c : ℝ) :
    affineComp r z (ofCont (ContinuousMap.const (Rd d) c)) =
      ofCont (ContinuousMap.const (Rd d) c) := by
  rw [affineComp_ofCont hr, ContinuousMap.const_comp]

/-! ### Affine pullback between open sets -/

/-- The open set `{x | r x + z ∈ V}` (`= (V - z)/r` for `r ≠ 0`; a preimage, so no hypothesis
is needed). -/
def preOpens (r : ℝ) (z : Rd d) (V : Opens (Rd d)) : Opens (Rd d) :=
  ⟨affinePt r z ⁻¹' V, V.isOpen.preimage (affinePt r z).continuous⟩

@[simp]
theorem mem_preOpens (r : ℝ) (z : Rd d) (V : Opens (Rd d)) (x : Rd d) :
    x ∈ preOpens r z V ↔ r • x + z ∈ V := Iff.rfl

theorem coe_preOpens (r : ℝ) (z : Rd d) (V : Opens (Rd d)) :
    (preOpens r z V : Set (Rd d)) = affinePt r z ⁻¹' V := rfl

/-- `φ ↦ φ((·-z)/r)` from `𝓓(preOpens r z V)` to `𝓓(V)` (function part). -/
def testPullOnFun {r : ℝ} (hr : r ≠ 0) (z : Rd d) (V : Opens (Rd d))
    (φ : TestOn (preOpens r z V)) : TestOn V :=
  ⟨φ ∘ affMap r z, contDiff_comp_affMap r z φ.contDiff,
    hasCompactSupport_comp_affMap hr z φ.hasCompactSupport,
    (tsupport_comp_subset_preimage _ (continuous_affMap r z)).trans fun x hx => by
      have h' : r • affMap r z x + z ∈ (V : Set (Rd d)) := φ.tsupport_subset hx
      rwa [affinePt_affMap hr] at h'⟩

@[simp]
theorem testPullOnFun_apply {r : ℝ} (hr : r ≠ 0) (z : Rd d) (V : Opens (Rd d))
    (φ : TestOn (preOpens r z V)) (x : Rd d) :
    testPullOnFun hr z V φ x = φ (affMap r z x) := rfl

/-- the compact `r K + z` -/
def affK (r : ℝ) (z : Rd d) (K : Compacts (Rd d)) : Compacts (Rd d) :=
  K.map (fun y => r • y + z) (by fun_prop)

theorem affMap_mem_of {r : ℝ} (hr : r ≠ 0) (z : Rd d) (K : Compacts (Rd d)) {x : Rd d}
    (hx : affMap r z x ∈ (K : Set (Rd d))) : x ∈ (affK r z K : Set (Rd d)) :=
  ⟨affMap r z x, hx, affinePt_affMap hr z x⟩

/-- `φ ↦ φ((·-z)/r)` from `𝓓_K` to `𝓓_{rK+z}`. -/
def pullK {r : ℝ} (hr : r ≠ 0) (z : Rd d) (K : Compacts (Rd d)) :
    𝓓^{⊤}_{K}(Rd d, ℝ) →ₗ[ℝ] 𝓓^{⊤}_{affK r z K}(Rd d, ℝ) where
  toFun φ :=
    { toFun := φ ∘ affMap r z
      contDiff' := contDiff_comp_affMap r z φ.contDiff
      zero_on_compl' := fun _ hx => φ.zero_on_compl (fun hK => hx (affMap_mem_of hr z K hK)) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem continuous_pullK {r : ℝ} (hr : r ≠ 0) (z : Rd d) (K : Compacts (Rd d)) :
    Continuous (pullK hr z K) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  let Ψ := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
      (E := fun _ : Fin i => Rd d) (E₁ := fun _ : Fin i => Rd d) (F := ℝ)
      (fun _ => affLin r)).compLeftContinuousBounded (Rd d)
  have key : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ pullK hr z K) =
      (fun g => (Ψ g).compContinuous ⟨affMap r z, continuous_affMap r z⟩) ∘
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := by
    funext φ
    ext x : 1
    simp only [comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rw [BoundedContinuousFunction.compContinuous_apply,
      ContinuousLinearMap.compLeftContinuousBounded_apply,
      ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact iteratedFDeriv_comp_affMap r z φ.contDiff i x
  rw [key]
  exact ((BoundedContinuousFunction.continuous_compContinuous _).comp Ψ.continuous).comp
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous

theorem affK_subset (r : ℝ) (z : Rd d) (V : Opens (Rd d)) {K : Compacts (Rd d)}
    (hK : (K : Set (Rd d)) ⊆ preOpens r z V) : (affK r z K : Set (Rd d)) ⊆ V := by
  rintro x ⟨y, hy, rfl⟩
  exact hK hy

/-- `φ ↦ φ((·-z)/r)` as a continuous linear map `𝓓(preOpens r z V) → 𝓓(V)` (`r ≠ 0`). -/
def testPullOn {r : ℝ} (hr : r ≠ 0) (z : Rd d) (V : Opens (Rd d)) :
    TestOn (preOpens r z V) →L[ℝ] TestOn V :=
  TestFunction.mkCLM ℝ (testPullOnFun hr z V) (fun _ _ => rfl) (fun _ _ => rfl) (fun K hK => by
    have : (testPullOnFun hr z V ∘ TestFunction.ofSupportedIn hK) =
        TestFunction.ofSupportedInCLM ℝ (affK_subset r z V hK) ∘ pullK hr z K := by
      funext φ; ext x; rfl
    rw [this]
    exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp (continuous_pullK hr z K))

@[simp]
theorem testPullOn_apply {r : ℝ} (hr : r ≠ 0) (z : Rd d) (V : Opens (Rd d))
    (φ : TestOn (preOpens r z V)) (x : Rd d) : testPullOn hr z V φ x = φ (affMap r z x) := rfl

/-- `k ↦ k(r · + z)` from `𝒟'(V)` to `𝒟'(preOpens r z V)`:
`⟨k(r·+z), φ⟩ = r^{-d} ⟨k, φ((·-z)/r)⟩`. -/
def distAffine {r : ℝ} (hr : r ≠ 0) (z : Rd d) {V : Opens (Rd d)} (k : DistOn V) :
    DistOn (preOpens r z V) :=
  (r ^ d)⁻¹ • k.comp (testPullOn hr z V)

theorem distAffine_apply {r : ℝ} (hr : r ≠ 0) (z : Rd d) {V : Opens (Rd d)} (k : DistOn V)
    (φ : TestOn (preOpens r z V)) :
    distAffine hr z k φ = (r ^ d)⁻¹ * k (testPullOn hr z V φ) := rfl

theorem testAffinePull_testIncl {r : ℝ} (hr : r ≠ 0) (z : Rd d) (V : Opens (Rd d))
    (φ : TestOn (preOpens r z V)) :
    testAffinePull r z (testIncl (preOpens r z V) φ) = testIncl V (testPullOn hr z V φ) :=
  TestFunction.ext fun x => by
    rw [testIncl_apply, testPullOn_apply, testAffinePull_of_ne hr, comp_apply, testIncl_apply]

/-- The restriction of `h(r·+z)` to `preOpens r z V` is the affine image of `h|_V`. -/
theorem restrictTo_affineComp {r : ℝ} (hr : r ≠ 0) (z : Rd d) (V : Opens (Rd d))
    (h : DistRd d) :
    restrictTo (preOpens r z V) (affineComp r z h) = distAffine hr z (restrictTo V h) := by
  ext φ
  rw [restrictTo_apply, affineComp_apply, distAffine_apply, restrictTo_apply,
    testAffinePull_testIncl hr]

/-- Locality transport: if `h|_V = h'|_V` then `h(r·+z)` and `h'(r·+z)` agree on
`preOpens r z V`. -/
theorem restrictTo_affineComp_congr {r : ℝ} (hr : r ≠ 0) (z : Rd d) (V : Opens (Rd d))
    {h h' : DistRd d} (hh : restrictTo V h = restrictTo V h') :
    restrictTo (preOpens r z V) (affineComp r z h) =
      restrictTo (preOpens r z V) (affineComp r z h') := by
  rw [restrictTo_affineComp hr, restrictTo_affineComp hr, hh]

end HigherDimLQGMetric
