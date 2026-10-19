import LQGMetric.Field.GFFInvariance
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rotations of test functions, distributions and the whole-plane GFF

Infrastructure for the rotation case of blueprint Proposition `prop:metric-facts` (F3), proved
from the exact rotation covariance of LFPP (`GaussianLQG/Metric/LFPPRotation.lean`).

* `testCLEPull e : 𝓓(ℂ) →L[ℝ] 𝓓(ℂ)`, `φ ↦ φ ∘ e`, for a real-linear continuous equivalence
  `e` of `ℂ` (the same construction as `LQGMetric.testAffinePull`, through the spaces `𝓓_K`);
* `testRot a`: `φ ↦ φ(a⁻¹ ·)` (junk `0` for `a = 0`), and the rotated distribution
  `rotDist a h`, `⟨rotDist a h, φ⟩ = ⟨h, φ(a⁻¹ ·)⟩`. For `‖a‖ = 1` this is the pullback
  `h(a ·)` (the Jacobian of `x ↦ a x` is `|a|² = 1`), the analogue of `LQGMetric.affineComp`;
* rotations preserve Lebesgue measure on `ℂ` (`integral_comp_mul_of_norm_eq_one`), the covariance
  `logCov` (`logCov_comp_mul`) and mean-zero test functions, hence the law of the whole-plane GFF:
  `isWholePlaneGFF_rotDist` (rotation invariance of the whole-plane GFF modulo additive constant,
  used in GM, arXiv:1905.00383v3, and in blueprint (S4)).

The proofs mirror `LQGMetric.Field.GFFInvariance` (scalings and translations).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.GFFInv

/-! ## Pullback of test functions by a linear equivalence -/

section CLEPull

open TopologicalSpace

variable (e : ℂ ≃L[ℝ] ℂ)

/-- the compact `e⁻¹(K)` -/
def cleK (K : Compacts ℂ) : Compacts ℂ := K.map e.symm e.symm.continuous

lemma mem_cleK_of (K : Compacts ℂ) {x : ℂ} (hx : e x ∈ (K : Set ℂ)) :
    x ∈ (cleK e K : Set ℂ) :=
  ⟨e x, hx, e.symm_apply_apply x⟩

/-- `φ ↦ φ ∘ e` from `𝓓_K` to `𝓓_{e⁻¹ K}` -/
def clePullK (K : Compacts ℂ) :
    𝓓^{⊤}_{K}(ℂ, ℝ) →ₗ[ℝ] 𝓓^{⊤}_{cleK e K}(ℂ, ℝ) where
  toFun φ :=
    { toFun := φ ∘ e
      contDiff' := φ.contDiff.comp e.contDiff
      zero_on_compl' := fun _ hx => φ.zero_on_compl (fun hK => hx (mem_cleK_of e K hK)) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma iteratedFDeriv_comp_cle {φ : ℂ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (i : ℕ)
    (x : ℂ) :
    iteratedFDeriv ℝ i (φ ∘ e) x =
      (iteratedFDeriv ℝ i φ (e x)).compContinuousLinearMap fun _ => (e : ℂ →L[ℝ] ℂ) :=
  (e : ℂ →L[ℝ] ℂ).iteratedFDeriv_comp_right hφ x (by exact_mod_cast le_top)

lemma continuous_clePullK (K : Compacts ℂ) : Continuous (clePullK e K) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  let Ψ := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
      (E := fun _ : Fin i => ℂ) (E₁ := fun _ : Fin i => ℂ) (F := ℝ)
      (fun _ => (e : ℂ →L[ℝ] ℂ))).compLeftContinuousBounded ℂ
  have key : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ clePullK e K) =
      (fun g => (Ψ g).compContinuous ⟨e, e.continuous⟩) ∘
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := by
    funext φ
    ext x : 1
    simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rw [BoundedContinuousFunction.compContinuous_apply,
      ContinuousLinearMap.compLeftContinuousBounded_apply,
      ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact iteratedFDeriv_comp_cle e φ.contDiff i x
  rw [key]
  exact ((BoundedContinuousFunction.continuous_compContinuous _).comp Ψ.continuous).comp
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous

lemma hasCompactSupport_comp_cle {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (φ ∘ e) :=
  hφ.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding

/-- `φ ↦ φ ∘ e` on `𝓓(ℂ)`, for a real-linear continuous equivalence `e` of `ℂ`. -/
def testCLEPull : TestC →L[ℝ] TestC :=
  TestFunction.mkCLM ℝ
    (fun φ => ⟨φ ∘ e, φ.contDiff.comp e.contDiff, hasCompactSupport_comp_cle e φ.hasCompactSupport,
      subset_univ _⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun K _ => by
      have : (fun φ : TestC => (⟨φ ∘ e, φ.contDiff.comp e.contDiff,
          hasCompactSupport_comp_cle e φ.hasCompactSupport, subset_univ _⟩ : TestC)) ∘
          TestFunction.ofSupportedIn (subset_univ (K : Set ℂ)) =
          TestFunction.ofSupportedInCLM ℝ (subset_univ (cleK e K : Set ℂ)) ∘ clePullK e K := by
        funext φ; ext x; rfl
      rw [this]
      exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp (continuous_clePullK e K))

end CLEPull

/-! ## Rotations -/

/-- multiplication by `b ≠ 0` as a real-linear continuous equivalence of `ℂ` -/
def mulCLE (b : ℂ) (hb : b ≠ 0) : ℂ ≃L[ℝ] ℂ where
  toFun x := b * x
  invFun x := b⁻¹ * x
  map_add' x y := mul_add b x y
  map_smul' c x := by
    simp only [Complex.real_smul, RingHom.id_apply]
    ring
  left_inv x := inv_mul_cancel_left₀ hb x
  right_inv x := mul_inv_cancel_left₀ hb x
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/-- `φ ↦ φ(a⁻¹ ·)` on `𝓓(ℂ)` (junk `0` for `a = 0`) -/
def testRot (a : ℂ) : TestC →L[ℝ] TestC :=
  if ha : a = 0 then 0 else testCLEPull (mulCLE a⁻¹ (inv_ne_zero ha))

lemma testRot_apply {a : ℂ} (ha : a ≠ 0) (φ : TestC) (x : ℂ) :
    testRot a φ x = φ (a⁻¹ * x) := by
  simp only [testRot, ha, dite_false]
  rfl

/-- The rotated distribution: `⟨rotDist a h, φ⟩ = ⟨h, φ(a⁻¹ ·)⟩`. For `‖a‖ = 1` this is the
pullback `h(a ·)` of `h` by the rotation `x ↦ a x` (whose Jacobian is `|a|² = 1`); compare
`LQGMetric.affineComp`. -/
def rotDist (a : ℂ) (h : DistC) : DistC := h.comp (testRot a)

lemma rotDist_apply (a : ℂ) (h : DistC) (φ : TestC) : rotDist a h φ = h (testRot a φ) := rfl

lemma ne_zero_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) : a ≠ 0 := by
  rintro rfl
  rw [norm_zero] at ha
  exact zero_ne_one ha

lemma norm_inv_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) : ‖a⁻¹‖ = 1 := by
  rw [norm_inv, ha, inv_one]

/-- Multiplication by `a` with `‖a‖ = 1` preserves Lebesgue measure on `ℂ`. -/
lemma measurePreserving_mul_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurePreserving (fun x : ℂ => a * x) volume volume := by
  have e : (fun x : ℂ => a * x) = ⇑(rotation (⟨a, mem_sphere_zero_iff_norm.2 ha⟩ : Circle)) :=
    funext fun x => (rotation_apply (⟨a, mem_sphere_zero_iff_norm.2 ha⟩ : Circle) x).symm
  rw [e]
  exact (rotation _).measurePreserving

/-- Change of variables `x ↦ a x` with `‖a‖ = 1`. -/
lemma integral_comp_mul_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) (F : ℂ → ℝ) :
    ∫ x, F (a * x) = ∫ x, F x :=
  (measurePreserving_mul_of_norm_eq_one ha).integral_comp
    (mulCLE a (ne_zero_of_norm_eq_one ha)).toHomeomorph.measurableEmbedding F

lemma integral_testRot {a : ℂ} (ha : ‖a‖ = 1) (φ : TestC) :
    ∫ x, testRot a φ x = ∫ x, φ x := by
  simp only [testRot_apply (ne_zero_of_norm_eq_one ha)]
  exact integral_comp_mul_of_norm_eq_one (norm_inv_of_norm_eq_one ha) fun x => φ x

/-- **The covariance `-log|x - y|` is rotation invariant.** -/
theorem logCov_comp_mul {b : ℂ} (hb : ‖b‖ = 1) (φ ψ : ℂ → ℝ) :
    logCov (fun x => φ (b * x)) (fun y => ψ (b * y)) = logCov φ ψ := by
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hbi : ‖b⁻¹‖ = 1 := norm_inv_of_norm_eq_one hb
  unfold logCov
  rw [← integral_comp_mul_of_norm_eq_one hbi]
  congr 1
  funext x
  rw [← integral_comp_mul_of_norm_eq_one hbi]
  congr 1
  funext y
  beta_reduce
  rw [mul_inv_cancel_left₀ hb0, mul_inv_cancel_left₀ hb0, ← mul_sub, norm_mul, hbi, one_mul]

/-- the rotation on mean-zero test functions -/
def rot0 {a : ℂ} (ha : ‖a‖ = 1) (φ : TestC0) : TestC0 :=
  ⟨testRot a φ.1, by rw [integral_testRot ha, φ.2]⟩

lemma logCov_rot0 {a : ℂ} (ha : ‖a‖ = 1) (φ ψ : TestC0) :
    logCov (rot0 ha φ).1 (rot0 ha ψ).1 = logCov φ.1 ψ.1 := by
  have e : ∀ χ : TestC0, ((rot0 ha χ).1 : ℂ → ℝ) = fun x => χ.1 (a⁻¹ * x) :=
    fun χ => funext fun x => testRot_apply (ne_zero_of_norm_eq_one ha) χ.1 x
  rw [e, e]
  exact logCov_comp_mul (norm_inv_of_norm_eq_one ha) _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Rotation invariance of the whole-plane GFF**: if `h` is a whole-plane GFF (modulo additive
constant) and `‖a‖ = 1`, then so is `h(a ·) = rotDist a h`. -/
theorem isWholePlaneGFF_rotDist {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {a : ℂ}
    (ha : ‖a‖ = 1) : IsWholePlaneGFF (fun ω => rotDist a (h ω)) P where
  measurable := measurable_distC_iff.2 fun φ => (measurable_pair (testRot a φ)).comp hh.measurable
  gaussian := hh.gaussian.comp_right (rot0 ha)
  centered := fun φ => hh.centered (rot0 ha φ)
  covariance_eq := fun φ ψ =>
    (hh.covariance_eq (rot0 ha φ) (rot0 ha ψ)).trans (logCov_rot0 ha φ ψ)

end GaussianLQG
