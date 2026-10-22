import HigherDimLQGMetric.Frozen.KernelSymbol
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives of Euclidean norm powers

The punctured-space homogeneity estimate used in MA5 A2.4. The scaling identity
for iterated Fréchet derivatives holds even without a global smoothness hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Iterated derivatives commute with scalar dilation, with the expected power factor. -/
theorem iteratedFDeriv_comp_const_smul_any {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (f : E → F) (i : ℕ) :
    iteratedFDeriv ℝ i (fun z => f (a • z)) =
      fun x => a ^ i • iteratedFDeriv ℝ i f (a • x) := by
  induction i with
  | zero => ext; simp
  | succ i hi =>
      ext v
      rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
      simp only [Nat.succ_eq_add_one, hi, Function.comp_apply,
        continuousMultilinearCurryLeftEquiv_symm_apply, smul_apply]
      simp only [← Pi.smul_def]
      rw [fderiv_const_smul_field (f := fun x : E => iteratedFDeriv ℝ i f (a • x)) (a ^ i)]
      simp only [Pi.smul_apply]
      rw [fderiv_comp_smul, smul_smul, ← pow_succ]
      simp

/-- Derivatives of `‖·‖^m` are homogeneous away from zero. -/
theorem norm_pow_deriv_homogeneous {dim : ℕ} (m : ℕ) (r : ℝ) (hr : 0 < r)
    (n : ℕ) (u : Rd dim) (hu : u ≠ 0) :
    r ^ n • iteratedFDeriv ℝ n (fun z : Rd dim => ‖z‖ ^ m) (r • u) =
      r ^ m • iteratedFDeriv ℝ n (fun z : Rd dim => ‖z‖ ^ m) u := by
  let f : Rd dim → ℝ := fun z => ‖z‖ ^ m
  have hfun : (fun z : Rd dim => f (r • z)) = fun z => r ^ m • f z := by
    funext z
    simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_eq_mul, mul_pow]
  have h := congrFun (iteratedFDeriv_comp_const_smul_any r f n) u
  rw [hfun] at h
  have hfd : ContDiffAt ℝ n f u := (contDiffAt_norm ℝ hu).pow m
  change iteratedFDeriv ℝ n (r ^ m • f) u = _ at h
  rw [iteratedFDeriv_const_smul_apply hfd] at h
  exact h.symm

private theorem norm_pow_deriv_unit_bounded {dim : ℕ} (m n : ℕ) :
    ∃ C : ℝ, ∀ u : Rd dim, ‖u‖ = 1 →
      ‖iteratedFDeriv ℝ n (fun z : Rd dim => ‖z‖ ^ m) u‖ ≤ C := by
  let f : Rd dim → ℝ := fun z => ‖z‖ ^ m
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ({0}ᶜ : Set (Rd dim)) := by
    intro u hu
    exact ((contDiffAt_norm ℝ (show u ≠ 0 from hu)).pow m).contDiffWithinAt
  have hc : ContinuousOn (iteratedFDeriv ℝ n f) ({0}ᶜ : Set (Rd dim)) :=
    ContinuousOn.continuousOn_iteratedFDeriv hs (isClosed_singleton.isOpen_compl) (by simp)
  have hsub : Metric.sphere (0 : Rd dim) 1 ⊆ ({0}ᶜ : Set (Rd dim)) := by
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
    exact fun hz => by simp at hz; subst u; norm_num at hu1
  have hb : Bornology.IsBounded ((iteratedFDeriv ℝ n f) '' Metric.sphere (0 : Rd dim) 1) :=
    ((isCompact_sphere (0 : Rd dim) 1).image_of_continuousOn (hc.mono hsub)).isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  exact ⟨C, fun u hu => hC _ ⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu,
    rfl⟩⟩

/-- The `n`th derivative of `‖·‖^m` has growth at most `‖x‖^(m-n)`. -/
theorem norm_pow_deriv_weighted {dim : ℕ} (m n : ℕ) :
    ∃ C : ℝ, ∀ x : Rd dim, x ≠ 0 →
      ‖x‖ ^ n * ‖iteratedFDeriv ℝ n (fun z : Rd dim => ‖z‖ ^ m) x‖ ≤
        C * ‖x‖ ^ m := by
  obtain ⟨C, hC⟩ := norm_pow_deriv_unit_bounded (dim := dim) m n
  refine ⟨C, fun x hx => ?_⟩
  let r : ℝ := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx
  let u : Rd dim := r⁻¹ • x
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, r, inv_mul_cancel₀ hr.ne']
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hru : r • u = x := by
    simp [u, smul_smul, mul_inv_cancel₀ hr.ne']
  have hscale := norm_pow_deriv_homogeneous m r hr n u hu0
  rw [hru] at hscale
  have hnorm := congrArg norm hscale
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)] at hnorm
  calc
    ‖x‖ ^ n * ‖iteratedFDeriv ℝ n (fun z : Rd dim => ‖z‖ ^ m) x‖ =
        r ^ m * ‖iteratedFDeriv ℝ n (fun z : Rd dim => ‖z‖ ^ m) u‖ := by
      simpa only [r] using hnorm
    _ ≤ C * r ^ m := by
      have h := mul_le_mul_of_nonneg_left (hC u hu) (pow_nonneg hr.le m)
      simpa only [mul_comm] using h
    _ = C * ‖x‖ ^ m := rfl

end HigherDimLQGMetric
