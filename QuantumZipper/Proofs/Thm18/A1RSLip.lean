import QuantumZipper.Proofs.Thm18.A1RSRadius
import QuantumZipper.Proofs.Zipper.RegCont
import QuantumZipper.Proofs.Loewner.CaraRZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (11): polynomial Lipschitz bounds off strips, in space and in time

For the parameter moduli of the smeared-loop family `a1rfNu` (A1RFSmear.lean) all maps are
compared at the same angles, and off strips `{Im ≤ τ}` of small mass the following bounds are
polynomial in `1/τ` (in contrast to the Grönwall bounds `exp(C/τ²)`, which give no power
modulus):

* `norm_sub_le_of_holo_bdd`: a holomorphic map of `ℍ` bounded by `B` on `ℍ ∩ ball 0 (R+1)` is
  `2B/τ`-Lipschitz on `{Im ≥ τ} ∩ closedBall 0 R` (`τ ≤ 1`; Cauchy's estimate
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` and the mean value inequality on the
  convex set). Used for the pushing maps `f_t ∘ ψ`.
* `norm_fwdMapInv_add_sub_mul_le`: the time displacement of `f_t⁻¹` at a point of height
  `≥ τ`: `τ ‖f_{s+h}⁻¹ u − f_s⁻¹ u‖ ≤ √((R + D)² + 4s) · D`, `D = 3ε + 6√h`, `ε` the oscillation
  of the driver on `[s, s+h]` (flow property `RegCont.fwdMapInv_add`, uniform displacement of the
  reverse flow `CaraR.norm_revMap_sub_self_le` — Lawler, *Conformally Invariant Processes in the
  Plane*, Lemma 4.12 — and the two-point upper bound `norm_fwdMapInv_sub_mul_le`).

Own elementary arguments on the cited estimates.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

/-- **Cauchy–Lipschitz bound off a strip.** -/
theorem norm_sub_le_of_holo_bdd {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H) {B R τ : ℝ}
    (hB : ∀ z ∈ H, ‖z‖ < R + 1 → ‖F z‖ ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1) {w w' : ℂ}
    (hw : τ ≤ w.im) (hw' : τ ≤ w'.im) (hwR : ‖w‖ ≤ R) (hwR' : ‖w'‖ ≤ R) :
    ‖F w - F w'‖ ≤ 2 * B / τ * ‖w - w'‖ := by
  set S : Set ℂ := {z | τ ≤ z.im} ∩ closedBall 0 R with hS
  have hconv : Convex ℝ S := by
    refine Convex.inter ?_ (convex_closedBall 0 R)
    have : {z : ℂ | τ ≤ z.im} = Complex.im ⁻¹' Ici τ := rfl
    rw [this]
    exact (convex_Ici τ).linear_preimage Complex.imLm
  have hball : ∀ z ∈ S, closedBall z (τ / 2) ⊆ H ∩ ball 0 (R + 1) := by
    intro z hz y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have h1 : |(y - z).im| ≤ ‖y - z‖ := Complex.abs_im_le_norm _
    rw [sub_im, abs_le] at h1
    have hz1 : τ ≤ z.im := hz.1
    refine ⟨show 0 < y.im by linarith [h1.1], ?_⟩
    rw [mem_ball, dist_zero_right]
    have h2 : ‖z‖ ≤ R := by simpa using hz.2
    calc ‖y‖ = ‖(y - z) + z‖ := by ring_nf
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      _ < R + 1 := by linarith
  have hdiff : ∀ z ∈ S, DifferentiableAt ℂ F z := fun z hz => by
    have hz1 : τ ≤ z.im := hz.1
    exact hd.differentiableAt (isOpen_H.mem_nhds (show 0 < z.im by linarith))
  have hderiv : ∀ z ∈ S, ‖deriv F z‖ ≤ 2 * B / τ := by
    intro z hz
    have hr : 0 < τ / 2 := half_pos hτ
    have hcl : DiffContOnCl ℂ F (ball z (τ / 2)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z hr.ne']
      exact hd.mono fun y hy => (hball z hz hy).1
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl
      (C := B) fun y hy => by
        have hy' := hball z hz (sphere_subset_closedBall hy)
        exact hB y hy'.1 (by simpa using hy'.2)
    calc ‖deriv F z‖ ≤ B / (τ / 2) := this
      _ = 2 * B / τ := by field_simp
  have hwS : w ∈ S := ⟨hw, by simpa using hwR⟩
  have hw'S : w' ∈ S := ⟨hw', by simpa using hwR'⟩
  exact hconv.norm_image_sub_le_of_norm_deriv_le hdiff hderiv hw'S hwS

/-- **Time displacement of `f_t⁻¹` at a point of height `≥ τ`, polynomial in `1/τ`.** -/
theorem norm_fwdMapInv_add_sub_mul_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s h ε τ R : ℝ} (hs : 0 ≤ s) (hh : 0 < h)
    (hε : ∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) (hτ : 0 < τ) {u : ℂ}
    (hu : τ ≤ u.im) (huR : u.im ≤ R) :
    τ * ‖fwdMapInv W (s + h) u - fwdMapInv W s u‖ ≤
      Real.sqrt ((R + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * s) *
        (3 * ε + 6 * Real.sqrt h) := by
  have hu0 : u ∈ H := show 0 < u.im by linarith
  set V' : ℝ → ℝ := fun q => W (s + h - q) - W (s + h) with hV'
  have hV'c : Continuous V' := by rw [hV']; fun_prop
  rw [RegCont.fwdMapInv_add hW hW0 hs hh.le hu0]
  set φ := revMap V' h u with hφ
  have hd : ‖φ - u‖ ≤ 3 * ε + 6 * Real.sqrt h := CaraR.norm_revMap_sub_self_le hV'c hh hε hu0
  have hφim : u.im ≤ φ.im := im_le_im_revMap V' hV'c u hu0 hh.le
  have hφR : φ.im ≤ R + (3 * ε + 6 * Real.sqrt h) := by
    have h1 : |(φ - u).im| ≤ ‖φ - u‖ := Complex.abs_im_le_norm _
    rw [sub_im, abs_le] at h1
    linarith
  have hD : 0 ≤ 3 * ε + 6 * Real.sqrt h := (norm_nonneg _).trans hd
  have key := norm_fwdMapInv_sub_mul_le hW hW0 hs hτ (hu.trans hφim) hu hφR (by linarith)
  refine key.trans (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _))

end A1RS
end R18
end QuantumZipper
