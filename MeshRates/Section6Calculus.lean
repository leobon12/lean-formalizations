import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import BouRabeeGwynne.PaperObjects

/-!
# Calculus inputs for MR §6: Taylor bound (77) and the rate choice (80)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace BouRabeeGwynne.MeshRates

/-- Second-order Taylor bound (MR (77)): on a convex set where `‖D²h‖ ≤ M`, the first-order
remainder is at most `M/2 · ‖y - x‖²`. -/
theorem taylor_first_order_remainder_le {d : ℕ} {h : Euc d → ℝ} {W S : Set (Euc d)}
    (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W) (hS : Convex ℝ S) (hSW : S ⊆ W) {M : ℝ}
    (hM : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) {x y : Euc d} (hx : x ∈ S) (hy : y ∈ S) :
    |h y - h x - fderiv ℝ h x (y - x)| ≤ M / 2 * ‖y - x‖ ^ 2 := by
  have hdh : ∀ z ∈ S, DifferentiableAt ℝ h z := fun z hz =>
    ((hh.differentiableOn (by norm_num)) z (hSW hz)).differentiableAt (hW.mem_nhds (hSW hz))
  have hDh : ContDiffOn ℝ 1 (fun z => fderiv ℝ h z) W :=
    hh.fderiv_of_isOpen hW (by norm_num)
  have hdDh : ∀ z ∈ S, DifferentiableAt ℝ (fderiv ℝ h) z := fun z hz =>
    ((hDh.differentiableOn (by norm_num)) z (hSW hz)).differentiableAt (hW.mem_nhds (hSW hz))
  set v := y - x with hv
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • v ∈ S := fun s hs => by
    have := hS.add_smul_sub_mem hx hy hs
    simpa [hv] using this
  let q : ℝ → ℝ := fun s => h (x + s • v) - h x - s * fderiv ℝ h x v
  let q' : ℝ → ℝ := fun s => (fderiv ℝ h (x + s • v) - fderiv ℝ h x) v
  have hq : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt q (q' s) s := by
    intro s hs
    have hpath : HasDerivAt (fun r : ℝ => x + r • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    have hcomp := (hdh _ (hseg s hs)).hasFDerivAt.comp_hasDerivAt s hpath
    have h2 := (hcomp.sub_const (h x)).sub ((hasDerivAt_id s).mul_const (fderiv ℝ h x v))
    apply h2.congr_deriv
    simp [q']
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖q' s‖ ≤ M * s * ‖v‖ ^ 2 := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have hg : ‖fderiv ℝ h (x + s • v) - fderiv ℝ h x‖ ≤ M * ‖x + s • v - x‖ :=
      hS.norm_image_sub_le_of_norm_fderiv_le hdDh hM hx (hseg s hs')
    have hn : ‖x + s • v - x‖ = s * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc ‖q' s‖ ≤ ‖fderiv ℝ h (x + s • v) - fderiv ℝ h x‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ v
      _ ≤ (M * (s * ‖v‖)) * ‖v‖ := by
          rw [← hn]; exact mul_le_mul_of_nonneg_right hg (norm_nonneg v)
      _ = M * s * ‖v‖ ^ 2 := by ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := q) (f' := q') (B := fun s => M / 2 * s ^ 2 * ‖v‖ ^ 2)
    (B' := fun s => M * s * ‖v‖ ^ 2) (a := 0) (b := 1)
    (fun s hs => (hq s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hq s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (by simp [q])
    (fun s => by
      have := ((hasDerivAt_pow 2 s).const_mul (M / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring)
    hbound (x := 1) ⟨zero_le_one, le_rfl⟩
  have hxy : x + v = y := by rw [hv, add_sub_cancel]
  simpa [q, Real.norm_eq_abs, hxy] using key

/-- MR (80): with `η = ε^{4/(d+4)}`, `η + (ε/η)^{4/d} + ε(ε/η)^{2/d} + ε ≤ 4 ε^{4/(d+4)}` for
`0 < ε ≤ 1`. -/
theorem rate_choice_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ (4 / ((d : ℝ) + 4)) + (ε / ε ^ (4 / ((d : ℝ) + 4))) ^ (4 / (d : ℝ)) +
        ε * (ε / ε ^ (4 / ((d : ℝ) + 4))) ^ (2 / (d : ℝ)) + ε ≤
      4 * ε ^ (4 / ((d : ℝ) + 4)) := by
  set a : ℝ := 4 / ((d : ℝ) + 4) with ha
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd4 : (0 : ℝ) < d + 4 := by linarith
  have hq : ε / ε ^ a = ε ^ (1 - a) := by rw [Real.rpow_sub hε, Real.rpow_one]
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hd4]; linarith
  have h2 : (ε ^ (1 - a)) ^ (4 / (d : ℝ)) = ε ^ a := by
    rw [← Real.rpow_mul hε.le]; congr 1; rw [ha]; field_simp; ring
  have h3 : ε * (ε ^ (1 - a)) ^ (2 / (d : ℝ)) ≤ ε ^ a := by
    rw [← Real.rpow_mul hε.le]
    conv_lhs => arg 1; rw [← Real.rpow_one ε]
    rw [← Real.rpow_add hε]
    apply Real.rpow_le_rpow_of_exponent_ge hε hε1
    have : 0 ≤ (1 - a) * (2 / (d : ℝ)) := by
      apply mul_nonneg (by linarith) (by positivity)
    linarith
  have h4 : ε ≤ ε ^ a := by
    conv_lhs => rw [← Real.rpow_one ε]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1 ha1
  rw [hq, h2]
  linarith

end BouRabeeGwynne.MeshRates
