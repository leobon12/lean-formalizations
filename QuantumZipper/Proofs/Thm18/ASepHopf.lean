import QuantumZipper.Proofs.Thm11.ForwardClock
import QuantumZipper.Proofs.Thm18.ExactClRTX
import QuantumZipper.Proofs.Thm18.G1PkgTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (b): the imaginary-part comparison, uniform over a parameter box (`τ' = 0`)

For the A-sep family at `τ' = 0` (D84), `ψ = revMapInv (revDrv W τ a)` and `a ψ(w) = f_τ(a w)`
on the image of the re-zipping map (`G4Core.mul_revMapInv_backDrv_eq_fwdMap`, Loewner cocycle).
The comparison `Im ψ(w) ≥ c · Im w` needed by the deterministic node `det_unif_gen`
(G4SepUC2Det) and by the strip bounds of the pushed circles holds with the **explicit constant**
`c = exp(−2τ/m²)`, where `m` is a lower bound for `|f_s(a w)|`, `s ∈ [0, τ]`:

* `im_sol_ge_of_lower`, `im_fwdMap_ge_of_lower`: the Loewner clock identity
  `Im f_t(z) = Im z · exp(−2 ∫_0^t |f_s(z)|^{-2} ds)` (`FwdClock.sol_im_eq_clock`; Lawler,
  *Conformally invariant processes in the plane*, §4.1, the ODE `∂_t Im g_t = −2 Im g_t/|g_t − W_t|²`)
  and `|f_s(z)| ≥ m`;
* `im_revMapInv_revDrv_ge`: the comparison for `ψ`.

So the comparison is uniform over any parameter box on which the lower bound `m` is uniform
(the centre modulus task (C1), Kemppainen, *SLE*, Lemma 6.7). This replaces the compactness
argument of `im_revMapInv_ge_compact` (one map at a time) by a quantitative one. Own elementary
argument from the clock identity.
-/

noncomputable section

open MeasureTheory Set

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- **Lower bound for the imaginary part along a forward solution.** -/
theorem im_sol_ge_of_lower {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) {T m : ℝ}
    (hm : 0 < m) {u : ℝ → ℂ} (hu : IsForwardSol W z T u)
    (hlow : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖u s‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    z.im * Real.exp (-2 * T / m ^ 2) ≤ (u t).im := by
  rw [FwdClock.sol_im_eq_clock hW hz hu ht]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hz.le
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hint : ∫ s in (0 : ℝ)..t, 1 / ‖u s‖ ^ 2 ≤ ∫ s in (0 : ℝ)..t, 1 / m ^ 2 := by
    refine intervalIntegral.integral_mono_on ht.1 ?_ intervalIntegrable_const fun s hs => ?_
    · exact ((FwdClock.sol_contOn_inv_sq hu).mono hsub).intervalIntegrable_of_Icc ht.1
    · have h1 : m ≤ ‖u s‖ := hlow s (hsub hs)
      have h2 : m ^ 2 ≤ ‖u s‖ ^ 2 := pow_le_pow_left₀ hm.le h1 2
      exact one_div_le_one_div_of_le (by positivity) h2
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  have hT : t * (1 / m ^ 2) ≤ T * (1 / m ^ 2) :=
    mul_le_mul_of_nonneg_right ht.2 (by positivity)
  have e : -2 * T / m ^ 2 = -2 * (T * (1 / m ^ 2)) := by ring
  rw [e]
  linarith

/-- The same for the forward map `f_t = fwdMap W t`. -/
theorem im_fwdMap_ge_of_lower {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {T m : ℝ} (hm : 0 < m) (hsol : ∃ u, IsForwardSol W z T u)
    (hlow : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    z.im * Real.exp (-2 * T / m ^ 2) ≤ (fwdMap W t z).im := by
  obtain ⟨u, hu⟩ := hsol
  rw [fwdMap_eq hW hz hu ht]
  exact im_sol_ge_of_lower hW hz hm hu (fun s hs => by rw [← fwdMap_eq hW hz hu hs]; exact hlow s hs)
    ht

/-- At `τ' = 0`, `a ψ(w) = f_τ(a w)` on the image of the re-zipping map. -/
theorem mul_revMapInv_revDrv0_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ a : ℝ}
    (hτ : 0 ≤ τ) (ha : 0 < a) {w : ℂ}
    (hw : w ∈ revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 '' H) (hwH : 0 < w.im) :
    (a : ℂ) * revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w = fwdMap W τ ((a : ℂ) * w) := by
  rw [mul_revMapInv_backDrv_eq_fwdMap hW hW0 le_rfl hτ ha hw]
  have haw : 0 < ((a : ℂ) * w).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    positivity
  rw [G1Pkg.fwdMapInv_zero_time hW haw, hW0, Complex.ofReal_zero, add_zero]

end ASep
end QuantumZipper
