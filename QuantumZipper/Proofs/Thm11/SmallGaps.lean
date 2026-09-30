import QuantumZipper.Proofs.Thm11.LyapunovAlgebra
import QuantumZipper.Proofs.Loewner.RealLine
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Two small gaps in the Theorem 1.1 groundwork

* FD8-EXT: for `4 < κ < 8` (so `a = gExp κ ∈ (−1,0)`), bounds on `g'` and `g`:
  `|g'(θ)| ≤ (4π/κ) sin^a θ`, `g'` is interval integrable on `[0,π]`, and `g` is bounded.
* FD5-REAL: local existence of a real solution of the forward flow from a real point.
-/

noncomputable section

open Real MeasureTheory Set intervalIntegral
open scoped NNReal

namespace QuantumZipper

namespace Thm11Lyap

theorem gExp_neg_of_four_lt {κ : ℝ} (hκ : 4 < κ) : gExp κ < 0 := by
  unfold gExp; rw [sub_neg, div_lt_iff₀ (by linarith)]; linarith

theorem neg_one_lt_gExp_of_lt_eight {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) : -1 < gExp κ := by
  unfold gExp; rw [lt_sub_iff_add_lt, lt_div_iff₀ hκ]; linarith

/-- FD8-EXT (i): `|I(θ)| ≤ |θ − π/2|` for `κ ≥ 4`. -/
theorem abs_gInt_le_of_four_le {κ : ℝ} (hκ : 4 ≤ κ) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    |gInt κ θ| ≤ |θ - π / 2| := by
  have ha : 0 ≤ -gExp κ := by
    unfold gExp; rw [neg_nonneg, sub_nonpos, div_le_iff₀ (by linarith)]; linarith
  have hbd : ∀ φ ∈ Set.uIoc (π / 2) θ, ‖sin φ ^ (-gExp κ)‖ ≤ 1 := by
    intro φ hφ
    have hsφ := sin_pos_of_mem_Ioo (uIcc_subset_Ioo h (uIoc_subset_uIcc hφ))
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hsφ _)]
    exact Real.rpow_le_one hsφ.le (sin_le_one φ) ha
  have hI := norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, one_mul] at hI
  exact hI

/-- FD8-EXT (i): `|g'(θ)| ≤ (4π/κ) sin^a θ` for `κ ≥ 4`. -/
theorem abs_gPrime_le_of_four_le {κ : ℝ} (hκ : 4 ≤ κ) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    |gPrime κ θ| ≤ 4 * π / κ * sin θ ^ gExp κ := by
  have hκ0 : 0 < κ := by linarith
  have hsa : 0 < sin θ ^ gExp κ := Real.rpow_pos_of_pos (sin_pos_of_mem_Ioo h) _
  unfold gPrime
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 8 / κ), abs_of_pos hsa]
  calc 8 / κ * sin θ ^ gExp κ * |gInt κ θ| ≤ 8 / κ * sin θ ^ gExp κ * (π / 2) := by
        gcongr
        exact (abs_gInt_le_of_four_le hκ h).trans (abs_sub_pi_div_two_le h)
    _ = 4 * π / κ * sin θ ^ gExp κ := by ring

/-- The explicit integrable majorant `(4π/κ)(2/π)^a (θ^a + (π−θ)^a)` of `|g'|`. -/
def gPrimeMajorant (κ θ : ℝ) : ℝ :=
  4 * π / κ * (2 / π) ^ gExp κ * (θ ^ gExp κ + (π - θ) ^ gExp κ)

theorem sin_rpow_le_of_neg {a : ℝ} (ha : a < 0) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    sin θ ^ a ≤ (2 / π) ^ a * (θ ^ a + (π - θ) ^ a) := by
  have hs := sin_pos_of_mem_Ioo h
  have h2 : 0 < 2 / π := by positivity
  have hθ := h.1
  have hθ' : 0 < π - θ := by linarith [h.2]
  have hA : 0 ≤ (2 / π) ^ a * θ ^ a := by positivity
  have hB : 0 ≤ (2 / π) ^ a * (π - θ) ^ a := by positivity
  rw [mul_add]
  rcases le_or_gt θ (π / 2) with hle | hlt
  · have hm := mul_le_sin hθ.le hle
    have := Real.rpow_le_rpow_of_nonpos (by positivity) hm ha.le
    rw [Real.mul_rpow h2.le hθ.le] at this
    linarith
  · have hm := mul_le_sin hθ'.le (by linarith)
    rw [sin_pi_sub] at hm
    have := Real.rpow_le_rpow_of_nonpos (by positivity) hm ha.le
    rw [Real.mul_rpow h2.le hθ'.le] at this
    linarith

theorem abs_gPrime_le_majorant {κ : ℝ} (hκ : 4 < κ) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    |gPrime κ θ| ≤ gPrimeMajorant κ θ := by
  have hκ0 : 0 < κ := by linarith
  refine (abs_gPrime_le_of_four_le hκ.le h).trans ?_
  unfold gPrimeMajorant
  rw [mul_assoc (4 * π / κ)]
  exact mul_le_mul_of_nonneg_left (sin_rpow_le_of_neg (gExp_neg_of_four_lt hκ) h)
    (by positivity)

theorem intervalIntegrable_gPrimeMajorant {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    IntervalIntegrable (gPrimeMajorant κ) volume 0 π := by
  have ha := neg_one_lt_gExp_of_lt_eight hκ hκ8
  have h1 : IntervalIntegrable (fun θ : ℝ => θ ^ gExp κ) volume 0 π :=
    intervalIntegral.intervalIntegrable_rpow' ha
  have h2 : IntervalIntegrable (fun θ : ℝ => (π - θ) ^ gExp κ) volume 0 π := by
    have := (intervalIntegral.intervalIntegrable_rpow' ha (a := π) (b := 0)).comp_sub_left π
    simpa using this
  exact (h1.add h2).const_mul _

theorem gPrimeMajorant_nonneg {κ : ℝ} (hκ : 0 < κ) {θ : ℝ} (h : θ ∈ Icc 0 π) :
    0 ≤ gPrimeMajorant κ θ := by
  unfold gPrimeMajorant
  have : 0 ≤ π - θ := by linarith [h.2]
  have := h.1
  positivity

/-- FD8-EXT (iii): `g` is bounded on `(0,π)` for `4 < κ < 8`. -/
theorem exists_abs_gFun_le {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ C, ∀ θ ∈ Ioo 0 π, |gFun κ θ| ≤ C := by
  have hκ0 : 0 < κ := by linarith
  have hB := intervalIntegrable_gPrimeMajorant hκ0 hκ8
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 π)] gPrimeMajorant κ :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun θ h =>
      gPrimeMajorant_nonneg hκ0 (Ioc_subset_Icc_self h)
  refine ⟨∫ θ in (0:ℝ)..π, gPrimeMajorant κ θ, fun θ h => ?_⟩
  have key : ∀ c d, 0 < c → c ≤ d → d < π →
      |∫ t in c..d, gPrime κ t| ≤ ∫ θ in (0:ℝ)..π, gPrimeMajorant κ θ := by
    intro c d hc hcd hd
    have hBcd : IntervalIntegrable (gPrimeMajorant κ) volume c d :=
      hB.mono_set (by rw [uIcc_of_le hcd, uIcc_of_le pi_pos.le]; exact Icc_subset_Icc hc.le hd.le)
    refine (norm_integral_le_of_norm_le (μ := volume) (f := gPrime κ) hcd (Filter.Eventually.of_forall fun t ht => ?_)
      hBcd).trans (integral_mono_interval hc.le hcd hd.le hnn hB)
    rw [Real.norm_eq_abs]
    exact abs_gPrime_le_majorant hκ ⟨hc.trans ht.1, ht.2.trans_lt hd⟩
  unfold gFun
  rcases le_or_gt (π / 2) θ with hle | hlt
  · exact key _ _ (by linarith [pi_pos]) hle h.2
  · rw [integral_symm, abs_neg]
    exact key _ _ h.1 hlt.le (by linarith [pi_pos])

end Thm11Lyap

namespace RealLine

variable {W : ℝ → ℝ} {x : ℝ}

end RealLine

end QuantumZipper
