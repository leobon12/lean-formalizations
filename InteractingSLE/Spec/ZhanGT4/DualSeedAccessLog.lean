/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessTransport
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteSource

/-!
# Opposite-time rates of the normalized seed factors

Packet PROVE-ZHAN-GT4-A22. The original source is separated from the second
curve. Normalize the opposite-flow divided difference by the original map's
derivative at that source. Its logarithmic derivative is regular even when
the two fixed accesses coincide: the diagonal gives (D13), the off-diagonal
cases (D14) and (D15).
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)

namespace OwnData

variable {W U b : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ}
    (h : OwnData W A φ T b U)
include h

/-- Logarithmic evolution of the opposite-flow divided difference, with
its derivative value on the diagonal. -/
theorem hasDerivWithinAt_log_dslope_frzImg {u v : ℝ} {q r : ℝ → ℂ}
    (hq : IsForwardSol U (u : ℂ) (b T) q)
    (hr : IsForwardSol U (v : ℂ) (b T) r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun y => Real.log (dslope (fun x => frzImg U b x y) u v))
      (-2 * frzA W U b φ 1 t ^ 2 /
        ((frzImg U b u t - frzA W U b φ 0 t) *
          (frzImg U b v t - frzA W U b φ 0 t))) (Icc 0 T) t := by
  have hD := (h.dslope_frzImg_pos hq hr ht).ne'
  have hd := (h.hasDerivWithinAt_dslope_frzImg hq hr ht).log hD
  refine hd.congr_deriv ?_
  field_simp

omit h in
/-- The logarithm of the original derivative at a separated source obeys
its usual variational equation on the closed time interval. -/
theorem hasDerivWithinAt_log_source_deriv (hW : Continuous W) {p : ℝ} {q : ℝ → ℂ}
    (hq : IsForwardSol W (p : ℂ) T q) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun y => Real.log (deriv (fwdMap W y) p).re)
      (-2 / (fwdMap W t p).re ^ 2) (Icc 0 T) t := by
  have hG := (deriv_fwdMap_real hW hq ht).2.ne'
  have hd := ((source_gmap_rates hW hq ht).2).log hG
  refine hd.congr_deriv ?_
  simp only [add_sub_cancel_right]
  field_simp

/-- **Normalized (D13)--(D15) in the opposite time direction.** The formula
is valid for equal seed accesses; there is no singular initial-gap term. -/
theorem hasDerivWithinAt_log_normalized_dslope (hW : Continuous W) {u v p : ℝ} {q r q₀ : ℝ → ℂ}
    (hq : IsForwardSol U (u : ℂ) (b T) q)
    (hr : IsForwardSol U (v : ℂ) (b T) r)
    (hq₀ : IsForwardSol W (p : ℂ) T q₀) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (fun y => Real.log (dslope (fun x => frzImg U b x y) u v /
        (deriv (fwdMap W y) p).re))
      (-2 * frzA W U b φ 1 t ^ 2 /
        ((frzImg U b u t - frzA W U b φ 0 t) *
          (frzImg U b v t - frzA W U b φ 0 t)) + 2 / (fwdMap W t p).re ^ 2)
      (Icc 0 T) t := by
  have hd := (h.hasDerivWithinAt_log_dslope_frzImg hq hr ht).sub
    (hasDerivWithinAt_log_source_deriv hW hq₀ ht)
  have he (y : ℝ) (hy : y ∈ Icc (0 : ℝ) T) :
      Real.log (dslope (fun x => frzImg U b x y) u v / (deriv (fwdMap W y) p).re) =
        Real.log (dslope (fun x => frzImg U b x y) u v) -
          Real.log (deriv (fwdMap W y) p).re :=
    Real.log_div (h.dslope_frzImg_pos hq hr hy).ne'
      (deriv_fwdMap_real hW hq₀ hy).2.ne'
  simpa only [neg_div, sub_neg_eq_add] using hd.congr he (he t ht)

end OwnData
end InteractingSLE.ZhanGT4
