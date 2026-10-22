import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Scaling

/-!
# Change from the unit pin to the radius-ten pin (packet P4)

The almost-sure Weyl relation for a constant field shift gives Lemma 2.2(c)
for the mean-log normalized metrics on any set of point pairs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Dividing a two-metric comparison by the positive factor `exp (η Z)`. -/
private theorem p4_pin_change_scalar (ξ η Z c e A B : ℝ) :
    Real.exp (η * Z) * B ≤ c * (Real.exp (ξ * Z) * A) + e ↔
      B ≤ c * Real.exp ((ξ - η) * Z) * A + e * Real.exp (-η * Z) := by
  have hp : 0 < Real.exp (η * Z) := Real.exp_pos _
  have hkey : Real.exp (η * Z) *
      (c * Real.exp ((ξ - η) * Z) * A + e * Real.exp (-η * Z)) =
      c * (Real.exp (ξ * Z) * A) + e := by
    rw [show (ξ - η) * Z = ξ * Z - η * Z by ring,
      Real.exp_sub, show -η * Z = -(η * Z) by ring, Real.exp_neg]
    field_simp
  rw [← hkey]
  exact (mul_le_mul_iff_of_pos_left hp)

/-- Lemma 2.2(c): the comparison after changing to the radius-ten pin,
with the Gaussian pin correction bounded by `exp (ξbar |Z|)`. -/
theorem pin_change {d : ℕ} (hd : 2 ≤ d) {ξ η ξbar : ℝ}
    (_hξ : 0 < ξ) (hη : 0 < η) (hηbar : η ≤ ξbar)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E)
    (X : Set (Rd d)) {c e : ℝ} (_hc : 0 < c) (_he : 0 ≤ e) :
    ∀ᵐ h ∂(normLGFLaw d),
      (let Z := sphereAvg h 10 0
       let g := pin 10 h
       (∀ x ∈ X, ∀ y ∈ X, (rho E h).1 (x, y) ≤ c * (rho D h).1 (x, y) + e) ↔
         (∀ x ∈ X, ∀ y ∈ X,
           (rho E g).1 (x, y) ≤ c * Real.exp ((ξ - η) * Z) * (rho D g).1 (x, y) +
             e * Real.exp (-η * Z))) ∧
      Real.exp (-η * sphereAvg h 10 0) ≤ Real.exp (ξbar * |sphereAvg h 10 0|) := by
  filter_upwards [ae_apply_pin hd hD 10, ae_apply_pin hd hE 10] with h hDh hEh
  let Z := sphereAvg h 10 0
  let g := pin 10 h
  have hDρ (x y : Rd d) : (rho D h).1 (x, y) =
      Real.exp (ξ * Z) * (rho D g).1 (x, y) := by
    rw [rho_apply, rho_apply, hDh x y]
    ring
  have hEρ (x y : Rd d) : (rho E h).1 (x, y) =
      Real.exp (η * Z) * (rho E g).1 (x, y) := by
    rw [rho_apply, rho_apply, hEh x y]
    ring
  constructor
  · constructor
    · intro hcmp x hx y hy
      have hxy := hcmp x hx y hy
      rw [hDρ x y, hEρ x y] at hxy
      exact (p4_pin_change_scalar ξ η Z c e _ _).mp hxy
    · intro hcmp x hx y hy
      have hxy := hcmp x hx y hy
      rw [hDρ x y, hEρ x y]
      exact (p4_pin_change_scalar ξ η Z c e _ _).mpr hxy
  · have hξbar : 0 ≤ ξbar := le_trans hη.le hηbar
    have hbound : -η * Z ≤ ξbar * |Z| := by
      rcases le_total 0 Z with hZ | hZ
      · rw [abs_of_nonneg hZ]
        nlinarith [mul_nonneg (sub_nonneg.mpr hηbar) hZ]
      · rw [abs_of_nonpos hZ]
        nlinarith [mul_nonneg hξbar (neg_nonneg.mpr hZ)]
    exact Real.exp_le_exp.mpr hbound

end HigherDimLQGContinuity
