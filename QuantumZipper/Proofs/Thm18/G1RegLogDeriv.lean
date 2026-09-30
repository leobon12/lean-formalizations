import QuantumZipper.Proofs.Thm18.G1Pair
import QuantumZipper.Proofs.Complex.KoebeDistortion

/-!
# G1-REG, part 1: clause (i) of `G1.ChoiceRegular` (Theorem 1.8, node G1)

Clause (i) of `G1.ChoiceRegular` asks that `log ‖ψ'‖` be integrable against every folded
circle `fc(d, r)`, `d ∈ ℍ̄`, `r > 0`, including circles crossing `ℝ`. This holds
**deterministically** for every injective holomorphic `ψ` on `ℍ` (no Hölder regularity of the
boundary, no randomness):

* `G1.abs_log_norm_deriv_le_of_injOn` (Bloch-type growth of `log ψ'`): for `R > 0` there is
  `K` with `|log ‖ψ'(w)‖| ≤ K + C₂ |log Im w|` for all `w ∈ ℍ`, `‖w‖ ≤ R`, where `C₂` is the
  distortion exponent of `CA.Koebe.koebeDistExp`;
* `G1.integrable_log_norm_deriv_foldedCircle_of_injOn`: the integrability on folded circles;
* `G1.choiceRegular_logDeriv`: clause (i) for `ψ = φ⁻¹`, `φ` any normalized uniformizer of an
  open domain (in particular for the components of `ℍ \ η` in Theorem 1.8).

## Sources

The pointwise bound is the Koebe distortion theorem (Garnett–Marshall, *Harmonic Measure*,
Ch. I, Thm 4.5, (4.17), p. 22; Pommerenke, *Univalent Functions*, Thm 1.6, p. 21), in the form
`CA.Koebe.norm_deriv_le_distortion` / `distortion_le_norm_deriv` (exponent `C₂` instead of the
sharp `2`, see D-KOEBE), applied on the disc `B(Re w + iY, Y) ⊆ ℍ`, `Y = R + 1`, which gives
`(Im w / Y)^{C₂} ≤ ‖ψ'(w)‖ / ‖ψ'(Re w + iY)‖ ≤ (Im w / Y)^{−C₂}` (the standard "log ψ' is a Bloch
function" estimate, Pommerenke, *Boundary Behaviour of Conformal Maps*, Prop. 1.2 / §4.1).
The integrability of `log Im` on folded circles is `TwoPoint.integrable_log_im_foldedCircle`.
The assembly (one disc per point, compactness of the top segment) is an own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1

open CA.Koebe

/-- The disc `B(t + iY, Y)` lies in `ℍ`. -/
theorem ball_top_subset_H (t : ℝ) {Y : ℝ} :
    ball ((t : ℂ) + (Y : ℂ) * Complex.I) Y ⊆ H := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  have h1 : |z.im - Y| ≤ ‖z - ((t : ℂ) + (Y : ℂ) * Complex.I)‖ := by
    have := Complex.abs_im_le_norm (z - ((t : ℂ) + (Y : ℂ) * Complex.I))
    simpa using this
  show 0 < z.im
  have := neg_abs_le (z.im - Y)
  linarith

/-- **Bloch-type growth of `log ψ'`** (Koebe distortion on one disc per point). -/
theorem abs_log_norm_deriv_le_of_injOn {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ H)
    (hinj : InjOn ψ H) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, ∀ w ∈ H, ‖w‖ ≤ R →
      |Real.log ‖deriv ψ w‖| ≤ K + koebeDistExp * |Real.log w.im| := by
  set Y : ℝ := R + 1 with hY
  have hY0 : 0 < Y := by linarith
  set c : ℝ → ℂ := fun t => (t : ℂ) + (Y : ℂ) * Complex.I with hc
  have hcH : ∀ t, c t ∈ H := fun t => by
    show 0 < (c t).im
    simp [hc, hY0]
  have hcont : ContinuousOn (fun t => Real.log ‖deriv ψ (c t)‖) (Icc (-R) R) := by
    have hdc : ContinuousOn (deriv ψ) H := (hd.deriv isOpen_H).continuousOn
    have hcc : Continuous c := by fun_prop
    refine ContinuousOn.log ((hdc.comp hcc.continuousOn fun t _ => hcH t).norm) fun t _ => ?_
    exact norm_ne_zero_iff.2 (deriv_ne_zero_of_injOn isOpen_H hd hinj (hcH t))
  obtain ⟨K0, hK0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨K0 + koebeDistExp * |Real.log Y|, fun w hw hwR => ?_⟩
  have hwim : 0 < w.im := hw
  have hre : w.re ∈ Icc (-R) R := by
    have := Complex.abs_re_le_norm w
    exact ⟨by linarith [neg_abs_le w.re], by linarith [le_abs_self w.re]⟩
  have himR : w.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm w).trans hwR)
  have hball := ball_top_subset_H w.re (Y := Y)
  have hdist : dist w (c w.re) = Y - w.im := by
    rw [dist_eq_norm]
    have : w - c w.re = ((w.im - Y : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hc]
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have hwB : w ∈ ball (c w.re) Y := by
    rw [mem_ball, hdist]; linarith
  have hs : 1 - dist w (c w.re) / Y = w.im / Y := by
    rw [hdist]; field_simp; ring
  have hdB := hd.mono hball
  have hiB := hinj.mono hball
  have hup := norm_deriv_le_distortion hdB hiB hwB
  have hlo := distortion_le_norm_deriv hdB hiB hwB
  rw [hs] at hup hlo
  have hpc : 0 < ‖deriv ψ (c w.re)‖ :=
    norm_pos_iff.2 (deriv_ne_zero_of_injOn isOpen_H hd hinj (hcH _))
  have hpw : 0 < ‖deriv ψ w‖ := norm_pos_iff.2 (deriv_ne_zero_of_injOn isOpen_H hd hinj hw)
  have hq : 0 < w.im / Y := div_pos hwim hY0
  have hlogq : Real.log (w.im / Y) = Real.log w.im - Real.log Y :=
    Real.log_div hwim.ne' hY0.ne'
  have hup' := Real.log_le_log hpw hup
  have hlo' := Real.log_le_log (mul_pos hpc (Real.rpow_pos_of_pos hq _)) hlo
  rw [Real.log_mul hpc.ne' (Real.rpow_pos_of_pos hq _).ne', Real.log_rpow hq, hlogq] at hup' hlo'
  have hK := hK0 w.re hre
  rw [Real.norm_eq_abs] at hK
  have hC := koebeDistExp_pos
  have e1 := abs_le.1 hK
  have e2 := neg_abs_le (Real.log w.im)
  have e3 := le_abs_self (Real.log w.im)
  have e4 := neg_abs_le (Real.log Y)
  have e5 := le_abs_self (Real.log Y)
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left e3 hC.le, mul_le_mul_of_nonneg_left e5 hC.le]
  · nlinarith [mul_le_mul_of_nonneg_left e2 hC.le, mul_le_mul_of_nonneg_left e4 hC.le]

/-- **Clause (i), deterministic form.** For `ψ` injective and holomorphic on `ℍ`, `log ‖ψ'‖` is
integrable against every folded circle. -/
theorem integrable_log_norm_deriv_foldedCircle_of_injOn {ψ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ ψ H) (hinj : InjOn ψ H) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r) := by
  obtain ⟨K, hK⟩ := abs_log_norm_deriv_le_of_injOn hd hinj (R := ‖d‖ + r) (by positivity)
  refine ((integrable_const K).add
    ((TwoPoint.integrable_log_im_foldedCircle d hr).abs.const_mul koebeDistExp)).mono'
    (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable ?_
  filter_upwards [TwoPoint.foldedCircle_ae_norm_le d hr.le,
    TwoPoint.foldedCircle_ae_mem_H d hr] with x hx hxH
  rw [Real.norm_eq_abs]
  exact hK x hxH hx

/-- The inverse of a normalized uniformizer is injective on `ℍ`. -/
theorem injOn_invFunOn_of_uniformizer {D : Set ℂ} {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer D φ) : InjOn (invFunOn φ D) H :=
  LeftInvOn.injOn hφ.1.surjOn.rightInvOn_invFunOn

/-- **Clause (i) of `ChoiceRegular`** for `ψ = φ⁻¹`, `φ` a normalized uniformizer of an open
domain `D` (deterministic). -/
theorem choiceRegular_logDeriv {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer D φ) :
    ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv (invFunOn φ D) z‖) (foldedCircle d r) :=
  fun d _ _ hr => integrable_log_norm_deriv_foldedCircle_of_injOn (invFunOn_props hD hφ).1
    (injOn_invFunOn_of_uniformizer hφ) d hr

end G1
end Thm18Asm
end QuantumZipper
