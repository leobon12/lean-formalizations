import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A circle-integral estimate for the capacity rate

Packet PROVE-GEO-LOC2, step (2) (`ȧ = R_t'(W_t)²`, [Law05] §4.6.1). Pure complex analysis, no
Loewner theory.

`norm_div_deriv_sub_mul_deriv_le`: let `F`, `G` be holomorphic near the closed disc
`B̄(x, r)`, `F(x) = y`, `F ≠ y` elsewhere on the disc and `F'(x) ≠ 0`. If on the circle
`|w − x| = r`
`|(G(w) − F(w)) − (h'/(F(w) − y) − G'(w) h/(w − x))| ≤ err`,
then `|h'/F'(x) − h G'(x)| ≤ r · err`.

Proof: integrate over the circle. `∮ (G − F) = 0` (Cauchy), `∮ G'(w)/(w − x) = 2πi G'(x)`
(Cauchy's formula), and `1/(F(w) − y) = (w − x)⁻¹ k(w)⁻¹` with `k = dslope F x` holomorphic and
non-vanishing on the disc, so `∮ 1/(F − y) = 2πi/k(x) = 2πi/F'(x)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

namespace InteractingSLE

namespace ConformalImageFull

/-- **Circle-integral estimate** (residues of `h'/(F − y)` and `G' h/(· − x)` at `x`). -/
theorem norm_div_deriv_sub_mul_deriv_le {F G : ℂ → ℂ} {x y h h' : ℂ} {r r₀ err : ℝ}
    (hr : 0 < r) (hrr : r < r₀) (hF : DifferentiableOn ℂ F (ball x r₀))
    (hG : DifferentiableOn ℂ G (ball x r₀)) (hFx : F x = y)
    (hne : ∀ w ∈ closedBall x r, w ≠ x → F w ≠ y) (hd : deriv F x ≠ 0)
    (hbound : ∀ w ∈ sphere x r,
      ‖(G w - F w) - (h' / (F w - y) - deriv G w * h / (w - x))‖ ≤ err) :
    ‖h' / deriv F x - h * deriv G x‖ ≤ r * err := by
  have hcb : closedBall x r ⊆ ball x r₀ := closedBall_subset_ball hrr
  have hFc : DifferentiableOn ℂ F (closedBall x r) := hF.mono hcb
  have hGc : DifferentiableOn ℂ G (closedBall x r) := hG.mono hcb
  have hG'c : DifferentiableOn ℂ (deriv G) (closedBall x r) :=
    ((hG.analyticOnNhd isOpen_ball).deriv.differentiableOn).mono hcb
  set k := dslope F x with hk
  have hkd : DifferentiableOn ℂ k (ball x r₀) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self (hr.trans hrr)))).2 hF
  have hk0 : ∀ w ∈ closedBall x r, k w ≠ 0 := by
    intro w hw
    by_cases hwx : w = x
    · rw [hwx, hk, dslope_same]; exact hd
    · rw [hk, dslope_of_ne _ hwx, slope_def_field, hFx]
      exact div_ne_zero (sub_ne_zero.2 (hne w hw hwx)) (sub_ne_zero.2 hwx)
  have hkinv : DifferentiableOn ℂ (fun w => (k w)⁻¹) (closedBall x r) :=
    (hkd.mono hcb).inv hk0
  have hFk : ∀ w ∈ sphere x r, F w - y = (w - x) * k w := by
    intro w hw
    have hwx : w ≠ x := ne_of_mem_sphere hw hr.ne'
    rw [hk, dslope_of_ne _ hwx, slope_def_field, hFx]
    field_simp [sub_ne_zero.2 hwx]
  -- the three circle integrals
  have hxb : x ∈ ball x r := mem_ball_self hr
  have I1 : (∮ w in C(x, r), (w - x)⁻¹ • (k w)⁻¹) = (2 * π * I : ℂ) • (k x)⁻¹ :=
    hkinv.circleIntegral_sub_inv_smul hxb
  have I2 : (∮ w in C(x, r), (w - x)⁻¹ • deriv G w) = (2 * π * I : ℂ) • deriv G x :=
    hG'c.circleIntegral_sub_inv_smul hxb
  have I3 : (∮ w in C(x, r), (G w - F w)) = 0 :=
    ((hGc.sub hFc).mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero
      hr.le
  -- integrability
  have hsph : sphere x r ⊆ closedBall x r := sphere_subset_closedBall
  have hcont1 : ContinuousOn (fun w => (w - x)⁻¹ • (k w)⁻¹) (sphere x r) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw =>
      sub_ne_zero.2 (ne_of_mem_sphere hw hr.ne')).smul (hkinv.continuousOn.mono hsph)
  have hcont2 : ContinuousOn (fun w => (w - x)⁻¹ • deriv G w) (sphere x r) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw =>
      sub_ne_zero.2 (ne_of_mem_sphere hw hr.ne')).smul (hG'c.continuousOn.mono hsph)
  have hcont3 : ContinuousOn (fun w => G w - F w) (sphere x r) :=
    (hGc.continuousOn.sub hFc.continuousOn).mono hsph
  set f : ℂ → ℂ := fun w => (G w - F w) -
    (h' * ((w - x)⁻¹ • (k w)⁻¹) - h * ((w - x)⁻¹ • deriv G w)) with hf
  have hfeq : EqOn f (fun w => (G w - F w) - (h' / (F w - y) - deriv G w * h / (w - x)))
      (sphere x r) := by
    intro w hw
    have hwx : w - x ≠ 0 := sub_ne_zero.2 (ne_of_mem_sphere hw hr.ne')
    have hkw : k w ≠ 0 := hk0 w (hsph hw)
    simp only [hf, smul_eq_mul, hFk w hw]
    field_simp
  have hc1 : ContinuousOn (fun w => h' * ((w - x)⁻¹ • (k w)⁻¹)) (sphere x r) :=
    continuousOn_const.mul hcont1
  have hc2 : ContinuousOn (fun w => h * ((w - x)⁻¹ • deriv G w)) (sphere x r) :=
    continuousOn_const.mul hcont2
  have hint : (∮ w in C(x, r), f w) =
      -((2 * π * I : ℂ) * (h' * (k x)⁻¹ - h * deriv G x)) := by
    have e1 : (∮ w in C(x, r), f w) = (∮ w in C(x, r), (G w - F w)) -
        ∮ w in C(x, r), (h' * ((w - x)⁻¹ • (k w)⁻¹) - h * ((w - x)⁻¹ • deriv G w)) :=
      circleIntegral.integral_sub (hcont3.circleIntegrable hr.le)
        ((hc1.sub hc2).circleIntegrable hr.le)
    have e2 : (∮ w in C(x, r), (h' * ((w - x)⁻¹ • (k w)⁻¹) - h * ((w - x)⁻¹ • deriv G w))) =
        (∮ w in C(x, r), h' * ((w - x)⁻¹ • (k w)⁻¹)) -
          ∮ w in C(x, r), h * ((w - x)⁻¹ • deriv G w) :=
      circleIntegral.integral_sub (hc1.circleIntegrable hr.le) (hc2.circleIntegrable hr.le)
    rw [e1, e2, circleIntegral.integral_const_mul, circleIntegral.integral_const_mul, I1,
      I2, I3]
    simp only [smul_eq_mul]
    ring
  have hle := circleIntegral.norm_integral_le_of_norm_le_const (f := f) hr.le fun w hw => by
    rw [hfeq hw]; exact hbound w hw
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hkx : k x = deriv F x := by rw [hk, dslope_same]
  have hnorm : ‖(∮ w in C(x, r), f w)‖ = 2 * π * ‖h' / deriv F x - h * deriv G x‖ := by
    rw [hint, norm_neg, norm_mul, show (2 * π * I : ℂ) = ((2 * π : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi,
      hkx, ← div_eq_mul_inv]
  rw [hnorm] at hle
  have hle' : 2 * π * ‖h' / deriv F x - h * deriv G x‖ ≤ 2 * π * (r * err) := by
    linarith
  exact le_of_mul_le_mul_left hle' hpi

end ConformalImageFull

end InteractingSLE
