import QuantumZipper.Proofs.RS.MartingaleBound
import QuantumZipper.Proofs.RS.TraceGrid
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.RS.TailBounds

/-!
# The second moment of `|f̂_t'|` at a point of `ℍ`

Packet `planning/packets/PROVE-RS05-74c.md` (positivity in [RS05, Lemma 7.3] for `κ > 8`), input of
the area estimate for `∂K_t` (`planning/handoffs/PROVE-RS05-74.md`, "Details" item 6).

For the centred inverse map `F_t = fwdMapInv (drive κ B ω) t` (`F_t(w) = g_t⁻¹(W_t + w)`) and
`z = x + iy ∈ ℍ`,

`E |F_t'(z)|² ≤ (|z| / y)^{8/κ}`     (all `t ≥ 0`).

Proof. By the time reversal of [RS05, Lemma 3.1] (pathwise: QuantumZipper's
`deriv_fwdMapInv_eq_deriv_revMap_revBM`) `F_t'` is the derivative of the reverse flow driven by the
reversed Brownian motion. For the reverse flow `Z_s = X_s + i Y_s`, `Φ_s = |h_s'(z)|`, the process
`Φ^λ Y^ζ (Y/|Z|)^{−2r}` is a supermartingale ([RS05, Theorem 3.2]; QuantumZipper's
`RS.rs_martingale_bound`) with `λ = r(2 + κ/2) − κr²/2`, `ζ = 2r − κr²/2`. At `r = 4/κ` one gets
`λ = 2`, `ζ = 0`, i.e. `Φ² (|Z|/Y)^{8/κ}`, and `|Z| ≥ Y` gives the bound. This is the
"bulk second moment" `E|f̂_t'(x+iy)|² ≲ y^{−8/κ}` for `|x|` bounded.

## Main results

* `rsLam_four_div`, `rsZeta_four_div`: `λ(κ, 4/κ) = 2`, `ζ(κ, 4/κ) = 0`.
* `lintegral_norm_deriv_revMap_sq_le`: the bound for the reverse flow.
* `lintegral_norm_deriv_fwdMapInv_sq_le`: the bound for `F_t`.
* `measurable_norm_deriv_fwdMapInv`: `ω ↦ |F_t'(z)|` is measurable for a good version of `B`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-- At `r = 4/κ` the Rohde–Schramm exponent `λ` equals `2`. -/
theorem rsLam_four_div {κ : ℝ} (hκ : 0 < κ) : rsLam κ (4 / κ) = 2 := by
  unfold rsLam
  field_simp
  ring

/-- At `r = 4/κ` the Rohde–Schramm exponent `ζ` vanishes. -/
theorem rsZeta_four_div {κ : ℝ} (hκ : 0 < κ) : rsZeta κ (4 / κ) = 0 := by
  unfold rsZeta
  field_simp
  ring

/-- `1 ≤ (Y/|Z|)^{−8/κ}` for `Z` in the upper half-plane. -/
theorem one_le_im_div_norm_rpow {κ : ℝ} (hκ : 0 < κ) {u : ℂ} (hu : 0 < u.im) :
    1 ≤ (u.im / ‖u‖) ^ (-2 * (4 / κ)) := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 fun h => by simp [h] at hu
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hu hn) ?_ ?_
  · rw [div_le_one hn]
    exact (Complex.abs_im_le_norm u).trans' (le_abs_self _)
  · have : 0 < 4 / κ := by positivity
    linarith

/-- **Second moment of the reverse-flow derivative** ([RS05, Theorem 3.2] at `r = 4/κ`):
`E |h_T'(z)|² ≤ (|z|/Im z)^{8/κ}`. -/
theorem lintegral_norm_deriv_revMap_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) :
    ∫⁻ ω, ENNReal.ofReal (‖deriv (revMap (drive κ B ω) T) z‖ ^ 2) ∂P
      ≤ ENNReal.ofReal ((‖z‖ / z.im) ^ (8 / κ)) := by
  have hr : (0 : ℝ) ≤ 4 / κ := by positivity
  have h := rs_martingale_bound hB hκ hr hT hz
  rw [rsLam_four_div hκ, rsZeta_four_div hκ] at h
  have hz' : 0 < z.im := hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 fun h0 => by simp [h0] at hz'
  have hrhs : z.im ^ (0 : ℝ) * (z.im / ‖z‖) ^ (-2 * (4 / κ)) = (‖z‖ / z.im) ^ (8 / κ) := by
    rw [Real.rpow_zero, one_mul, show -2 * (4 / κ) = -(8 / κ) by ring,
      Real.rpow_neg (div_pos hz' hzn).le, ← Real.inv_rpow (div_pos hz' hzn).le, inv_div]
  rw [hrhs] at h
  refine le_trans (lintegral_mono_ae ?_) h
  filter_upwards [hB.cont] with ω hc
  refine ENNReal.ofReal_le_ofReal ?_
  have hu : 0 < (revMap (drive κ B ω) T z).im := TwoPoint.im_revMap_pos (drive_continuous hc) hz hT
  rw [Real.rpow_zero, mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact le_mul_of_one_le_right (by positivity) (one_le_im_div_norm_rpow hκ hu)

/-- **Second moment of `|F_t'(z)|`**: `E |F_t'(z)|² ≤ (|z|/Im z)^{8/κ}` for the centred inverse
SLE map `F_t = fwdMapInv (drive κ B ω) t`, every `t ≥ 0`, `z ∈ ℍ`. -/
theorem lintegral_norm_deriv_fwdMapInv_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H) :
    ∫⁻ ω, ENNReal.ofReal (‖deriv (fwdMapInv (drive κ B ω) t) z‖ ^ 2) ∂P
      ≤ ENNReal.ofReal ((‖z‖ / z.im) ^ (8 / κ)) := by
  obtain ⟨B'', hB''m, hB''c, hB''0, hB''br, hB''eq⟩ := exists_good_version0 hB
  have hrev : IsBrownianReal (UnzipInvariance.revBM B'' t.toNNReal) P :=
    UnzipInvariance.isBrownianReal_revBM hB''br.toIsPreBrownianReal hB''c t.toNNReal
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (lintegral_norm_deriv_revMap_sq_le hrev hκ ht hz)
  filter_upwards [hB''eq] with ω hω
  have hdr : drive κ B ω = drive κ B'' ω := funext fun s => by simp [drive, hω]
  rw [hdr, deriv_fwdMapInv_eq_deriv_revMap_revBM κ ht (hB''c ω) (hB''0 ω) hz]

/-- For a version of `B` with continuous paths started at `0`, `ω ↦ |F_t'(z)|` is measurable. -/
theorem measurable_norm_deriv_fwdMapInv {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    Measurable fun ω => ‖deriv (fwdMapInv (drive κ B ω) t) z‖ := by
  have hrm : ∀ s, Measurable (UnzipInvariance.revBM B t.toNNReal s) := fun s => by
    simp only [UnzipInvariance.revBM]
    exact ((hBm _).add (hBm _)).sub ((hBm _).const_smul _)
  have hrc : ∀ ω, Continuous (UnzipInvariance.revBM B t.toNNReal · ω) := fun ω => by
    simp only [UnzipInvariance.revBM_apply]
    fun_prop
  have h := (measurable_deriv_revMap_drive κ hrm hrc hz ht).norm
  have e : (fun ω => ‖deriv (fwdMapInv (drive κ B ω) t) z‖) =
      fun ω => ‖deriv (revMap (drive κ (UnzipInvariance.revBM B t.toNNReal) ω) t) z‖ :=
    funext fun ω => by rw [deriv_fwdMapInv_eq_deriv_revMap_revBM κ ht (hBc ω) (hB0 ω) hz]
  rw [e]
  exact h

end InteractingSLE
