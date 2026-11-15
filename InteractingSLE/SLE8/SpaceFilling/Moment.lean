import QuantumZipper.Proofs.RS.MartingaleBound
import QuantumZipper.Proofs.RS.TraceGrid
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.RS.TraceMeas

/-!
# κ = 8 space filling, Lemma 3: the reverse derivative moment at `p = 14/9`

Source: the user's note *Space filling of a continuous SLE₈ trace*
(`source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §3, Lemma 3 and its proof, p. 3).

Let `B` be a standard Brownian motion, `W = √8 B`, and `F_t = fwdMapInv (drive 8 B ω) t` the
centred inverse Loewner map `F_t(w) = g_t⁻¹(W_t + w)`. For deterministic `t ≥ 0`, `x ∈ ℝ`, `y > 0`,
`h > 0`, with `p = 14/9`,

`E[(y |F_t'(x+iy)|)^p 1{Im F_t(x+iy) ≥ h}] ≤ h^{-2/9} y^{10/9} (x² + y²)^{1/3}`.     (3.1)

## Proof

By time reversal (pathwise: QuantumZipper's `RS.fwdMapInv_drive_eq_revMap_revBM` and
`RS.deriv_fwdMapInv_eq_deriv_revMap_revBM`), `F_t(z)` and `F_t'(z)` are the value and derivative at
time `t` of the reverse flow `Z_s` (3.2) driven by the reversed Brownian motion
`UnzipInvariance.revBM` (a Brownian motion, `UnzipInvariance.isBrownianReal_revBM`). For that flow,
`M_s = |J_s|^{14/9} Y_s^{-4/9} |Z_s|^{2/3}` is the Rohde–Schramm supermartingale
`Φ^λ Y^ζ (Y/|Z|)^{-2r}` at `κ = 8`, `r = 1/3` (`λ = 14/9`, `ζ = 2/9`), whose expectation bound
`E M_t ≤ M_0` is QuantumZipper's `RS.rs_martingale_bound`. On `{Y_t ≥ h}`, `|Z_t| ≥ Y_t` gives
`M_t ≥ h^{2/9} |J_t|^{14/9}`, and multiplying by `y^{14/9}` gives (3.1).

## Main results

* `lintegral_indicator_rpow_deriv_fwdMapInv_le` — **Lemma 3**, (3.1).
* `lintegral_indicator_rpow_deriv_fwdMapInv_le_of_abs_le` — the "in particular" clause:
  `≤ C_{L,h} y^{10/9}` for `|x| ≤ L`, `0 < y ≤ 1`, with `C_{L,h} = h^{-2/9} (L² + 1)^{1/3}`.
* `measurable_fwdMapInv_deriv_drive` — measurability in `ω` of `F_t(z)` and `|F_t'(z)|` for a
  version of `B` with continuous paths started at `0` (used for Tonelli in Proposition 5).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8.SpaceFilling

open QuantumZipper QuantumZipper.RS

/-- The Rohde–Schramm exponent `λ(8, 1/3) = 14/9`. -/
theorem rsLam_eight_one_third : rsLam 8 (1 / 3) = 14 / 9 := by
  unfold rsLam; norm_num

/-- The Rohde–Schramm exponent `ζ(8, 1/3) = 2/9`. -/
theorem rsZeta_eight_one_third : rsZeta 8 (1 / 3) = 2 / 9 := by
  unfold rsZeta; norm_num

/-- The pointwise inequality behind Lemma 3: on `{Y ≥ h}`, with `0 < Y ≤ N` (`N = |Z|`),
`Φ^{14/9} ≤ h^{-2/9} Φ^{14/9} Y^{2/9} (Y/N)^{-2/3}`. -/
theorem rpow_le_mul_martingale {Φ Y N h : ℝ} (hΦ : 0 ≤ Φ) (hh : 0 < h) (hY : h ≤ Y)
    (hN : Y ≤ N) :
    Φ ^ (14 / 9 : ℝ) ≤
      h ^ (-(2 / 9 : ℝ)) * (Φ ^ (14 / 9 : ℝ) * Y ^ (2 / 9 : ℝ) * (Y / N) ^ (-2 * (1 / 3 : ℝ))) := by
  have hY0 : 0 < Y := hh.trans_le hY
  have hN0 : 0 < N := hY0.trans_le hN
  have h1 : 1 ≤ h ^ (-(2 / 9 : ℝ)) * Y ^ (2 / 9 : ℝ) := by
    rw [Real.rpow_neg hh.le, ← div_eq_inv_mul, ← Real.div_rpow hY0.le hh.le]
    exact Real.one_le_rpow ((one_le_div hh).2 hY) (by norm_num)
  have h2 : 1 ≤ (Y / N) ^ (-2 * (1 / 3 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hY0 hN0) ((div_le_one hN0).2 hN)
      (by norm_num)
  have hΦp : 0 ≤ Φ ^ (14 / 9 : ℝ) := Real.rpow_nonneg hΦ _
  calc Φ ^ (14 / 9 : ℝ) ≤ Φ ^ (14 / 9 : ℝ) * (h ^ (-(2 / 9 : ℝ)) * Y ^ (2 / 9 : ℝ)) *
        (Y / N) ^ (-2 * (1 / 3 : ℝ)) := by
        have h3 : 0 ≤ Φ ^ (14 / 9 : ℝ) * (h ^ (-(2 / 9 : ℝ)) * Y ^ (2 / 9 : ℝ)) := by positivity
        exact (le_mul_of_one_le_right hΦp h1).trans (le_mul_of_one_le_right h3 h2)
    _ = _ := by ring

/-- The constant of Lemma 3: `y^{14/9} h^{-2/9} · y^{2/9} (y/|z|)^{-2/3} = h^{-2/9} y^{10/9}
(x² + y²)^{1/3}` for `z = x + iy`. -/
theorem rpow_mul_martingale_initial_eq (x : ℝ) {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    y ^ (14 / 9 : ℝ) * h ^ (-(2 / 9 : ℝ)) *
        (y ^ (2 / 9 : ℝ) * (y / ‖(x : ℂ) + y * I‖) ^ (-2 * (1 / 3 : ℝ))) =
      h ^ (-(2 / 9 : ℝ)) * y ^ (10 / 9 : ℝ) * (x ^ 2 + y ^ 2) ^ (1 / 3 : ℝ) := by
  have hq : 0 < x ^ 2 + y ^ 2 := by positivity
  have hn : ‖(x : ℂ) + y * I‖ = (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_def, Complex.normSq_add_mul_I, Real.sqrt_eq_rpow]
  have hnp : 0 < (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hq _
  rw [hn, Real.div_rpow hy.le hnp.le, ← Real.rpow_mul hq.le]
  have e1 : y ^ (14 / 9 : ℝ) * y ^ (2 / 9 : ℝ) = y ^ (10 / 9 : ℝ) * y ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hy, ← Real.rpow_add hy]; norm_num
  have e2 : (x ^ 2 + y ^ 2) ^ (1 / 2 * (-2 * (1 / 3)) : ℝ) = ((x ^ 2 + y ^ 2) ^ (1 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hq.le]; norm_num
  have e3 : y ^ (-2 * (1 / 3) : ℝ) = (y ^ (2 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hy.le]; norm_num
  have hy23 : 0 < y ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hy _
  have hq13 : 0 < (x ^ 2 + y ^ 2) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hq _
  rw [e2, e3, div_inv_eq_mul]
  calc y ^ (14 / 9 : ℝ) * h ^ (-(2 / 9 : ℝ)) *
        (y ^ (2 / 9 : ℝ) * ((y ^ (2 / 3 : ℝ))⁻¹ * (x ^ 2 + y ^ 2) ^ (1 / 3 : ℝ)))
      = h ^ (-(2 / 9 : ℝ)) * (y ^ (14 / 9 : ℝ) * y ^ (2 / 9 : ℝ)) * (y ^ (2 / 3 : ℝ))⁻¹ *
          (x ^ 2 + y ^ 2) ^ (1 / 3 : ℝ) := by ring
    _ = _ := by rw [e1]; field_simp

/-- **Lemma 3 (reverse derivative moment).** For chordal SLE₈ (`W = √8 B`), deterministic `t ≥ 0`,
`x ∈ ℝ`, `y > 0`, `h > 0`, and `p = 14/9`:
`E[(y |F_t'(x+iy)|)^p 1{Im F_t(x+iy) ≥ h}] ≤ h^{-2/9} y^{10/9} (x² + y²)^{1/3}` (3.1).
The note fixes `t > 0`; the bound holds for every `t ≥ 0`. -/
theorem lintegral_indicator_rpow_deriv_fwdMapInv_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {t : ℝ} (ht : 0 ≤ t) (x : ℝ)
    {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    ∫⁻ ω, {ω | h ≤ (fwdMapInv (drive 8 B ω) t (x + y * I)).im}.indicator
        (fun ω => ENNReal.ofReal ((y * ‖deriv (fwdMapInv (drive 8 B ω) t) (x + y * I)‖) ^
          (14 / 9 : ℝ))) ω ∂P
      ≤ ENNReal.ofReal (h ^ (-(2 / 9 : ℝ)) * y ^ (10 / 9 : ℝ) * (x ^ 2 + y ^ 2) ^ (1 / 3 : ℝ)) := by
  set z : ℂ := (x : ℂ) + y * I with hz_def
  have hzim : z.im = y := by simp [hz_def]
  have hz : z ∈ H := show 0 < z.im by rw [hzim]; exact hy
  obtain ⟨B'', -, hB''c, hB''0, hB''br, hB''eq⟩ := exists_good_version0 hB
  set R := UnzipInvariance.revBM B'' t.toNNReal with hR
  have hrev : IsBrownianReal R P :=
    UnzipInvariance.isBrownianReal_revBM hB''br.toIsPreBrownianReal hB''c t.toNNReal
  have hm := rs_martingale_bound hrev (κ := 8) (r := 1 / 3) (by norm_num) (by norm_num) ht hz
  rw [rsLam_eight_one_third, rsZeta_eight_one_third, hzim] at hm
  set c : ℝ := y ^ (14 / 9 : ℝ) * h ^ (-(2 / 9 : ℝ)) with hc
  have hc0 : 0 ≤ c := by positivity
  calc ∫⁻ ω, {ω | h ≤ (fwdMapInv (drive 8 B ω) t z).im}.indicator
          (fun ω => ENNReal.ofReal ((y * ‖deriv (fwdMapInv (drive 8 B ω) t) z‖) ^
            (14 / 9 : ℝ))) ω ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal c * ENNReal.ofReal
            (‖deriv (revMap (drive 8 R ω) t) z‖ ^ (14 / 9 : ℝ) *
              (revMap (drive 8 R ω) t z).im ^ (2 / 9 : ℝ) *
              ((revMap (drive 8 R ω) t z).im / ‖revMap (drive 8 R ω) t z‖) ^
                (-2 * (1 / 3 : ℝ))) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hB''eq] with ω hω
        have hdr : drive 8 B ω = drive 8 B'' ω := funext fun s => by simp [drive, hω]
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        split_ifs with hY
        · rw [hdr, fwdMapInv_drive_eq_revMap_revBM 8 B'' ht (hB''c ω) (hB''0 ω) hz] at hY
          rw [hdr, deriv_fwdMapInv_eq_deriv_revMap_revBM 8 ht (hB''c ω) (hB''0 ω) hz,
            ← ENNReal.ofReal_mul hc0]
          refine ENNReal.ofReal_le_ofReal ?_
          have hY0 : 0 < (revMap (drive 8 R ω) t z).im := hh.trans_le hY
          have hN : (revMap (drive 8 R ω) t z).im ≤ ‖revMap (drive 8 R ω) t z‖ :=
            (le_abs_self _).trans (Complex.abs_im_le_norm _)
          have key := rpow_le_mul_martingale (norm_nonneg (deriv (revMap (drive 8 R ω) t) z))
            hh hY hN
          rw [Real.mul_rpow hy.le (norm_nonneg _), hc]
          calc y ^ (14 / 9 : ℝ) * ‖deriv (revMap (drive 8 R ω) t) z‖ ^ (14 / 9 : ℝ)
              ≤ y ^ (14 / 9 : ℝ) * (h ^ (-(2 / 9 : ℝ)) *
                  (‖deriv (revMap (drive 8 R ω) t) z‖ ^ (14 / 9 : ℝ) *
                    (revMap (drive 8 R ω) t z).im ^ (2 / 9 : ℝ) *
                    ((revMap (drive 8 R ω) t z).im / ‖revMap (drive 8 R ω) t z‖) ^
                      (-2 * (1 / 3 : ℝ)))) :=
                mul_le_mul_of_nonneg_left key (by positivity)
            _ = _ := by ring
        · exact zero_le
    _ = ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal
            (‖deriv (revMap (drive 8 R ω) t) z‖ ^ (14 / 9 : ℝ) *
              (revMap (drive 8 R ω) t z).im ^ (2 / 9 : ℝ) *
              ((revMap (drive 8 R ω) t z).im / ‖revMap (drive 8 R ω) t z‖) ^
                (-2 * (1 / 3 : ℝ))) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (y ^ (2 / 9 : ℝ) * (y / ‖z‖) ^ (-2 * (1 / 3 : ℝ))) :=
        mul_le_mul_right hm _
    _ = _ := by
        rw [← ENNReal.ofReal_mul hc0, hc, hz_def, rpow_mul_martingale_initial_eq x hy hh]

/-- **Lemma 3, "in particular".** For `|x| ≤ L` and `0 < y ≤ 1` the expectation in (3.1) is at most
`C_{L,h} y^{10/9}` with `C_{L,h} = h^{-2/9} (L² + 1)^{1/3}`. -/
theorem lintegral_indicator_rpow_deriv_fwdMapInv_le_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {t : ℝ} (ht : 0 ≤ t)
    {L x y h : ℝ} (hx : |x| ≤ L) (hy : 0 < y) (hy1 : y ≤ 1) (hh : 0 < h) :
    ∫⁻ ω, {ω | h ≤ (fwdMapInv (drive 8 B ω) t (x + y * I)).im}.indicator
        (fun ω => ENNReal.ofReal ((y * ‖deriv (fwdMapInv (drive 8 B ω) t) (x + y * I)‖) ^
          (14 / 9 : ℝ))) ω ∂P
      ≤ ENNReal.ofReal (h ^ (-(2 / 9 : ℝ)) * (L ^ 2 + 1) ^ (1 / 3 : ℝ) * y ^ (10 / 9 : ℝ)) := by
  refine (lintegral_indicator_rpow_deriv_fwdMapInv_le hB ht x hy hh).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hxy : x ^ 2 + y ^ 2 ≤ L ^ 2 + 1 := by
    have h1 : x ^ 2 ≤ L ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    have h2 : y ^ 2 ≤ 1 := by nlinarith
    linarith
  have h3 : (x ^ 2 + y ^ 2) ^ (1 / 3 : ℝ) ≤ (L ^ 2 + 1) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hxy (by norm_num)
  calc h ^ (-(2 / 9 : ℝ)) * y ^ (10 / 9 : ℝ) * (x ^ 2 + y ^ 2) ^ (1 / 3 : ℝ)
      ≤ h ^ (-(2 / 9 : ℝ)) * y ^ (10 / 9 : ℝ) * (L ^ 2 + 1) ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- For a version of `B` with continuous paths started at `0`, `ω ↦ F_t(z)` and `ω ↦ |F_t'(z)|`
are measurable (`F_t = fwdMapInv (drive κ B ω) t`, `z ∈ ℍ`). -/
theorem measurable_fwdMapInv_deriv_drive {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    Measurable (fun ω => fwdMapInv (drive κ B ω) t z) ∧
      Measurable (fun ω => ‖deriv (fwdMapInv (drive κ B ω) t) z‖) := by
  refine ⟨measurable_fwdMapInv_drive hBm hBc hB0 κ ht hz, ?_⟩
  have hrm : ∀ s, Measurable (UnzipInvariance.revBM B t.toNNReal s) := fun s => by
    simp only [UnzipInvariance.revBM]
    exact ((hBm _).add (hBm _)).sub ((hBm _).const_smul _)
  have hrc : ∀ ω, Continuous (UnzipInvariance.revBM B t.toNNReal · ω) := fun ω => by
    simp only [UnzipInvariance.revBM_apply]
    fun_prop
  have e : (fun ω => ‖deriv (fwdMapInv (drive κ B ω) t) z‖) =
      fun ω => ‖deriv (revMap (drive κ (UnzipInvariance.revBM B t.toNNReal) ω) t) z‖ :=
    funext fun ω => by rw [deriv_fwdMapInv_eq_deriv_revMap_revBM κ ht (hBc ω) (hB0 ω) hz]
  rw [e]
  exact (measurable_deriv_revMap_drive κ hrm hrc hz ht).norm

end InteractingSLE.SLE8.SpaceFilling
