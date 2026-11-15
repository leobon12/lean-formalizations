import QuantumZipper.Proofs.RS.TailBounds

/-!
# Rohde–Schramm tail bound with `ζ ≤ 0` (the step needed for `κ > 8`)

Design `planning/INFRA-GEO.md` §3 "SLE", packet GEO-RS8; design handoff
`planning/handoffs/INFRA-GEO-ARCH.md` §D.2.

With `W = drive κ B ω`, `u_T = revMap W T z`, `λ = rsLam κ r`, `ζ = rsZeta κ r`, QuantumZipper's
E1 (`QuantumZipper.RS.rs_martingale_bound`) gives
`E[|u_T'|^λ (Im u_T)^ζ (Im u_T/|u_T|)^{−2r}] ≤ (Im z)^ζ (Im z/|z|)^{−2r}`.
QuantumZipper's E2 (`QuantumZipper.RS.rs_tail_bound`) bounds `(Im u_T)^ζ` from below by
`(Im z)^ζ`, which needs `ζ ≥ 0`. For `ζ ≤ 0` we use instead the upper bound
`(Im u_T)² ≤ (Im z)² + 4T` (`QuantumZipper.TwoPoint.im_revMap_sq_le`), which gives
`(Im u_T)^ζ ≥ ((Im z)² + 4T)^{ζ/2}`.

## Main statements (namespace `InteractingSLE`)

* `rsIntegrand_ge_of_rsZeta_nonpos`: on the event `‖u_T'‖ > (Im z)^{β−1}` the E1 integrand is at
  least `(Im z)^{(β−1)λ} ((Im z)² + 4T)^{ζ/2}`.
* `rs_tail_bound_of_rsZeta_nonpos`:
  `P(‖u_T'(z)‖ > (Im z)^{β−1}) ≤ (|z|/Im z)^{2r} ((Im z)² + 4T)^{−ζ/2} (Im z)^{(1−β)λ + ζ}`.
* `rs_tail_bound_axis_of_rsZeta_nonpos`: the same at `z = y i`.
* Exponent arithmetic at `r = rsR1 κ = (8+κ)/(4κ)` for `κ > 8`: `ζ < 0`, `λ > 0`, and
  `(1 − θ)λ + ζ > 2` for `θ < 2(κ−8)²/((8+κ)(8+3κ))` (`two_lt_rsGridExp_of_eight_lt`).

References: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Cor. 3.5
(p. 14) and Thm 3.6 (p. 16); A. Kemppainen, *Schramm–Loewner Evolution* (2017), Thm 5.5 and
Prop. 5.10 (pp. 98–99). The `ζ ≤ 0` variant is the design's own step (handoff §D.2).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-! ### Deterministic lower bound for the E1 integrand when `ζ ≤ 0` -/

/-- On the event `‖u_T'‖ > (Im z)^{β−1}`, for `ζ ≤ 0`, the E1 integrand
`|u_T'|^λ (Im u_T)^ζ (Im u_T/|u_T|)^{−2r}` is at least `(Im z)^{(β−1)λ} ((Im z)² + 4T)^{ζ/2}`. -/
theorem rsIntegrand_ge_of_rsZeta_nonpos {W : ℝ → ℝ} (hW : Continuous W) {κ r T : ℝ}
    (hr : 0 ≤ r) (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H) (hlam : 0 ≤ rsLam κ r)
    (hzeta : rsZeta κ r ≤ 0) {β : ℝ} (hev : z.im ^ (β - 1) < ‖deriv (revMap W T) z‖) :
    z.im ^ ((β - 1) * rsLam κ r) * (z.im ^ 2 + 4 * T) ^ (rsZeta κ r / 2) ≤
      rsIntegrand κ r W T z := by
  have hy : 0 < z.im := hz
  set a := ‖deriv (revMap W T) z‖ with ha
  set Y := (revMap W T z).im with hY
  have hYpos : 0 < Y := TwoPoint.im_revMap_pos hW hz hT
  have hYsq : Y ^ 2 ≤ z.im ^ 2 + 4 * T := TwoPoint.im_revMap_sq_le hW hz hT
  have hc0 : 0 < z.im ^ (β - 1) := Real.rpow_pos_of_pos hy _
  have hA : z.im ^ ((β - 1) * rsLam κ r) ≤ a ^ rsLam κ r := by
    rw [Real.rpow_mul hy.le]
    exact Real.rpow_le_rpow hc0.le hev.le hlam
  have hB : (z.im ^ 2 + 4 * T) ^ (rsZeta κ r / 2) ≤ Y ^ rsZeta κ r := by
    have hYeq : Y ^ rsZeta κ r = (Y ^ 2) ^ (rsZeta κ r / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hYpos.le]
      congr 1
      ring
    rw [hYeq]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hYsq (by linarith)
  have hn : 0 < ‖revMap W T z‖ := hYpos.trans_le (Complex.im_le_norm _)
  have hS : 1 ≤ (Y / ‖revMap W T z‖) ^ (-2 * r) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hYpos hn)
      ((div_le_one hn).2 (Complex.im_le_norm _)) (by linarith)
  have hA0 : 0 ≤ z.im ^ ((β - 1) * rsLam κ r) := (Real.rpow_pos_of_pos hy _).le
  have hB0 : 0 ≤ (z.im ^ 2 + 4 * T) ^ (rsZeta κ r / 2) := Real.rpow_nonneg (by positivity) _
  calc z.im ^ ((β - 1) * rsLam κ r) * (z.im ^ 2 + 4 * T) ^ (rsZeta κ r / 2)
      ≤ a ^ rsLam κ r * Y ^ rsZeta κ r := mul_le_mul hA hB hB0 (hA0.trans hA)
    _ = a ^ rsLam κ r * Y ^ rsZeta κ r * 1 := (mul_one _).symm
    _ ≤ rsIntegrand κ r W T z := by
      unfold rsIntegrand
      exact mul_le_mul_of_nonneg_left hS
        (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hYpos.le _))

/-! ### The tail bound -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **RS tail bound with `ζ ≤ 0`.** For `z ∈ ℍ`, `T ≥ 0`, `r ≥ 0`, `λ ≥ 0`, `ζ ≤ 0`:
`P(‖u_T'(z)‖ > (Im z)^{β−1}) ≤ (|z|/Im z)^{2r} ((Im z)² + 4T)^{−ζ/2} (Im z)^{(1−β)λ + ζ}`.
Markov's inequality applied to E1 (`rs_martingale_bound`) with the lower bound
`rsIntegrand_ge_of_rsZeta_nonpos`, as in RS Cor. 3.5. -/
theorem rs_tail_bound_of_rsZeta_nonpos (hB : IsBrownianReal B P) {κ r T : ℝ} (hκ : 0 < κ)
    (hr : 0 ≤ r) (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H) (hlam : 0 ≤ rsLam κ r)
    (hzeta : rsZeta κ r ≤ 0) (β : ℝ) :
    P {ω | z.im ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) z‖} ≤
      ENNReal.ofReal ((‖z‖ / z.im) ^ (2 * r) * (z.im ^ 2 + 4 * T) ^ (-rsZeta κ r / 2) *
        z.im ^ ((1 - β) * rsLam κ r + rsZeta κ r)) := by
  have hy : 0 < z.im := hz
  have hzn : 0 < ‖z‖ := hy.trans_le (Complex.im_le_norm z)
  have hS0 : 0 < z.im ^ 2 + 4 * T := by positivity
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := WedgeRes.exists_good_version hB
  have hB'mt : ∀ t, Measurable (B' t) := fun t => hB'm.comp measurable_prodMk_left
  have hdr : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω := by
    filter_upwards [hB'eq] with ω hω
    exact funext fun t => by simp only [drive, hω]
  have hE1 : ∫⁻ ω, ENNReal.ofReal (rsIntegrand κ r (drive κ B ω) T z) ∂P
      ≤ ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r)) :=
    rs_martingale_bound hB hκ hr hT hz
  have hE1' : ∫⁻ ω, ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z) ∂P
      ≤ ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r)) := by
    refine le_of_eq_of_le (lintegral_congr_ae ?_) hE1
    filter_upwards [hdr] with ω hω
    rw [hω]
  set c₁ := z.im ^ ((β - 1) * rsLam κ r) with hc₁def
  set c₂ := (z.im ^ 2 + 4 * T) ^ (rsZeta κ r / 2) with hc₂def
  have hc₁ : 0 < c₁ := Real.rpow_pos_of_pos hy _
  have hc₂ : 0 < c₂ := Real.rpow_pos_of_pos hS0 _
  have hc : 0 < c₁ * c₂ := mul_pos hc₁ hc₂
  have hmono : P {ω | z.im ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) z‖}
      ≤ P {ω | ENNReal.ofReal (c₁ * c₂) ≤
          ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z)} := by
    refine measure_mono_ae ?_
    filter_upwards [hdr] with ω hω
    intro hmem
    have hmem' : z.im ^ (β - 1) < ‖deriv (revMap (drive κ B' ω) T) z‖ := by
      rw [hω]; exact hmem
    exact ENNReal.ofReal_le_ofReal (rsIntegrand_ge_of_rsZeta_nonpos
      (NonSwallow.continuous_drive_ns hB'c κ ω) hr hT hz hlam hzeta hmem')
  have hmeas : Measurable fun ω => ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z) := by
    have hd := measurable_deriv_revMap_drive κ hB'mt hB'c hz hT
    have hu := ReverseFlow.measurable_revMap_drive κ B' hB'mt hB'c z hy hT
    have him : Measurable fun ω => (revMap (drive κ B' ω) T z).im :=
      Complex.measurable_im.comp hu
    exact (((hd.norm.pow_const _).mul (him.pow_const _)).mul
      ((him.div hu.norm).pow_const _)).ennreal_ofReal
  have hX : (z.im / ‖z‖) ^ (-2 * r) = (‖z‖ / z.im) ^ (2 * r) := by
    rw [show -2 * r = -(2 * r) by ring, Real.rpow_neg (div_nonneg hy.le hzn.le),
      ← Real.inv_rpow (div_nonneg hy.le hzn.le), inv_div]
  have hc₂inv : (z.im ^ 2 + 4 * T) ^ (-rsZeta κ r / 2) = c₂⁻¹ := by
    rw [hc₂def, ← Real.rpow_neg hS0.le, neg_div]
  have hyexp : z.im ^ ((1 - β) * rsLam κ r + rsZeta κ r) = z.im ^ rsZeta κ r / c₁ := by
    rw [hc₁def, ← Real.rpow_sub hy]
    congr 1
    ring
  calc P {ω | z.im ^ (β - 1) < ‖deriv (revMap (drive κ B ω) T) z‖}
      ≤ P {ω | ENNReal.ofReal (c₁ * c₂) ≤
          ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z)} := hmono
    _ ≤ (∫⁻ ω, ENNReal.ofReal (rsIntegrand κ r (drive κ B' ω) T z) ∂P) /
          ENNReal.ofReal (c₁ * c₂) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable (ENNReal.ofReal_pos.2 hc).ne'
        ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r)) /
          ENNReal.ofReal (c₁ * c₂) :=
      ENNReal.div_le_div_right hE1' _
    _ = ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r) / (c₁ * c₂)) :=
      (ENNReal.ofReal_div_of_pos hc).symm
    _ = ENNReal.ofReal ((‖z‖ / z.im) ^ (2 * r) * (z.im ^ 2 + 4 * T) ^ (-rsZeta κ r / 2) *
          z.im ^ ((1 - β) * rsLam κ r + rsZeta κ r)) := by
      congr 1
      rw [hX, hc₂inv, hyexp]
      field_simp

/-- **RS tail bound with `ζ ≤ 0`, on the imaginary axis** (`z = y i`, so `|z|/Im z = 1`):
`P(‖u_T'(iy)‖ > y^{β−1}) ≤ (y² + 4T)^{−ζ/2} y^{(1−β)λ + ζ}`. This is the step that
QuantumZipper's `rs_tail_bound` (which needs `ζ ≥ 0`) lacks; it uses `Im u_T ≤ √(y² + 4T)`
instead of `Im u_T ≥ y` (design handoff `INFRA-GEO-ARCH` §D.2). -/
theorem rs_tail_bound_axis_of_rsZeta_nonpos (hB : IsBrownianReal B P) {κ r T y : ℝ}
    (hκ : 0 < κ) (hr : 0 ≤ r) (hT : 0 ≤ T) (hy : 0 < y)
    (hlam : 0 ≤ QuantumZipper.RS.rsLam κ r) (hzeta : QuantumZipper.RS.rsZeta κ r ≤ 0) (β : ℝ) :
    P {ω | y ^ (β - 1) < ‖deriv (QuantumZipper.revMap (QuantumZipper.drive κ B ω) T) (y * I)‖} ≤
      ENNReal.ofReal ((y ^ 2 + 4 * T) ^ (-QuantumZipper.RS.rsZeta κ r / 2) *
        y ^ ((1 - β) * QuantumZipper.RS.rsLam κ r + QuantumZipper.RS.rsZeta κ r)) := by
  have him : ((y : ℂ) * I).im = y := by simp
  have hn : ‖(y : ℂ) * I‖ = y := by simp [abs_of_pos hy]
  have hz : (y : ℂ) * I ∈ H := by show 0 < ((y : ℂ) * I).im; rw [him]; exact hy
  have := rs_tail_bound_of_rsZeta_nonpos hB hκ hr hT hz hlam hzeta β
  rwa [him, hn, div_self hy.ne', Real.one_rpow, one_mul] at this

end Tail

/-! ### Exponent arithmetic at `r = rsR1 κ` for `κ > 8` -/

/-- `ζ = (8+κ)(8−κ)/(32κ) < 0` at `r = rsR1 κ` for `κ > 8`. -/
theorem rsZeta_rsR1_neg {κ : ℝ} (hκ : 8 < κ) : rsZeta κ (rsR1 κ) < 0 := by
  rw [rsZeta_rsR1 (by linarith)]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith))
    (by linarith)

/-- `λ = (8+κ)(8+3κ)/(32κ) > 0` at `r = rsR1 κ`. -/
theorem rsLam_rsR1_pos {κ : ℝ} (hκ : 0 < κ) : 0 < rsLam κ (rsR1 κ) := by
  rw [rsLam_rsR1 hκ]; positivity

/-- The admissible range of the grid exponent `θ` for `κ > 8`:
`θ₁(κ) = 2(κ−8)²/((8+κ)(8+3κ))`, i.e. `θ₁ λ = λ + ζ − 2` at `r = rsR1 κ`. -/
def rsTheta1 (κ : ℝ) : ℝ := 2 * (κ - 8) ^ 2 / ((8 + κ) * (8 + 3 * κ))

theorem rsTheta1_pos {κ : ℝ} (hκ : 8 < κ) : 0 < rsTheta1 κ := by
  unfold rsTheta1
  have : 0 < (κ - 8) ^ 2 := by nlinarith
  positivity

theorem rsTheta1_lt_one {κ : ℝ} (hκ : 8 < κ) : rsTheta1 κ < 1 := by
  unfold rsTheta1
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- For `θ < θ₁(κ)` the grid exponent `(1−θ)λ + ζ` at `r = rsR1 κ` exceeds `2`
(`λ + ζ = (8+κ)²/(16κ)` and `(8+κ)² − 32κ = (κ−8)²`). -/
theorem two_lt_rsGridExp_of_eight_lt {κ θ : ℝ} (hκ : 8 < κ) (hθ : θ < rsTheta1 κ) :
    2 < (1 - θ) * rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ) := by
  have hκ0 : 0 < κ := by linarith
  have hL := rsLam_rsR1 hκ0
  have hZ := rsZeta_rsR1 hκ0
  have hLpos := rsLam_rsR1_pos hκ0
  have hkey : rsTheta1 κ * rsLam κ (rsR1 κ) =
      rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ) - 2 := by
    rw [hL, hZ, rsTheta1]
    field_simp
    ring
  have h1 : θ * rsLam κ (rsR1 κ) < rsTheta1 κ * rsLam κ (rsR1 κ) :=
    mul_lt_mul_of_pos_right hθ hLpos
  linarith

end InteractingSLE
