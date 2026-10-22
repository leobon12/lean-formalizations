import HigherDimLQGContinuity.MarginalEuclid.Grid
import HigherDimLQGContinuity.MarginalEuclid.PairEuclid

/-! Moments of the finite grid error. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- An ℓ^q majorant of the grid maximum. -/
def euclidGridSum {d : ℕ} (D : ContMetric d) (R s q : ℝ) : ℝ≥0∞ :=
  (∑ p ∈ euclidGrid (d := d) R s ×ˢ euclidGrid R s,
    edist (D.1 p) (euclidDistC d p) ^ q) ^ (1 / q)

theorem euclidGridErr_le_sum {d : ℕ} (D : ContMetric d) (R s : ℝ)
    {q : ℝ} (hq : 0 < q) : euclidGridErr D R s ≤ euclidGridSum D R s q := by
  unfold euclidGridErr euclidGridSum
  exact iSup₂_le fun p hp => GaussianLQG.le_rpow_sum_rpow _
    (fun p => edist (D.1 p) (euclidDistC d p)) hq hp

theorem measurable_grid_pair_error {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (p : Rd d × Rd d) :
    Measurable fun g => edist ((rho D g).1 p) (euclidDistC d p) :=
  (p2_measurable_contMetric_apply (measurable_rho hD) p).edist measurable_const

theorem measurable_euclidGridSum {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (R s q : ℝ) :
    Measurable fun g => euclidGridSum (rho D g) R s q := by
  unfold euclidGridSum
  exact (Finset.measurable_sum _ fun p _ =>
    (measurable_grid_pair_error hD p).pow_const q).pow_const (1 / q)

theorem eLpNorm_grid_pair_error_le {d : ℕ} {D : DistRd d → ContMetric d}
    {R q C ξ : ℝ}
    (hpair : ∀ x y : Rd d, ‖x‖ ≤ R → ‖y‖ ≤ R →
      eLpNorm (fun g => (rho D g).1 (x, y) - dist x y)
        (ENNReal.ofReal q) (normLGFLaw d) ≤ ENNReal.ofReal (C * ξ))
    (p : Rd d × Rd d) (hp : ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R) :
    eLpNorm (fun g => edist ((rho D g).1 p) (euclidDistC d p))
      (ENNReal.ofReal q) (normLGFLaw d) ≤ ENNReal.ofReal (C * ξ) := by
  have heq : eLpNorm (fun g => edist ((rho D g).1 p) (euclidDistC d p))
      (ENNReal.ofReal q) (normLGFLaw d) =
      eLpNorm (fun g => (rho D g).1 (p.1, p.2) - dist p.1 p.2)
        (ENNReal.ofReal q) (normLGFLaw d) := by
    apply eLpNorm_congr_enorm_ae
    filter_upwards [] with g
    simp [euclidDistC, edist_dist, Real.dist_eq, Real.enorm_eq_ofReal_abs]
  rw [heq]
  exact hpair p.1 p.2 hp.1 hp.2

theorem eLpNorm_euclidGridSum_le {d : ℕ}
    {D : DistRd d → ContMetric d} (hD : Measurable D)
    {R s q C ξ : ℝ}
    (hq : 1 ≤ q)
    (hpair : ∀ x y : Rd d, ‖x‖ ≤ 2 * (R + 1) → ‖y‖ ≤ 2 * (R + 1) →
      eLpNorm (fun g => (rho D g).1 (x, y) - dist x y)
        (ENNReal.ofReal q) (normLGFLaw d) ≤ ENNReal.ofReal (C * ξ)) :
    eLpNorm (fun g => euclidGridSum (rho D g) R s q)
      (ENNReal.ofReal q) (normLGFLaw d) ≤
        (((euclidGrid (d := d) R s ×ˢ euclidGrid (d := d) R s).card : ℝ≥0∞) ^ (1 / q)) *
          ENNReal.ofReal (C * ξ) := by
  apply GaussianLQG.eLpNorm_rpow_sum_rpow_le
    (euclidGrid (d := d) R s ×ˢ euclidGrid R s)
  · intro p hp
    exact measurable_grid_pair_error hD p
  · linarith
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    have h1 := w3b_norm_lt_of_mem_grid (show p.1 ∈ euclidGrid R s from hp'.1)
    have h2 := w3b_norm_lt_of_mem_grid (show p.2 ∈ euclidGrid R s from hp'.2)
    have hb : ‖p.1‖ ≤ 2 * (R + 1) ∧ ‖p.2‖ ≤ 2 * (R + 1) := by
      constructor <;> nlinarith
    exact eLpNorm_grid_pair_error_le hpair p hb

/-- The number of ordered grid pairs grows at most as the mesh to `-2d`. -/
theorem euclidGrid_pair_card_le {d : ℕ} (hd : 1 ≤ d)
    {R s : ℝ} (hR : 1 ≤ R) (hs : 0 < s) (hs1 : s ≤ 1) :
    ((euclidGrid (d := d) R s ×ˢ euclidGrid (d := d) R s).card : ℝ) ≤
      (((32 * (d : ℝ) + 5) * (R + 1)) / s) ^ (2 * d) := by
  have hR1 : 0 < R + 1 := by linarith
  have hε : 0 < s / (R + 1) := by positivity
  have hε1 : s / (R + 1) ≤ 1 := (div_le_one hR1).2 (by linarith)
  have hcard := w3b_card_grid_le hd (by norm_num : (0 : ℝ) < 1) hR1 hε hε1
  have hcard' : ((euclidGrid (d := d) R s).card : ℝ) ≤
      (((32 * (d : ℝ) + 5) * (R + 1)) / s) ^ d := by
    simpa only [euclidGrid] using
      (calc
        ((w3bGrid d 1 (R + 1) (s / (R + 1))).card : ℝ) ≤
            (16 * (d : ℝ) * (1 + 1) + 5) ^ d / (s / (R + 1)) ^ d := hcard
        _ = (((32 * (d : ℝ) + 5) * (R + 1)) / s) ^ d := by
          rw [← div_pow]
          congr 1
          field_simp
          ring)
  calc
    (((euclidGrid (d := d) R s ×ˢ euclidGrid (d := d) R s).card : ℝ)) =
        ((euclidGrid (d := d) R s).card : ℝ) ^ 2 := by
          rw [Finset.card_product]
          push_cast
          ring
    _ ≤ ((((32 * (d : ℝ) + 5) * (R + 1)) / s) ^ d) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcard' 2
    _ = (((32 * (d : ℝ) + 5) * (R + 1)) / s) ^ (2 * d) := by
          rw [← pow_mul]
          congr 1
          omega

/-- Integrate a three-term grid filling inequality. -/
theorem n5_lintegral_grid_fill {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T G H : Ω → ℝ≥0∞) (hG : Measurable G) (hH : Measurable H)
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (a b B K : ℝ≥0∞) (ha : a ≠ ⊤)
    (hpath : ∀ ω, T ω ≤ G ω + a * H ω + b)
    (hGq : eLpNorm G (ENNReal.ofReal q) μ ≤ B)
    (hHp : ∫⁻ ω, H ω ^ p ∂μ ≤ K) :
    ∫⁻ ω, T ω ^ p ∂μ ≤
      (2 : ℝ≥0∞) ^ p * ((2 : ℝ≥0∞) ^ p * (B ^ p + a ^ p * K) + b ^ p) := by
  have hp0 : 0 < p := by linarith
  have hGpq : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal hpq
  have hGp : eLpNorm G (ENNReal.ofReal p) μ ≤ B :=
    (eLpNorm_le_eLpNorm_of_exponent_le hGpq hG.aestronglyMeasurable).trans hGq
  have hGint : ∫⁻ ω, G ω ^ p ∂μ ≤ B ^ p := by
    rw [GaussianLQG.eLpNorm_ofReal_eq hp0] at hGp
    simp_rw [enorm_eq_self] at hGp
    have hh := ENNReal.rpow_le_rpow hGp hp0.le
    simpa only [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] using hh
  have hpoint (ω : Ω) : T ω ^ p ≤
      (2 : ℝ≥0∞) ^ p * ((2 : ℝ≥0∞) ^ p *
        (G ω ^ p + a ^ p * H ω ^ p) + b ^ p) := by
    have hfirst := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      (G ω + a * H ω) b hp0.le
    have hsecond := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      (G ω) (a * H ω) hp0.le
    calc
      T ω ^ p ≤ (G ω + a * H ω + b) ^ p :=
        ENNReal.rpow_le_rpow (hpath ω) hp0.le
      _ ≤ (2 : ℝ≥0∞) ^ p * ((G ω + a * H ω) ^ p + b ^ p) := hfirst
      _ ≤ (2 : ℝ≥0∞) ^ p *
          ((2 : ℝ≥0∞) ^ p * (G ω ^ p + (a * H ω) ^ p) + b ^ p) := by gcongr
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  have hmeasG : Measurable fun ω => G ω ^ p := hG.pow_const p
  have hmeasH : Measurable fun ω => H ω ^ p := hH.pow_const p
  have hconst : (2 : ℝ≥0∞) ^ p ≠ ⊤ := by finiteness
  calc
    ∫⁻ ω, T ω ^ p ∂μ ≤
        ∫⁻ ω, (2 : ℝ≥0∞) ^ p *
          ((2 : ℝ≥0∞) ^ p * (G ω ^ p + a ^ p * H ω ^ p) + b ^ p) ∂μ :=
          lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) ^ p *
        ((2 : ℝ≥0∞) ^ p *
          ((∫⁻ ω, G ω ^ p ∂μ) + a ^ p * (∫⁻ ω, H ω ^ p ∂μ)) + b ^ p) := by
          rw [lintegral_const_mul' _ _ hconst]
          rw [lintegral_add_left (f := fun ω =>
            (2 : ℝ≥0∞) ^ p * (G ω ^ p + a ^ p * H ω ^ p))
            ((hmeasG.add (measurable_const.mul hmeasH)).const_mul _),
            lintegral_const_mul' _ _ hconst,
            lintegral_add_left (f := fun ω => G ω ^ p) hmeasG,
            lintegral_const_mul' _ _ (by finiteness : a ^ p ≠ ⊤)]
          · simp [lintegral_const, measure_univ]
    _ ≤ (2 : ℝ≥0∞) ^ p * ((2 : ℝ≥0∞) ^ p * (B ^ p + a ^ p * K) + b ^ p) := by
          gcongr

/-- Grid growth is absorbed by a high enough fixed moment order. -/
theorem n5_grid_card_power_bound {n d : ℕ} {K C ξ q r : ℝ}
    (hK : 0 < K) (hC : 0 ≤ C) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hq : 0 < q) (hr : r ≤ 1 - 2 * d / q)
    (hn : (n : ℝ) ≤ (K / ξ) ^ (2 * d)) :
    (n : ℝ≥0∞) ^ (1 / q) * ENNReal.ofReal (C * ξ) ≤
      ENNReal.ofReal (K ^ (2 * d / q) * C * ξ ^ r) := by
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hKξ : 0 ≤ K / ξ := by positivity
  have he : 0 ≤ 2 * (d : ℝ) / q := by positivity
  have hξe : 0 < ξ ^ (2 * (d : ℝ) / q) := Real.rpow_pos_of_pos hξ _
  have hn' : (n : ℝ) ^ (1 / q) ≤
      K ^ (2 * d / q) / ξ ^ (2 * d / q) := by
    calc
      (n : ℝ) ^ (1 / q) ≤ ((K / ξ) ^ (2 * d)) ^ (1 / q) :=
        Real.rpow_le_rpow hN hn (by positivity)
      _ = (K / ξ) ^ (2 * d / q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hKξ]
        congr 1
        push_cast
        field_simp
      _ = K ^ (2 * d / q) / ξ ^ (2 * d / q) := Real.div_rpow hK.le hξ.le _
  have hreal : (n : ℝ) ^ (1 / q) * (C * ξ) ≤
      K ^ (2 * d / q) * C * ξ ^ r := by
    calc
      (n : ℝ) ^ (1 / q) * (C * ξ) ≤
          K ^ (2 * d / q) / ξ ^ (2 * d / q) * (C * ξ) :=
            mul_le_mul_of_nonneg_right hn' (mul_nonneg hC hξ.le)
      _ = K ^ (2 * d / q) * C * ξ ^ (1 - 2 * d / q) := by
        rw [Real.rpow_sub hξ, Real.rpow_one]
        field_simp
      _ ≤ K ^ (2 * d / q) * C * ξ ^ r := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hξ hξ1 hr)
          (mul_nonneg (Real.rpow_nonneg hK.le _) hC)
  have hconv : (n : ℝ≥0∞) ^ (1 / q) * ENNReal.ofReal (C * ξ) =
      ENNReal.ofReal ((n : ℝ) ^ (1 / q) * (C * ξ)) := by
    rw [← ENNReal.ofReal_natCast n,
      ENNReal.ofReal_rpow_of_nonneg hN (by positivity),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hN _)]
  rw [hconv]
  exact ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGContinuity
