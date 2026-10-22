import HigherDimLQGContinuity.Continuum.Moments
import HigherDimLQGMetric.Sec4.Lemma45Geom

/-!
# Point distances from local buffered diameters

A fixed straight segment is divided into finitely many steps. The local
buffered-diameter bound controls each step, giving a positive moment of a
point distance without a general compact-cover argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem l2_pair_le_localDiam {d : ℕ} (D : ContMetric d) {z u v : Rd d}
    {H : ℝ} (hH : 0 ≤ H) (hu : u ∈ ball z 1) (hv : v ∈ ball z 1)
    (hdiam : internalDiamRd D (ball z 1) (ball z 2) ≤ ENNReal.ofReal H) :
    D.1 (u, v) ≤ H := by
  have hle : ENNReal.ofReal (D.1 (u, v)) ≤ ENNReal.ofReal H := by
    calc
      ENNReal.ofReal (D.1 (u, v)) ≤ D.internal (ball z 2) u v :=
        D.ofReal_le_internal _ _ _
      _ ≤ internalDiamRd D (ball z 1) (ball z 2) :=
        le_iSup₂_of_le u hu (le_iSup₂_of_le v hv le_rfl)
      _ ≤ ENNReal.ofReal H := hdiam
  exact (ENNReal.ofReal_le_ofReal_iff hH).1 hle

/-- Finitely many unit buffered balls control one fixed point distance. -/
theorem l2_point_le_local {d : ℕ} (D : ContMetric d) (x y : Rd d)
    (n : ℕ) (hn : 0 < n) (hstep : ‖y - x‖ < n) {H : ℝ} (hH : 0 ≤ H)
    (hlocal : ∀ z ∈ closedBall (0 : Rd d) (‖x‖ + ‖y - x‖ + 1),
      internalDiamRd D (ball z 1) (ball z 2) ≤ ENNReal.ofReal H) :
    D.1 (x, y) ≤ n * H := by
  let w : ℕ → Rd d := fun i => x + ((i : ℝ) / n) • (y - x)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hw0 : w 0 = x := by simp [w]
  have hwn : w n = y := by
    simp [w, hn.ne']
  have hmem (i : ℕ) (hi : i ≤ n) :
      w i ∈ closedBall (0 : Rd d) (‖x‖ + ‖y - x‖ + 1) := by
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hi1 : (i : ℝ) ≤ n := by exact_mod_cast hi
    have ha0 : 0 ≤ (i : ℝ) / n := div_nonneg hi0 hnreal.le
    have ha1 : (i : ℝ) / n ≤ 1 := (div_le_iff₀ hnreal).2 (by simpa using hi1)
    have htri : ‖w i‖ ≤ ‖x‖ + ((i : ℝ) / n) * ‖y - x‖ := by
      calc
        ‖w i‖ = ‖x + ((i : ℝ) / n) • (y - x)‖ := rfl
        _ ≤ ‖x‖ + ‖((i : ℝ) / n) • (y - x)‖ := norm_add_le _ _
        _ = ‖x‖ + ((i : ℝ) / n) * ‖y - x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
    have hm : ((i : ℝ) / n) * ‖y - x‖ ≤ ‖y - x‖ :=
      (mul_le_mul_of_nonneg_right ha1 (norm_nonneg _)).trans_eq (one_mul _)
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hsub (i : ℕ) : w (i + 1) - w i = (n : ℝ)⁻¹ • (y - x) := by
    simp only [w, Nat.cast_add, Nat.cast_one]
    module
  have hnear (i : ℕ) : w (i + 1) ∈ ball (w i) 1 := by
    rw [mem_ball, dist_eq_norm, hsub]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnreal)]
    rw [← div_eq_inv_mul]
    exact (div_lt_iff₀ hnreal).2 (by simpa only [one_mul] using hstep)
  have hbound : ∀ i : ℕ, i ≤ n → D.1 (x, w i) ≤ (i : ℝ) * H := by
    intro i
    induction i with
    | zero =>
        intro _
        rw [hw0, D.apply_self]
        simp
    | succ i ih =>
        intro hi
        have hin : i ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi)
        have hwi : w i ∈ ball (w i) 1 := mem_ball_self (by norm_num)
        have hstepBound : D.1 (w i, w (i + 1)) ≤ H :=
          l2_pair_le_localDiam D hH hwi (hnear i) (hlocal (w i) (hmem i hin))
        have htri := D.2.triangle x (w i) (w (i + 1))
        have hprev := ih hin
        push_cast
        linarith
  simpa only [hwn] using hbound n le_rfl

/-- Uniform positive moments of each fixed point distance from the local Fatou envelope. -/
theorem continuum_point_upper {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d)) (x y : Rd d) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y)) ^ p ∂(normLGFLaw d) ≤
          ENNReal.ofReal C := by
  obtain ⟨C₀, A, hfatou⟩ := continuum_fatou hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
  let R : ℝ := ‖x‖ + ‖y - x‖ + 1
  have hR : 1 ≤ R := by
    dsimp [R]
    have hx := norm_nonneg x
    have hxy := norm_nonneg (y - x)
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ‖y - x‖
  have hn0 : 0 < n := by
    have hnorm := norm_nonneg (y - x)
    exact_mod_cast (show (0 : ℝ) < n by linarith)
  let C : ℝ := (n : ℝ) ^ p * (C₀ * (1 + R) ^ A)
  refine ⟨C, fun ξ hξ D hD => ?_⟩
  obtain ⟨H, hHm, hH1, hHmom, hHpt⟩ :=
    (hfatou ξ hξ D hD).2 R hR
  have hpoint : ∀ᵐ g ∂(normLGFLaw d),
      (rho D g).1 (x, y) ≤ (n : ℝ) * H g := by
    filter_upwards [hHpt] with g hg
    apply l2_point_le_local (rho D g) x y n hn0 hn (le_trans zero_le_one (hH1 g))
    intro z hz
    simpa only [mul_one, Real.one_rpow] using
      hg z hz 1 ⟨by norm_num, le_rfl⟩
  have hbound : ∀ᵐ g ∂(normLGFLaw d),
      ENNReal.ofReal ((rho D g).1 (x, y)) ^ p ≤
        ENNReal.ofReal ((n : ℝ) ^ p) * ENNReal.ofReal (H g ^ p) := by
    filter_upwards [hpoint] with g hg
    have hnp : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hHg : 0 ≤ H g := (hH1 g).trans' zero_le_one
    calc
      ENNReal.ofReal ((rho D g).1 (x, y)) ^ p ≤
          ENNReal.ofReal ((n : ℝ) * H g) ^ p := by gcongr
      _ = ENNReal.ofReal ((n : ℝ) ^ p) * ENNReal.ofReal (H g ^ p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hnp hHg) hp.le,
          Real.mul_rpow hnp hHg,
          ENNReal.ofReal_mul (Real.rpow_nonneg hnp _)]
  calc
    (∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y)) ^ p ∂(normLGFLaw d)) ≤
        ∫⁻ g, ENNReal.ofReal ((n : ℝ) ^ p) * ENNReal.ofReal (H g ^ p)
          ∂(normLGFLaw d) := lintegral_mono_ae hbound
    _ = ENNReal.ofReal ((n : ℝ) ^ p) *
        (∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d)) := by
      exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hHm.pow_const p))
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ p) * ENNReal.ofReal (C₀ * (1 + R) ^ A) := by
      gcongr
    _ = ENNReal.ofReal C := by
      rw [show C = (n : ℝ) ^ p * (C₀ * (1 + R) ^ A) from rfl,
        ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

/-- The inverse annular crossing moment bounds the inverse distance of a fixed pair. -/
theorem continuum_point_invMoment {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (x y : Rd d) (hxy : x ≠ y) {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        (∫⁻ g, (ENNReal.ofReal ((rho D g).1 (x, y)))⁻¹ ^ q
          ∂(normLGFLaw d)) ≤ ENNReal.ofReal C := by
  let t : ℝ := ‖y - x‖
  have ht : 0 < t := by
    dsimp [t]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have ha : 0 < t / 4 := by positivity
  have hac : t / 4 < t / 2 := by linarith
  obtain ⟨C, hC⟩ := continuum_invCross hd hκ hC1 hC2 hb hμ hμ1
    x ha hac hq
  refine ⟨C, fun ξ hξ D hD => ?_⟩
  letI := l9b_normLGFLaw_prob (show 2 ≤ d by omega)
  have hlgf := l9b_normLGFLaw_normalized (show 2 ≤ d by omega)
  have hlen : ∀ᵐ g ∂(normLGFLaw d), (rho D g).IsLength := by
    filter_upwards [hD.length (normLGFLaw d) id hlgf.1.isLGFPlusCont] with g hg
    exact ContMetric.isLength_smul (Real.exp_pos _) hg
  have hle : ∀ᵐ g ∂(normLGFLaw d),
      (ENNReal.ofReal ((rho D g).1 (x, y)))⁻¹ ^ q ≤
        (acrossDist (rho D g) x (t / 4) (t / 2))⁻¹ ^ q := by
    filter_upwards [hlen] with g hg
    have hcross : acrossDist (rho D g) x (t / 4) (t / 2) ≤
        ENNReal.ofReal ((rho D g).1 (x, y)) := by
      have hx : ‖x - x‖ < (t / 2) / 2 := by simp; linarith
      have hy : t / 2 ≤ ‖y - x‖ := by dsimp [t]; linarith
      have h := l9b_acrossDist_le_internal (rho D g) univ hx hy
      rw [(rho D g).internal_univ_of_isLength hg] at h
      have hr : (t / 2) / 2 = t / 4 := by ring
      simpa only [hr] using h
    exact ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr hcross) hq.le
  exact (lintegral_mono_ae hle).trans (hC ξ hξ D hD)

end HigherDimLQGContinuity
