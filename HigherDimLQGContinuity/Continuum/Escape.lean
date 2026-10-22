import HigherDimLQGContinuity.Continuum.EscapeDet

/-! Quantitative continuum annular barriers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The large-radius Gaussian cost is polynomial in the radius. -/
theorem l2_gauss_large {d : ℕ} {b q r ξ : ℝ}
    (hb : 0 < b) (hξ : 0 ≤ ξ) (hξb : ξ ≤ b)
    (hr : 1 ≤ r) (K : ℝ)
    (hv : Var[fun g : DistRd d => sphereAvg g r 0; normLGFLaw d] ≤ Real.log r + K) :
    (ENNReal.ofReal
      (Real.exp (Var[fun g : DistRd d => sphereAvg g r 0; normLGFLaw d] *
        (-2 * q * ξ) ^ 2 / 2))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.exp (q ^ 2 * b ^ 2 * max 0 K) * r ^ (q ^ 2 * b ^ 2)) := by
  have hvar : 0 ≤ Var[fun g : DistRd d => sphereAvg g r 0; normLGFLaw d] :=
    variance_nonneg _ _
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg _
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg _
  have hξ2 : ξ ^ 2 ≤ b ^ 2 := by nlinarith
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hr
  have hK : K ≤ max 0 K := le_max_right _ _
  have hmain :
      (Var[fun g : DistRd d => sphereAvg g r 0; normLGFLaw d] *
        (-2 * q * ξ) ^ 2 / 2) * (1 / 2 : ℝ) ≤
        q ^ 2 * b ^ 2 * (Real.log r + max 0 K) := by
    have hvar' : Var[fun g : DistRd d => sphereAvg g r 0; normLGFLaw d] ≤
        Real.log r + max 0 K := by linarith
    have hsum : 0 ≤ Real.log r + max 0 K := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hvar')
      (mul_nonneg hq2 (sq_nonneg ξ)), mul_nonneg (sub_nonneg.mpr hξ2)
      (mul_nonneg hq2 hsum)]
  have hreal : Real.exp ((Var[fun g : DistRd d => sphereAvg g r 0; normLGFLaw d] *
      (-2 * q * ξ) ^ 2 / 2) * (1 / 2 : ℝ)) ≤
      Real.exp (q ^ 2 * b ^ 2 * max 0 K) * r ^ (q ^ 2 * b ^ 2) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < r), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hmain]
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  rw [← Real.exp_mul]
  exact ENNReal.ofReal_le_ofReal hreal

/-- A far annular crossing has a uniform decaying inverse moment. -/
theorem continuum_largeCross_moment {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ q : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hq : 0 < q) (hqb : q ^ 2 * b ^ 2 ≤ q * μ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ r : ℝ, 1 ≤ r →
          (∫⁻ g, (acrossDist (rho D g) 0 r (2 * r))⁻¹ ^ q
            ∂(normLGFLaw d)) ≤ ENNReal.ofReal (C * r ^ (-(q * μ / 2))) := by
  obtain ⟨C₀, hC₀⟩ := continuum_scaled_invCross hd hκ hC1 hC2 hb hμ hμ1 hq
  obtain ⟨K₀, hK₀⟩ := exists_variance_sphereAvg_pinLaw_le (show 2 ≤ d by omega)
  let B : ℝ := max 1 C₀
  let C : ℝ := Real.exp (q ^ 2 * b ^ 2 * max 0 K₀) * B ^ (1 / 2 : ℝ)
  have hB : 1 ≤ B := le_max_left _ _
  have hC₀B : C₀ ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun ξ hξ D hD r hr => ?_⟩
  have hrpos : 0 < r := by linarith
  have hξpos : 0 < ξ := hξ.base.xi_pos
  have hφ : μ ≤ ξ * distExp d ξ := by
    have hsqrt : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
    nlinarith [hξ.gap, mul_nonneg hξpos.le hsqrt]
  have hvar : Var[fun g : DistRd d => sphereAvg g r 0; normLGFLaw d] ≤
      Real.log r + K₀ := by
    have hh := (hK₀ one_pos hrpos (0 : Rd d)).2 hr
    rw [pinLaw_one (show 2 ≤ d by omega)] at hh
    simpa only [div_one, norm_zero, zero_div, Real.log_zero, max_self,
      mul_zero, add_zero] using hh
  have hgauss := l2_gauss_large (q := q) hb hξpos.le hξ.le_b hr K₀ hvar
  have hpow : ((r ^ (ξ * distExp d ξ))⁻¹) ^ q * r ^ (q ^ 2 * b ^ 2) ≤
      r ^ (-(q * μ / 2)) := by
    have he : -q * (ξ * distExp d ξ) + q ^ 2 * b ^ 2 ≤ -(q * μ / 2) := by
      nlinarith [hqb, mul_nonneg hq.le (sub_nonneg.mpr hφ)]
    calc
      ((r ^ (ξ * distExp d ξ))⁻¹) ^ q * r ^ (q ^ 2 * b ^ 2) =
          r ^ (-q * (ξ * distExp d ξ) + q ^ 2 * b ^ 2) := by
        rw [← Real.rpow_neg hrpos.le (ξ * distExp d ξ),
          ← Real.rpow_mul hrpos.le, ← Real.rpow_add hrpos]
        congr 1
        ring
      _ ≤ r ^ (-(q * μ / 2)) := Real.rpow_le_rpow_of_exponent_le hr he
  have hCpow : (ENNReal.ofReal C₀) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := by
    calc
      (ENNReal.ofReal C₀) ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal B) ^ (1 / 2 : ℝ) := by gcongr
      _ = ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have hmain := hC₀ ξ hξ D hD 0 r hrpos
  calc
    (∫⁻ g, (acrossDist (rho D g) 0 r (2 * r))⁻¹ ^ q ∂(normLGFLaw d)) ≤
        (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q *
          (ENNReal.ofReal
            (Real.exp (Var[fun g : DistRd d => sphereAvg g r 0; normLGFLaw d] *
              (-2 * q * ξ) ^ 2 / 2))) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal C₀) ^ (1 / 2 : ℝ) := hmain
    _ ≤ (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q *
        ENNReal.ofReal (Real.exp (q ^ 2 * b ^ 2 * max 0 K₀) * r ^ (q ^ 2 * b ^ 2)) *
        ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := by gcongr
    _ = ENNReal.ofReal
        (((r ^ (ξ * distExp d ξ))⁻¹) ^ q * r ^ (q ^ 2 * b ^ 2) * C) := by
      rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hrpos _),
        ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hrpos.le _)) hq.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hrpos.le _)) _),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr
          (Real.rpow_nonneg hrpos.le _)) _) (by positivity : 0 ≤
            Real.exp (q ^ 2 * b ^ 2 * max 0 K₀) * r ^ (q ^ 2 * b ^ 2)))]
      congr 1
      dsimp [C]
      ring
    _ ≤ ENNReal.ofReal (C * r ^ (-(q * μ / 2))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        ((r ^ (ξ * distExp d ξ))⁻¹) ^ q * r ^ (q ^ 2 * b ^ 2) * C ≤
            r ^ (-(q * μ / 2)) * C := mul_le_mul_of_nonneg_right hpow hC
        _ = C * r ^ (-(q * μ / 2)) := mul_comm _ _

/-- A path crossing from radius two to radius `S` also crosses the outer half annulus. -/
theorem l2_unit_barrier {d : ℕ} (D : ContMetric d) (hD : D.IsLength)
    {S : ℝ} (hS : 4 < S) :
    acrossDist D 0 (S / 2) S ≤ acrossDist D 0 2 S := by
  have hA : ∀ x ∈ sphere (0 : Rd d) 2, ‖x - 0‖ < S / 2 := by
    intro x hx
    have hxnorm : ‖x‖ = 2 := by simpa only [mem_sphere, dist_zero_right] using hx
    rw [sub_zero, hxnorm]
    linarith
  have hB : ∀ y ∈ sphere (0 : Rd d) S, S ≤ ‖y - 0‖ := by
    intro y hy
    have hynorm : ‖y‖ = S := by simpa only [mem_sphere, dist_zero_right] using hy
    rw [sub_zero, hynorm]
  have h := l9b_acrossDist_le_setDistIn D univ hA hB
  have heq : setDistIn D univ (sphere 0 2) (sphere 0 S) = acrossDist D 0 2 S := by
    unfold setDistIn acrossDist
    simp_rw [D.internal_univ_of_isLength hD]
  rw [heq] at h
  simpa only [show S / 2 = S / 2 from rfl] using h

/-- Markov's inequality in the inverse-crossing form, retaining outer measures. -/
theorem l2_cross_small_markov {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (z : Rd d) (a c : ℝ) {q M t : ℝ}
    (hq : 0 < q) (hM : 0 ≤ M) (ht : 0 < t)
    (hmom : ∫⁻ g, (acrossDist (rho D g) z a c)⁻¹ ^ q ∂(normLGFLaw d) ≤
      ENNReal.ofReal M) :
    (normLGFLaw d) {g | acrossDist (rho D g) z a c ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (M * t ^ q) := by
  let ε : ℝ≥0∞ := (ENNReal.ofReal t)⁻¹ ^ q
  have hε0 : ε ≠ 0 := by
    dsimp [ε]
    exact (ENNReal.rpow_pos_of_nonneg
      (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) hq.le).ne'
  have hεtop : ε ≠ ⊤ := by
    dsimp [ε]
    exact ENNReal.rpow_ne_top_of_nonneg hq.le (ENNReal.inv_ne_top.mpr
      (ENNReal.ofReal_pos.mpr ht).ne')
  have hmark := meas_ge_le_lintegral_div (μ := normLGFLaw d)
    (l2_measurable_invCrossPow hD z a c q).aemeasurable hε0 hεtop
  calc
    (normLGFLaw d) {g | acrossDist (rho D g) z a c ≤ ENNReal.ofReal t} ≤
        (normLGFLaw d) {g | ε ≤ (acrossDist (rho D g) z a c)⁻¹ ^ q} := by
      apply measure_mono
      intro g hg
      exact ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr hg) hq.le
    _ ≤ (∫⁻ g, (acrossDist (rho D g) z a c)⁻¹ ^ q ∂(normLGFLaw d)) / ε := hmark
    _ ≤ ENNReal.ofReal M / ε := by gcongr
    _ = ENNReal.ofReal (M * t ^ q) := by
      rw [div_eq_mul_inv]
      dsimp [ε]
      rw [← ENNReal.inv_rpow, inv_inv,
        ENNReal.ofReal_rpow_of_nonneg ht.le hq.le,
        ← ENNReal.ofReal_mul hM]

/-- The unit buffered diameter obeys the usual positive-moment tail bound. -/
theorem l2_diam_large_markov {d : ℕ} (hd : 2 ≤ d)
    {ξ : ℝ} {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {p M t : ℝ} (hp : 0 < p) (ht : 0 < t)
    (hmom : ∫⁻ g, (internalDiamRd (rho D g)
      (closedBall (0 : Rd d) 1) (ball 0 2)) ^ p ∂(normLGFLaw d) ≤
        ENNReal.ofReal M) :
    (normLGFLaw d) {g | ENNReal.ofReal t < internalDiamRd (rho D g)
      (closedBall (0 : Rd d) 1) (ball 0 2)} ≤ ENNReal.ofReal (M / t ^ p) := by
  letI := l9b_normLGFLaw_prob hd
  have hl : ∀ᵐ g ∂(normLGFLaw d), (rho D g).IsLength := by
    have hlgf := (l9b_normLGFLaw_normalized hd).1.isLGFPlusCont
    filter_upwards [hD.length (normLGFLaw d) id hlgf] with g hg
    exact ContMetric.isLength_smul (Real.exp_pos _) hg
  have hV : AEMeasurable (fun g => internalDiamRd (rho D g)
      (closedBall (0 : Rd d) 1) (ball 0 2)) (normLGFLaw d) := by
    exact aemeasurable_diamIn_of_ae_length (normLGFLaw d) (rho D)
      (measurable_rho hD.measurable) hl isOpen_ball (by
        intro x hx
        have hnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
        rw [mem_ball, dist_zero_right]
        linarith)
  have hmk := meas_ge_le_lintegral_div (μ := normLGFLaw d)
    (hV.pow_const p) (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ht p)).ne'
    ENNReal.ofReal_ne_top
  calc
    (normLGFLaw d) {g | ENNReal.ofReal t < internalDiamRd (rho D g)
      (closedBall (0 : Rd d) 1) (ball 0 2)} ≤
        (normLGFLaw d) {g | ENNReal.ofReal (t ^ p) ≤
          (internalDiamRd (rho D g)
            (closedBall (0 : Rd d) 1) (ball 0 2)) ^ p} := by
      apply measure_mono
      intro g hg
      rw [← ENNReal.ofReal_rpow_of_nonneg ht.le hp.le]
      exact ENNReal.rpow_le_rpow hg.le hp.le
    _ ≤ (∫⁻ g, (internalDiamRd (rho D g)
      (closedBall (0 : Rd d) 1) (ball 0 2)) ^ p ∂(normLGFLaw d)) /
        ENNReal.ofReal (t ^ p) := hmk
    _ ≤ ENNReal.ofReal M / ENNReal.ofReal (t ^ p) := by gcongr
    _ = ENNReal.ofReal (M / t ^ p) := by
      rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ht p)]

/-- Unit-scale relative escape at large outer radius. -/
theorem continuum_unit_escape_large {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p q : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d))
    (hq : 0 < q) (hqb : q ^ 2 * b ^ 2 ≤ q * μ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ (K S : ℝ), 1 ≤ K → 8 ≤ S →
          (normLGFLaw d) {g | acrossDist (rho D g) 0 2 S ≤
            ENNReal.ofReal K * internalDiamRd (rho D g)
              (closedBall (0 : Rd d) 1) (ball 0 2)} ≤
            ENNReal.ofReal (C * (K ^ q + 1) * S ^ (-(μ / 4 * min q p))) := by
  obtain ⟨Cz, hCz0, hCz⟩ := continuum_largeCross_moment hd hκ hC1 hC2 hb hμ hμ1 hq hqb
  obtain ⟨Cv, hCv⟩ := continuum_unitDiam hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
  let Cv' : ℝ := max 1 Cv
  have hCv' : Cv ≤ Cv' := le_max_right _ _
  have hCv'0 : 0 ≤ Cv' := (zero_le_one.trans (le_max_left _ _))
  let pesc : ℝ := μ / 4 * min q p
  have hpesc : 0 < pesc := by dsimp [pesc]; positivity
  let C : ℝ := 2 ^ (q * μ / 2) * Cz + Cv'
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun ξ hξ D hD K S hK hS => ?_⟩
  have hS0 : 0 < S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have hK0 : 0 < K := by linarith
  let Z : DistRd d → ℝ≥0∞ := fun g => acrossDist (rho D g) 0 (S / 2) S
  let V : DistRd d → ℝ≥0∞ := fun g => internalDiamRd (rho D g)
    (closedBall (0 : Rd d) 1) (ball 0 2)
  let t : ℝ := S ^ (μ / 4)
  have ht : 0 < t := by dsimp [t]; positivity
  have hlen : ∀ᵐ g ∂(normLGFLaw d), (rho D g).IsLength := by
    letI := l9b_normLGFLaw_prob (show 2 ≤ d by omega)
    filter_upwards [hD.length (normLGFLaw d) id
      (l9b_normLGFLaw_normalized (show 2 ≤ d by omega)).1.isLGFPlusCont] with g hg
    exact ContMetric.isLength_smul (Real.exp_pos _) hg
  have hbar : ∀ᵐ g ∂(normLGFLaw d), Z g ≤ acrossDist (rho D g) 0 2 S := by
    filter_upwards [hlen] with g hg
    exact l2_unit_barrier (rho D g) hg (by linarith : 4 < S)
  have hsub : {g | acrossDist (rho D g) 0 2 S ≤ ENNReal.ofReal K * V g} ≤ᵐ[normLGFLaw d]
      {g | Z g ≤ ENNReal.ofReal (K * t)} ∪ {g | ENNReal.ofReal t < V g} := by
    filter_upwards [hbar] with g hg hE
    by_cases hV : ENNReal.ofReal t < V g
    · exact Or.inr hV
    · apply Or.inl
      calc
        Z g ≤ acrossDist (rho D g) 0 2 S := hg
        _ ≤ ENNReal.ofReal K * V g := hE
        _ ≤ ENNReal.ofReal K * ENNReal.ofReal t := by
          gcongr
          exact le_of_not_gt hV
        _ = ENNReal.ofReal (K * t) := (ENNReal.ofReal_mul hK0.le).symm
  have hZmom : ∫⁻ g, (Z g)⁻¹ ^ q ∂(normLGFLaw d) ≤
      ENNReal.ofReal (Cz * (S / 2) ^ (-(q * μ / 2))) := by
    have hh := hCz ξ hξ D hD (S / 2) (by linarith : 1 ≤ S / 2)
    simpa only [show (2 : ℝ) * (S / 2) = S by ring, Z] using hh
  have hZtail : (normLGFLaw d) {g | Z g ≤ ENNReal.ofReal (K * t)} ≤
      ENNReal.ofReal (Cz * (S / 2) ^ (-(q * μ / 2)) * (K * t) ^ q) :=
    l2_cross_small_markov hD.measurable 0 (S / 2) S hq
      (mul_nonneg hCz0 (Real.rpow_nonneg (by linarith : 0 ≤ S / 2) _))
      (mul_pos hK0 ht) hZmom
  have hVtail : (normLGFLaw d) {g | ENNReal.ofReal t < V g} ≤
      ENNReal.ofReal (Cv' / t ^ p) := by
    apply l2_diam_large_markov (show 2 ≤ d by omega) hD hp ht
    exact (hCv ξ hξ D hD).trans (ENNReal.ofReal_le_ofReal hCv')
  have hfirst : Cz * (S / 2) ^ (-(q * μ / 2)) * (K * t) ^ q ≤
      (2 ^ (q * μ / 2) * Cz) * K ^ q * S ^ (-pesc) := by
    have hpow : (S / 2) ^ (-(q * μ / 2)) * t ^ q =
        2 ^ (q * μ / 2) * S ^ (-(q * μ / 4)) := by
      dsimp [t]
      have htq : (S ^ (μ / 4)) ^ q = S ^ ((μ / 4) * q) :=
        (Real.rpow_mul hS0.le (μ / 4) q).symm
      rw [Real.div_rpow hS0.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        htq, div_eq_mul_inv, inv_inv]
      calc
        S ^ (-(q * μ / 2)) * 2 ^ (q * μ / 2) * S ^ ((μ / 4) * q) =
            2 ^ (q * μ / 2) * S ^ (-(q * μ / 2) + (μ / 4) * q) := by
          rw [Real.rpow_add hS0]
          ring
        _ = 2 ^ (q * μ / 2) * S ^ (-(q * μ / 4)) := by
          congr 1
          ring_nf
    rw [Real.mul_rpow hK0.le ht.le]
    have he : -(q * μ / 4) ≤ -pesc := by
      dsimp [pesc]
      nlinarith [min_le_left q p, mul_nonneg (div_nonneg hμ.le (by norm_num : (0 : ℝ) ≤ 4))
        (sub_nonneg.mpr (min_le_left q p))]
    have hpowers := Real.rpow_le_rpow_of_exponent_le hS1 he
    calc
      Cz * (S / 2) ^ (-(q * μ / 2)) * (K ^ q * t ^ q) =
          (2 ^ (q * μ / 2) * Cz) * K ^ q * S ^ (-(q * μ / 4)) := by
        calc
          _ = Cz * K ^ q * ((S / 2) ^ (-(q * μ / 2)) * t ^ q) := by ring
          _ = _ := by rw [hpow]; ring
      _ ≤ (2 ^ (q * μ / 2) * Cz) * K ^ q * S ^ (-pesc) := by
        gcongr
  have hsecond : Cv' / t ^ p ≤ Cv' * S ^ (-pesc) := by
    have hbase : Cv' / t ^ p = Cv' * S ^ (-(p * μ / 4)) := by
      dsimp [t]
      have htp : (S ^ (μ / 4)) ^ p = S ^ ((μ / 4) * p) :=
        (Real.rpow_mul hS0.le (μ / 4) p).symm
      rw [htp, div_eq_mul_inv, ← Real.rpow_neg hS0.le]
      congr 1
      ring_nf
    rw [hbase]
    gcongr
    dsimp [pesc]
    nlinarith [min_le_right q p, mul_nonneg (div_nonneg hμ.le (by norm_num : (0 : ℝ) ≤ 4))
      (sub_nonneg.mpr (min_le_right q p))]
  calc
    (normLGFLaw d) {g | acrossDist (rho D g) 0 2 S ≤ ENNReal.ofReal K * V g} ≤
        (normLGFLaw d) ({g | Z g ≤ ENNReal.ofReal (K * t)} ∪
          {g | ENNReal.ofReal t < V g}) := measure_mono_ae hsub
    _ ≤ (normLGFLaw d) {g | Z g ≤ ENNReal.ofReal (K * t)} +
        (normLGFLaw d) {g | ENNReal.ofReal t < V g} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Cz * (S / 2) ^ (-(q * μ / 2)) * (K * t) ^ q) +
        ENNReal.ofReal (Cv' / t ^ p) := add_le_add hZtail hVtail
    _ ≤ ENNReal.ofReal ((2 ^ (q * μ / 2) * Cz) * K ^ q * S ^ (-pesc)) +
        ENNReal.ofReal (Cv' * S ^ (-pesc)) := by gcongr
    _ ≤ ENNReal.ofReal (C * (K ^ q + 1) * S ^ (-pesc)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hKq : 0 ≤ K ^ q := Real.rpow_nonneg hK0.le _
      have hSp : 0 ≤ S ^ (-pesc) := Real.rpow_nonneg hS0.le _
      have hA : 0 ≤ 2 ^ (q * μ / 2) * Cz := by positivity
      dsimp [C]
      nlinarith [mul_nonneg hA hSp,
        mul_nonneg (mul_nonneg hCv'0 hKq) hSp]

/-- The unit-radius relative escape estimate, including the bounded outer-radius range. -/
theorem continuum_unit_escape {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p q : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d))
    (hq : 0 < q) (hqb : q ^ 2 * b ^ 2 ≤ q * μ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ (K S : ℝ), 1 ≤ K → 4 ≤ S →
          (normLGFLaw d) {g | acrossDist (rho D g) 0 2 S ≤
            ENNReal.ofReal K * internalDiamRd (rho D g)
              (closedBall (0 : Rd d) 1) (ball 0 2)} ≤
            ENNReal.ofReal (C * (K ^ q + 1) * S ^ (-(μ / 4 * min q p))) := by
  obtain ⟨C₀, hC₀0, hlarge⟩ := continuum_unit_escape_large hd hκ hC1 hC2
    hb hμ hμ1 hσ hσμ hp hpb hq hqb
  let pesc : ℝ := μ / 4 * min q p
  have hpesc : 0 < pesc := by dsimp [pesc]; positivity
  let C : ℝ := max 1 C₀ * 8 ^ pesc
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, fun ξ hξ D hD K S hK hS => ?_⟩
  have hK0 : 0 < K := by linarith
  have hS0 : 0 < S := by linarith
  by_cases hS8 : 8 ≤ S
  · have hh := hlarge ξ hξ D hD K S hK hS8
    refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : 0 ≤ (K ^ q + 1) * S ^ (-pesc) := by positivity
    have hC₀C : C₀ ≤ C := by
      dsimp [C]
      have hp8 : 1 ≤ (8 : ℝ) ^ pesc := Real.one_le_rpow (by norm_num) hpesc.le
      nlinarith [le_max_right (1 : ℝ) C₀]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₀C) hpow]
  · haveI := l9b_normLGFLaw_prob (show 2 ≤ d by omega)
    have hmeasure : (normLGFLaw d) {g | acrossDist (rho D g) 0 2 S ≤
          ENNReal.ofReal K * internalDiamRd (rho D g)
            (closedBall (0 : Rd d) 1) (ball 0 2)} ≤ 1 := by
      calc
        (normLGFLaw d) _ ≤ (normLGFLaw d) Set.univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    refine hmeasure.trans ?_
    have hSle : S ≤ 8 := le_of_lt (lt_of_not_ge hS8)
    have hSpow : (8 : ℝ) ^ (-pesc) ≤ S ^ (-pesc) :=
      Real.rpow_le_rpow_of_nonpos hS0 hSle (by linarith)
    have hmul : 1 ≤ C * (K ^ q + 1) * S ^ (-pesc) := by
      have hC1 : (8 : ℝ) ^ pesc ≤ C := by
        dsimp [C]
        have hm : 1 ≤ max (1 : ℝ) C₀ := le_max_left _ _
        nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 8) pesc]
      have hKq : 1 ≤ K ^ q + 1 := by
        have hh : 0 ≤ K ^ q := Real.rpow_nonneg hK0.le _
        linarith
      have h8pos : 0 < (8 : ℝ) ^ pesc := Real.rpow_pos_of_pos (by norm_num) _
      have hSp0 : 0 ≤ S ^ (-pesc) := Real.rpow_nonneg hS0.le _
      have hEq : (8 : ℝ) ^ pesc * (8 : ℝ) ^ (-pesc) = 1 := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
        exact mul_inv_cancel₀ h8pos.ne'
      calc
        1 = (8 : ℝ) ^ pesc * 8 ^ (-pesc) := hEq.symm
        _ ≤ C * S ^ (-pesc) := by gcongr
        _ ≤ C * (K ^ q + 1) * S ^ (-pesc) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hKq hC0) hSp0
    exact ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hmul

/-- Scaling sends the escape comparison at radius `R` to the unit-radius comparison. -/
theorem l2_escape_scale_event {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {R : ℝ} (hR : 0 < R) (K S : ℝ) :
    ∀ᵐ g ∂(normLGFLaw d),
      acrossDist (rho D g) 0 (2 * R) (S * R) ≤
        ENNReal.ofReal K * internalDiamRd (rho D g)
          (closedBall (0 : Rd d) R) (ball 0 (2 * R)) →
      acrossDist (rho D (recentre 1 R 0 g)) 0 2 S ≤
        ENNReal.ofReal K * internalDiamRd (rho D (recentre 1 R 0 g))
          (closedBall (0 : Rd d) 1) (ball 0 2) := by
  have hcross := l2_across_scaling hd hξ hD hR 0 2 S
  have hsets := rho_scaling_sets hd hξ hD (s := 1) one_pos hR (0 : Rd d)
  rw [pinLaw_one hd] at hsets
  filter_upwards [hcross, hsets] with g hc hs hE
  let c : ℝ≥0∞ := ENNReal.ofReal (scaleS d ξ 1 R 0 g)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (scaleS_pos d ξ 1 hR 0 g)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA : acrossDist (rho D g) 0 (2 * R) (S * R) =
      c * acrossDist (rho D (recentre 1 R 0 g)) 0 2 S := by
    simpa only [smul_zero, zero_add, mul_comm R 2, mul_comm R S, c] using hc
  have hV : internalDiamRd (rho D g)
      (closedBall (0 : Rd d) R) (ball 0 (2 * R)) =
      c * internalDiamRd (rho D (recentre 1 R 0 g))
        (closedBall (0 : Rd d) 1) (ball 0 2) := by
    have hh := hs.2 (ball (0 : Rd d) 2) (closedBall 0 1)
    rw [p2_image_affine_ball hR 0 0 2,
      p2_image_affine_closedBall hR 0 0 1] at hh
    simpa only [smul_zero, zero_add, mul_one, mul_comm R 2,
      internalDiamRd, diamIn, c] using hh
  rw [hA, hV] at hE
  have heq : c * acrossDist (rho D (recentre 1 R 0 g)) 0 2 S ≤
      c * (ENNReal.ofReal K * internalDiamRd (rho D (recentre 1 R 0 g))
        (closedBall (0 : Rd d) 1) (ball 0 2)) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hE
  exact (ENNReal.mul_le_mul_iff_right hc0 hctop).mp heq

/-- Uniform relative escape for the mean-log normalized strong metric at every base radius. -/
theorem continuum_escape_rho {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p q : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d))
    (hq : 0 < q) (hqb : q ^ 2 * b ^ 2 ≤ q * μ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ (K R S : ℝ), 1 ≤ K → 1 ≤ R → 4 ≤ S →
          (normLGFLaw d) {g | acrossDist (rho D g) 0 (2 * R) (S * R) ≤
            ENNReal.ofReal K * internalDiamRd (rho D g)
              (closedBall (0 : Rd d) R) (ball 0 (2 * R))} ≤
            ENNReal.ofReal (C * (K ^ q + 1) * S ^ (-(μ / 4 * min q p))) := by
  obtain ⟨C, hC0, hunit⟩ := continuum_unit_escape hd hκ hC1 hC2
    hb hμ hμ1 hσ hσμ hp hpb hq hqb
  refine ⟨C, hC0, fun ξ hξ D hD K R S hK hR hS => ?_⟩
  let E : Set (DistRd d) := {g | acrossDist (rho D g) 0 2 S ≤
    ENNReal.ofReal K * internalDiamRd (rho D g)
      (closedBall (0 : Rd d) 1) (ball 0 2)}
  have hscale := l2_escape_scale_event (show 2 ≤ d by omega) hξ.base.xi_pos hD
    (by linarith : 0 < R) K S
  have hle : (normLGFLaw d) {g | acrossDist (rho D g) 0 (2 * R) (S * R) ≤
      ENNReal.ofReal K * internalDiamRd (rho D g)
        (closedBall (0 : Rd d) R) (ball 0 (2 * R))} ≤
      (normLGFLaw d) {g | recentre 1 R 0 g ∈ E} := by
    exact measure_mono_ae hscale
  have hlaw := pinLaw_preimage_recentre_le (show 2 ≤ d by omega)
    (s := 1) (s₀ := 1) one_pos one_pos (by linarith : 0 < R)
    (0 : Rd d) E
  rw [pinLaw_one (show 2 ≤ d by omega)] at hlaw
  exact hle.trans (hlaw.trans (hunit ξ hξ D hD K S hK hS))

theorem l2_internalDiam_smul {d : ℕ} (D : ContMetric d) {c : ℝ} (hc : 0 < c)
    (K U : Set (Rd d)) :
    internalDiamRd (D.smul c hc) K U =
      ENNReal.ofReal c * internalDiamRd D K U := by
  unfold internalDiamRd
  simp_rw [ContMetric.internal_smul hc]
  simp only [ENNReal.mul_iSup]

/-- Relative escape is unchanged by mean-log normalization. -/
theorem continuum_escape {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p q : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d))
    (hq : 0 < q) (hqb : q ^ 2 * b ^ 2 ≤ q * μ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ (K R S : ℝ), 1 ≤ K → 1 ≤ R → 4 ≤ S →
          (normLGFLaw d) {g | acrossDist (D g) 0 (2 * R) (S * R) ≤
            ENNReal.ofReal K * internalDiamRd (D g)
              (closedBall (0 : Rd d) R) (ball 0 (2 * R))} ≤
            ENNReal.ofReal (C * (K ^ q + 1) * S ^ (-(μ / 4 * min q p))) := by
  obtain ⟨C, hC0, hrho⟩ := continuum_escape_rho hd hκ hC1 hC2
    hb hμ hμ1 hσ hσμ hp hpb hq hqb
  refine ⟨C, hC0, fun ξ hξ D hD K R S hK hR hS => ?_⟩
  have hsubset : {g | acrossDist (D g) 0 (2 * R) (S * R) ≤
      ENNReal.ofReal K * internalDiamRd (D g)
        (closedBall (0 : Rd d) R) (ball 0 (2 * R))} ⊆
      {g | acrossDist (rho D g) 0 (2 * R) (S * R) ≤
        ENNReal.ofReal K * internalDiamRd (rho D g)
          (closedBall (0 : Rd d) R) (ball 0 (2 * R))} := by
    intro g hg
    have hcross : acrossDist (rho D g) 0 (2 * R) (S * R) =
        ENNReal.ofReal (Real.exp (-logMean D)) *
          acrossDist (D g) 0 (2 * R) (S * R) := by
      exact acrossDist_smul (Real.exp_pos _) (D g) 0 (2 * R) (S * R)
    have hdiam : internalDiamRd (rho D g)
        (closedBall (0 : Rd d) R) (ball 0 (2 * R)) =
        ENNReal.ofReal (Real.exp (-logMean D)) * internalDiamRd (D g)
          (closedBall (0 : Rd d) R) (ball 0 (2 * R)) := by
      exact l2_internalDiam_smul (D g) (Real.exp_pos _) _ _
    change acrossDist (rho D g) 0 (2 * R) (S * R) ≤
      ENNReal.ofReal K * internalDiamRd (rho D g)
        (closedBall (0 : Rd d) R) (ball 0 (2 * R))
    change acrossDist (D g) 0 (2 * R) (S * R) ≤
      ENNReal.ofReal K * internalDiamRd (D g)
        (closedBall (0 : Rd d) R) (ball 0 (2 * R)) at hg
    rw [hcross, hdiam]
    calc
      ENNReal.ofReal (Real.exp (-logMean D)) * acrossDist (D g) 0 (2 * R) (S * R) ≤
          ENNReal.ofReal (Real.exp (-logMean D)) *
            (ENNReal.ofReal K * internalDiamRd (D g)
              (closedBall (0 : Rd d) R) (ball 0 (2 * R))) := by gcongr
      _ = ENNReal.ofReal K *
          (ENNReal.ofReal (Real.exp (-logMean D)) * internalDiamRd (D g)
            (closedBall (0 : Rd d) R) (ball 0 (2 * R))) := by ac_rfl
  exact (measure_mono hsubset).trans (hrho ξ hξ D hD K R S hK hR hS)

end HigherDimLQGContinuity
