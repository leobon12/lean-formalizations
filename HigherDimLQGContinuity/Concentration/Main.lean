import HigherDimLQGContinuity.Concentration.Shift

/-!
# Concentration of the log unit distance (packet N4; blueprint Part C `c:prop-conc`)

NA4 A1 Step 4 (without [9]'s log-Sobolev bootstrap, ruling N7). For `ξ ∈ (0, ξ̄]` and `D` strong at `ξ`,
`‖log ρ(0, e₁)‖_{L^p(ℙ)} ≤ C₃ p ξ` for every `p ≥ 1` (`concentration_logRho`), with `C₃` depending only on `d`,
`ξ̄` and the frame. Hence `ConcentrationStmt d` (`concentration_of`, interface I20; consumer N5).

Proof (blueprint `c:prop-conc`). Transport to the frame: `G = log ρ_{T(·)}(0, e₁)` on `(ℝ^ℕ, stdP)` has the law of
`log ρ(0, e₁)` under `ℙ` (`T_* stdP = ℙ`), is in every `L^p` by (E4), and `E G = 0` by (U0). Hypothesis (H) holds
on a full measurable set with `L_j = ξ ‖e_j‖_∞` (`exists_good_shiftLipschitz`), so GaussianLQG's
`gaussian_Lp_inequality` gives `‖G‖_p ≤ c_p (∫ (∑_j (∂_j G)²)^{p/2})^{1/p}`. Almost surely
`∑_j (∂_j G)² ≤ ξ² C_b U(T ω)` (`tsum_coordDeriv_sq_le` with the majorant of `exists_geodMajorant`), and
`∫ U^{p/2} ≤ (p/(2c))^{p/2} M` (`n4_lintegral_rpow_le`); with `c_p ≤ 2π √p` (`n4_gaussLpConst_le`) this gives
`‖G‖_p ≤ 2π √(C_b/(2c)) max(M, 1) · p ξ` for `p ≥ 2`, and `‖·‖_p ≤ ‖·‖_2` covers `1 ≤ p < 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)
open GaussianLQG (Coord stdP shiftBy coordDeriv)

variable {d : ℕ}

/-! ## Gaussian absolute moments -/

/-- `∫ e^{t x} dN(0, 1) = e^{t²/2}`. -/
theorem n4_integral_exp_mul_gaussian (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂(gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf, id, zero_mul, NNReal.coe_one, one_mul, zero_add] at h
  exact h

/-- **Gaussian absolute moments**: `∫ |x|^p dN(0, 1) ≤ (4 √p)^p` for `p ≥ 1`. -/
theorem n4_integral_abs_rpow_gaussian_le {p : ℝ} (hp : 1 ≤ p) :
    ∫ x, |x| ^ p ∂(gaussianReal 0 1) ≤ (4 * Real.sqrt p) ^ p := by
  have hp0 : 0 < p := by linarith
  set t := Real.sqrt p with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hp0
  have hpt : p / t = t := by
    rw [ht, div_eq_iff ht0.ne', Real.mul_self_sqrt hp0.le]
  have htsq : t ^ 2 = p := Real.sq_sqrt hp0.le
  -- pointwise bound
  have hpt' : ∀ x : ℝ, |x| ^ p ≤ t ^ p * (Real.exp (t * x) + Real.exp ((-t) * x)) := by
    intro x
    have h1 := n4_rpow_le_mul_exp (abs_nonneg x) hp0 ht0
    rw [hpt] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos ((-t) * x)]
    · rw [abs_of_nonpos hx, show t * -x = (-t) * x by ring]
      linarith [Real.exp_pos (t * x)]
  have hint : Integrable (fun x : ℝ => t ^ p * (Real.exp (t * x) + Real.exp ((-t) * x)))
      (gaussianReal 0 1) :=
    ((integrable_exp_mul_gaussianReal t).add (integrable_exp_mul_gaussianReal (-t))).const_mul _
  have hval : ∫ x, t ^ p * (Real.exp (t * x) + Real.exp ((-t) * x)) ∂(gaussianReal 0 1) =
      t ^ p * (2 * Real.exp (p / 2)) := by
    rw [integral_const_mul, integral_add (integrable_exp_mul_gaussianReal t)
      (integrable_exp_mul_gaussianReal (-t)), n4_integral_exp_mul_gaussian,
      n4_integral_exp_mul_gaussian, neg_sq, htsq]
    ring
  have hexp : 2 * Real.exp (p / 2) ≤ (4 : ℝ) ^ p := by
    have he : Real.exp (1 / 2) ≤ 2 := by
      have h1 : Real.exp (1 / 2) ^ 2 ≤ 2 ^ 2 := by
        rw [← Real.exp_nat_mul]
        have := Real.exp_one_lt_d9
        norm_num at this ⊢
        linarith
      exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).1 h1
    have h2 : Real.exp (p / 2) ≤ (2 : ℝ) ^ p := by
      rw [show p / 2 = 1 / 2 * p by ring, Real.exp_mul]
      exact Real.rpow_le_rpow (Real.exp_pos _).le he hp0.le
    have h3 : (2 : ℝ) ≤ 2 ^ p := by
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ p := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp
    have h4 : (4 : ℝ) ^ p = 2 ^ p * 2 ^ p := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
    rw [h4]
    nlinarith [Real.exp_pos (p / 2)]
  calc ∫ x, |x| ^ p ∂(gaussianReal 0 1)
      ≤ ∫ x, t ^ p * (Real.exp (t * x) + Real.exp ((-t) * x)) ∂(gaussianReal 0 1) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hint (ae_of_all _ hpt')
    _ = t ^ p * (2 * Real.exp (p / 2)) := hval
    _ ≤ t ^ p * 4 ^ p := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (4 * t) ^ p := by rw [Real.mul_rpow (by norm_num) ht0.le, mul_comm]

/-- **The constant of the Gaussian `L^p` inequality**: `c_p = (π/2) ‖N‖_p ≤ 2π √p` for `p ≥ 1`. -/
theorem n4_gaussLpConst_le {p : ℝ} (hp : 1 ≤ p) :
    Real.pi / 2 * (∫ x, |x| ^ p ∂(gaussianReal 0 1)) ^ (1 / p) ≤ 2 * Real.pi * Real.sqrt p := by
  have hp0 : 0 < p := by linarith
  have hnn : 0 ≤ ∫ x, |x| ^ p ∂(gaussianReal 0 1) :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _
  have h1 : (∫ x, |x| ^ p ∂(gaussianReal 0 1)) ^ (1 / p) ≤ ((4 * Real.sqrt p) ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow hnn (n4_integral_abs_rpow_gaussian_le hp) (by positivity)
  rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne', ← one_div] at h1
  calc Real.pi / 2 * (∫ x, |x| ^ p ∂(gaussianReal 0 1)) ^ (1 / p)
      ≤ Real.pi / 2 * (4 * Real.sqrt p) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * Real.pi * Real.sqrt p := by ring

/-! ## Elementary bounds -/

/-- An `L^q` bound from a bound on `∫⁻ |f|^q`. -/
theorem n4_memLp_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {q K : ℝ} (hq : 0 < q)
    (h : ∫⁻ x, ENNReal.ofReal (|f x| ^ q) ∂μ ≤ ENNReal.ofReal K) : MemLp f (ENNReal.ofReal q) μ := by
  refine ⟨hf, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  have hpt : ∀ x, ‖f x‖ₑ ^ q = ENNReal.ofReal (|f x| ^ q) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le]
  simp_rw [hpt]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)

/-- The real computation behind the final constant:
`((ξ² C_b)^{p/2} ((p/2/c)^{p/2} M))^{1/p} ≤ ξ √(C_b/(2c)) √p max(M, 1)`. -/
theorem n4_rpow_one_div_le {ξ Cb c M p : ℝ} (hξ : 0 ≤ ξ) (hCb : 0 ≤ Cb) (hc : 0 < c) (hM : 0 ≤ M)
    (hp : 1 ≤ p) :
    ((ξ ^ 2 * Cb) ^ (p / 2) * ((p / 2 / c) ^ (p / 2) * M)) ^ (1 / p) ≤
      ξ * Real.sqrt (Cb / (2 * c)) * Real.sqrt p * max M 1 := by
  have hp0 : 0 < p := by linarith
  rw [← mul_assoc, ← Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hM, ← Real.rpow_mul (by positivity)]
  have he : p / 2 * (1 / p) = 1 / 2 := by field_simp
  rw [he, ← Real.sqrt_eq_rpow]
  have hX : Real.sqrt (ξ ^ 2 * Cb * (p / 2 / c)) = ξ * Real.sqrt (Cb / (2 * c)) * Real.sqrt p := by
    rw [show ξ ^ 2 * Cb * (p / 2 / c) = ξ ^ 2 * (Cb / (2 * c) * p) by field_simp,
      Real.sqrt_mul (sq_nonneg ξ), Real.sqrt_sq hξ, Real.sqrt_mul (by positivity)]
    ring
  rw [hX]
  have hM1 : M ^ (1 / p) ≤ max M 1 := by
    rcases le_total M 1 with h | h
    · exact (Real.rpow_le_one hM h (by positivity)).trans (le_max_right _ _)
    · calc M ^ (1 / p) ≤ M ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h ((div_le_one hp0).2 hp)
        _ = M := Real.rpow_one M
        _ ≤ max M 1 := le_max_left _ _
  exact mul_le_mul_of_nonneg_left hM1 (by positivity)

/-- The frame map pushes `stdP` to `normLGFLaw d`. -/
theorem measurePreserving_frameT (hd : 2 ≤ d) (F : PairingFrame d) :
    MeasurePreserving F.T stdP (normLGFLaw d) :=
  ⟨F.measurable_T, l9b_map_eq_normLGFLaw hd F.normalized⟩

/-! ## Concentration -/

/-- **Concentration for `p ≥ 2`** (blueprint `c:prop-conc`, the main case): `‖log ρ(0, e₁)‖_p ≤ C₃ p ξ` with
`C₃ = 2π √(C_b/(2c)) max(M, 1)`. -/
theorem concentration_logRho_of_two_le {d : ℕ} (hd : 3 ≤ d) {ξbar : ℝ}
    (hU : UniformEstimates d ξbar 1) (F : PairingFrame d) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → ∀ p : ℝ, 2 ≤ p →
        eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d))) (ENNReal.ofReal p) (normLGFLaw d) ≤
          ENNReal.ofReal (C₃ * p * ξ) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  obtain ⟨σ, c, M, hσ, hσ1, hc, hM, hmaj⟩ := exists_geodMajorant hd hU
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcore⟩ := lemma21_core hd hU
  have hCb : 0 ≤ F.Cb := zero_le_one.trans F.one_le_Cb
  refine ⟨2 * Real.pi * Real.sqrt (F.Cb / (2 * c)) * max M 1, by positivity,
    fun ξ hξ D hD p hp => ?_⟩
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hξ0 : 0 < ξ := hξ.1
  have : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hT := measurePreserving_frameT hd2 F
  obtain ⟨U, hUm, hU1, hUexp, hUspec⟩ := hmaj ξ hξ D hD
  obtain ⟨⟨hint, hint0⟩, _, _, hU3⟩ := hcore ξ hξ D hD
  set G := logRhoFrame F D with hGdef
  have hGm : Measurable G := measurable_logRhoFrame F hD.measurable
  have hFm : Measurable fun g => Real.log ((rho D g).1 (0, e₁ d)) :=
    measurable_log_rho_apply hD.measurable _
  have hGeq : G = (fun g => Real.log ((rho D g).1 (0, e₁ d))) ∘ F.T := rfl
  -- `G ∈ L^p` from (E4)
  obtain ⟨Kp, hKp⟩ := hU.logMoments 0 (e₁ d) (p2_zero_ne_e₁ hd1) p hp1
  have hmomμ := hKp ξ hξ D hD
  rw [pinLaw_one hd2] at hmomμ
  have hmemμ : MemLp (fun g => Real.log ((rho D g).1 (0, e₁ d))) (ENNReal.ofReal p)
      (normLGFLaw d) := n4_memLp_of_lintegral hFm.aestronglyMeasurable hp0 hmomμ
  have hmemG : MemLp G (ENNReal.ofReal p) stdP := by
    rw [hGeq]
    exact hmemμ.comp_measurePreserving hT
  -- `E G = 0` from (U0)
  have hEG : ∫ ω, G ω ∂stdP = 0 := by
    rw [hGeq, ← hint0, ← hT.map_eq]
    exact (integral_map hT.measurable.aemeasurable hFm.aestronglyMeasurable).symm
  -- hypothesis (H) and the Gaussian `L^p` inequality
  obtain ⟨𝒢, h𝒢m, h𝒢c, h𝒢good, h𝒢W, hH⟩ := exists_good_shiftLipschitz hd1 F hξ0.le hD
  have hLp := GaussianLQG.gaussian_Lp_inequality hGm h𝒢m h𝒢c
    (L := fun j => ξ * frameBound F j) hH hp1 hmemG
  rw [hEG] at hLp
  simp only [sub_zero] at hLp
  -- the square function
  have hsq : ∀ᵐ ω ∂stdP, ∑' j, ENNReal.ofReal (coordDeriv G j ω ^ 2) ≤
      ENNReal.ofReal (ξ ^ 2 * (F.Cb * U (F.T ω))) := by
    have h1 := hT.quasiMeasurePreserving.ae hUspec
    have h2 := hT.quasiMeasurePreserving.ae hU3
    have h3 : ∀ᵐ ω ∂stdP, ω ∈ 𝒢 := mem_ae_iff.2 h𝒢c
    filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
    obtain ⟨S, B, hS, hB, hUeq, hgeo⟩ := hω1
    obtain ⟨η, hη⟩ := hω2.2.2.2.1 0 (e₁ d)
    obtain ⟨hrange, hball⟩ := hgeo η hη
    rw [hUeq]
    exact tsum_coordDeriv_sq_le hd1 F hξ0.le (h𝒢good hω3) (h𝒢W ω hω3) hη hS hB hσ hσ1 hrange hball
  -- the moment of the square function
  set Y : ℝ := (ξ ^ 2 * F.Cb) ^ (p / 2) * ((p / 2 / c) ^ (p / 2) * M) with hYdef
  have hY0 : 0 ≤ Y := by positivity
  have hp2 : 0 < p / 2 := by linarith
  have hUmom := n4_lintegral_rpow_le (μ := normLGFLaw d) (fun g => zero_le_one.trans (hU1 g)) hc
    hUexp hp2
  have hint_le : ∫⁻ ω, (∑' j, ENNReal.ofReal (coordDeriv G j ω ^ 2)) ^ (p / 2) ∂stdP ≤
      ENNReal.ofReal Y := by
    have hpt : ∀ g, ENNReal.ofReal ((ξ ^ 2 * (F.Cb * U g)) ^ (p / 2)) =
        ENNReal.ofReal ((ξ ^ 2 * F.Cb) ^ (p / 2)) * ENNReal.ofReal (U g ^ (p / 2)) := fun g => by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
        Real.mul_rpow (by positivity) (zero_le_one.trans (hU1 g))]
    have hmeas : Measurable fun g => ENNReal.ofReal ((ξ ^ 2 * (F.Cb * U g)) ^ (p / 2)) :=
      ((measurable_const.mul (measurable_const.mul hUm)).pow_const _).ennreal_ofReal
    calc ∫⁻ ω, (∑' j, ENNReal.ofReal (coordDeriv G j ω ^ 2)) ^ (p / 2) ∂stdP
        ≤ ∫⁻ ω, ENNReal.ofReal ((ξ ^ 2 * (F.Cb * U (F.T ω))) ^ (p / 2)) ∂stdP := by
          refine lintegral_mono_ae ?_
          filter_upwards [hsq] with ω hω
          have hnn : 0 ≤ ξ ^ 2 * (F.Cb * U (F.T ω)) :=
            mul_nonneg (sq_nonneg ξ) (mul_nonneg hCb (zero_le_one.trans (hU1 _)))
          rw [← ENNReal.ofReal_rpow_of_nonneg hnn hp2.le]
          exact ENNReal.rpow_le_rpow hω hp2.le
      _ = ∫⁻ g, ENNReal.ofReal ((ξ ^ 2 * (F.Cb * U g)) ^ (p / 2)) ∂(normLGFLaw d) :=
          hT.lintegral_comp hmeas
      _ = ENNReal.ofReal ((ξ ^ 2 * F.Cb) ^ (p / 2)) *
            ∫⁻ g, ENNReal.ofReal (U g ^ (p / 2)) ∂(normLGFLaw d) := by
          simp_rw [hpt]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((ξ ^ 2 * F.Cb) ^ (p / 2)) *
            ENNReal.ofReal ((p / 2 / c) ^ (p / 2) * M) := by gcongr
      _ = ENNReal.ofReal Y := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hroot : (∫⁻ ω, (∑' j, ENNReal.ofReal (coordDeriv G j ω ^ 2)) ^ (p / 2) ∂stdP) ^ (1 / p) ≤
      ENNReal.ofReal (Y ^ (1 / p)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hY0 (by positivity)]
    exact ENNReal.rpow_le_rpow hint_le (by positivity)
  -- assemble
  have hcp := n4_gaussLpConst_le hp1
  have hYb := n4_rpow_one_div_le hξ0.le hCb hc hM hp1
  rw [← hYdef] at hYb
  have heL : eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d))) (ENNReal.ofReal p) (normLGFLaw d) =
      eLpNorm G (ENNReal.ofReal p) stdP := by
    rw [hGeq, eLpNorm_comp_measurePreserving hFm.aestronglyMeasurable hT]
  rw [heL]
  have hcp0 : 0 ≤ Real.pi / 2 * (∫ x, |x| ^ p ∂(gaussianReal 0 1)) ^ (1 / p) := by
    have : 0 ≤ ∫ x, |x| ^ p ∂(gaussianReal 0 1) :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _
    positivity
  calc eLpNorm G (ENNReal.ofReal p) stdP
      ≤ ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂(gaussianReal 0 1)) ^ (1 / p)) *
          (∫⁻ ω, (∑' j, ENNReal.ofReal (coordDeriv G j ω ^ 2)) ^ (p / 2) ∂stdP) ^ (1 / p) := hLp
    _ ≤ ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂(gaussianReal 0 1)) ^ (1 / p)) *
          ENNReal.ofReal (Y ^ (1 / p)) := by gcongr
    _ = ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂(gaussianReal 0 1)) ^ (1 / p) *
          Y ^ (1 / p)) := (ENNReal.ofReal_mul hcp0).symm
    _ ≤ ENNReal.ofReal (2 * Real.pi * Real.sqrt (F.Cb / (2 * c)) * max M 1 * p * ξ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
        calc Real.pi / 2 * (∫ x, |x| ^ p ∂(gaussianReal 0 1)) ^ (1 / p) * Y ^ (1 / p)
            ≤ (2 * Real.pi * Real.sqrt p) *
                (ξ * Real.sqrt (F.Cb / (2 * c)) * Real.sqrt p * max M 1) :=
              mul_le_mul hcp hYb (by positivity) (by positivity)
          _ = 2 * Real.pi * Real.sqrt (F.Cb / (2 * c)) * max M 1 * (Real.sqrt p * Real.sqrt p) * ξ := by
              ring
          _ = 2 * Real.pi * Real.sqrt (F.Cb / (2 * c)) * max M 1 * p * ξ := by rw [hsp]

/-- **Concentration of the log unit distance** (blueprint Part C `c:prop-conc`; NA4 A1 Step 4, [9] (3.20)–(3.21)
without the log-Sobolev bootstrap): for `d ≥ 3`, `UniformEstimates d ξ̄ 1` and a pairing frame `F`, there is `C₃`
(depending only on `d`, `ξ̄` and the frame) such that `‖log ρ^D(0, e₁)‖_{L^p(ℙ)} ≤ C₃ p ξ` for every
`ξ ∈ (0, ξ̄]`, every `D` strong at `ξ` and every `p ≥ 1`. -/
theorem concentration_logRho {d : ℕ} (hd : 3 ≤ d) {ξbar : ℝ} (hU : UniformEstimates d ξbar 1)
    (F : PairingFrame d) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → ∀ p : ℝ, 1 ≤ p →
        eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d))) (ENNReal.ofReal p) (normLGFLaw d) ≤
          ENNReal.ofReal (C₃ * p * ξ) := by
  obtain ⟨C₃, hC₃, h⟩ := concentration_logRho_of_two_le hd hU F
  refine ⟨2 * C₃, by positivity, fun ξ hξ D hD p hp => ?_⟩
  have : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d (by omega)).1
  rcases le_total 2 p with hp2 | hp2
  · refine (h ξ hξ D hD p hp2).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ C₃ * p * ξ := by have := hξ.1; positivity
    nlinarith
  · have hFm : Measurable fun g => Real.log ((rho D g).1 (0, e₁ d)) :=
      measurable_log_rho_apply hD.measurable _
    calc eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d))) (ENNReal.ofReal p) (normLGFLaw d)
        ≤ eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d))) (ENNReal.ofReal 2) (normLGFLaw d) :=
          eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hp2)
            hFm.aestronglyMeasurable
      _ ≤ ENNReal.ofReal (C₃ * 2 * ξ) := h ξ hξ D hD 2 le_rfl
      _ ≤ ENNReal.ofReal (2 * C₃ * p * ξ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hξ0 := hξ.1
          have : 0 ≤ C₃ * ξ := by positivity
          nlinarith

/-- **`ConcentrationStmt`** (interface I20; producer N4, consumer N5): from Lemma 2.1 on one subcritical window
`(0, ξ̄]` and a pairing frame, `‖log ρ^D(0, e₁)‖_p ≤ C p ξ` for `ξ ∈ (0, ξ̄]`, `D` strong at `ξ`, `p ≥ 2`
(`ξ₂ = ξ̄`). The subcriticality of `ξ̄` is not used by the proof (it is part of the interface signature). -/
theorem concentration_of {d : ℕ} (hd : 3 ≤ d) {ξbar : ℝ} (hξ : 0 < ξbar)
    (_hsub : Real.sqrt (2 * d) < distExp d ξbar) (hU : UniformEstimates d ξbar 1) (F : PairingFrame d) :
    ConcentrationStmt d := by
  obtain ⟨C, hC, h⟩ := concentration_logRho hd hU F
  exact ⟨ξbar, C, hξ, hC, fun ξ hξ' D hD p hp => h ξ hξ' D hD p (by linarith)⟩

end HigherDimLQGContinuity
