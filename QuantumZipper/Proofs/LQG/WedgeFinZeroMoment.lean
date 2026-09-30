import QuantumZipper.Proofs.LQG.WedgeFinZeroBox

/-!
# WEDGE-FIN0, part 2: small fractional moments of `μ(B(0, 2^{-m-5}) ∩ ℍ)`

Continuation of `WedgeFinZeroBox`. With `eA(p) = p(2 + γ²/2) − p²γ²` (`FinArea.eA`):

* `lintegral_Sf_rpow_le`: for `eA(p) > 1`, `E S_m^p ≤ c_S 2^{-2pm}` (sum of the box bounds
  `lintegral_Mb_rpow_le'` over the Whitney boxes; geometric in the level);
* `lintegral_ball_rpow_le`: for every `0 < p' ≤ p`,
  `E μ_Z(B(0,2^{-m-5}) ∩ ℍ)^{p'} ≤ C 2^{-m eA(p')}`, from the pathwise bound `μ ≤ A_m S_m`,
  independence of `A_m` and `S_m`, the lognormal moment of `A_m`, and Jensen `E S^{p'} ≤ (E S^p)^{p'/p}`.

This is the area analogue at the boundary point `0` of the M4-P3(b) bound used by
`LogSingGood.ae_summable_tail_offsets`: `E μ(B(0,δ) ∩ ℍ)^{p'} ≲ δ^{p'γQ − p'²γ²}`, `γQ = 2 + γ²/2`
(Duplantier–Sheffield, Invent. Math. 185 (2011), §3; the exponent is the lognormal moment of the
circle average at scale `δ`). The constants are our own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace WedgeFinZero

open FinArea

theorem log_radius (m : ℕ) : log (radius m) = -(m : ℝ) * log 2 := by
  have := BdryExist.log_one_div_radius m
  rw [one_div, log_inv] at this; linarith

/-- The geometric ratio `2^{-(eA(p) − 1)}`. -/
def qR (γ p : ℝ) : ℝ := exp (-(log 2 * (eA γ p - 1)))

/-- The constant of `E S_m^p`. -/
def cS (γ p : ℝ) : ℝ := 8 * exp (cA γ 1 p - 6 * log 2 * eA γ p) * (1 - qR γ p)⁻¹

theorem box_exp_eq (γ p : ℝ) (m i : ℕ) :
    radius m ^ (-(p * (γ ^ 2 / 2))) *
      (exp (cA γ (radius m) p) * exp (-((m + 6 + i : ℕ) : ℝ) * log 2 * eA γ p)) =
    exp (cA γ 1 p - 6 * log 2 * eA γ p) * exp (-(2 * p * log 2)) ^ m *
      exp (-(log 2 * eA γ p)) ^ i := by
  rw [rpow_def_of_pos (radius_pos m), log_radius, ← exp_nat_mul, ← exp_nat_mul]
  simp only [← exp_add]
  congr 1
  simp only [cA, eA, log_one, log_radius]
  push_cast; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The box bound in explicit form. -/
theorem lintegral_Mb_rpow_le' [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {m i : ℕ} {j : ℤ} (hj : j ∈ jSet i) :
    ∫⁻ ω, Mb γ m i j (innerSampleC X 0 (radius m) ω) ^ p ∂P ≤
      ENNReal.ofReal (exp (cA γ 1 p - 6 * log 2 * eA γ p) * exp (-(2 * p * log 2)) ^ m *
        exp (-(log 2 * eA γ p)) ^ i) := by
  have hr := radius_pos m
  have h1 := lintegral_Mb_rpow_le hX (P := P) γ hp0 hp1 (m := m) hj
  have hbs := box_spec (m := m) hj
  have h2 := fracBoundC_boxK_le (γ := γ) (R := radius m) hp0 (n := m + 6 + i) j
    (by linarith [abs_nonneg ((j : ℝ) * radius (m + 6 + i))])
  have hc : ENNReal.ofReal (radius m ^ (-(p * (γ ^ 2 / 2)))) *
      ENNReal.ofReal (radius m ^ (γ ^ 2 / 2)) ^ p = 1 := by
    rw [ENNReal.ofReal_rpow_of_nonneg (rpow_nonneg hr.le _) hp0.le,
      ← ENNReal.ofReal_mul (rpow_nonneg hr.le _), ← rpow_mul hr.le, ← rpow_add hr,
      show -(p * (γ ^ 2 / 2)) + γ ^ 2 / 2 * p = 0 by ring, rpow_zero, ENNReal.ofReal_one]
  calc ∫⁻ ω, Mb γ m i j (innerSampleC X 0 (radius m) ω) ^ p ∂P
      = ENNReal.ofReal (radius m ^ (-(p * (γ ^ 2 / 2)))) *
          (ENNReal.ofReal (radius m ^ (γ ^ 2 / 2)) ^ p *
            ∫⁻ ω, Mb γ m i j (innerSampleC X 0 (radius m) ω) ^ p ∂P) := by
        rw [← mul_assoc, hc, one_mul]
    _ ≤ ENNReal.ofReal (radius m ^ (-(p * (γ ^ 2 / 2)))) *
          ENNReal.ofReal (exp (cA γ (radius m) p) *
            exp (-((m + 6 + i : ℕ) : ℝ) * log 2 * eA γ p)) := by
        gcongr; exact h1.trans h2
    _ = _ := by rw [← ENNReal.ofReal_mul (rpow_nonneg hr.le _), box_exp_eq]

/-- **`E S_m^p ≤ c_S 2^{-2pm}`** for `eA(p) > 1`. -/
theorem lintegral_Sf_rpow_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (he : 1 < eA γ p) (m : ℕ) :
    ∫⁻ ω, Sf γ m (innerSampleC X 0 (radius m) ω) ^ p ∂P ≤
      ENNReal.ofReal (cS γ p * exp (-(2 * p * log 2)) ^ m) := by
  set B := exp (cA γ 1 p - 6 * log 2 * eA γ p) * exp (-(2 * p * log 2)) ^ m with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set q0 := exp (-(log 2 * eA γ p)) with hq0d
  have hq00 : 0 ≤ q0 := (exp_pos _).le
  have hq : 2 * q0 = qR γ p := by
    rw [qR, hq0d]
    nth_rewrite 1 [← exp_log (two_pos : (0 : ℝ) < 2)]
    rw [← exp_add]; congr 1; ring
  have hq1 : qR γ p < 1 := Real.exp_lt_one_iff.2 (by nlinarith [log_pos one_lt_two])
  have hqn : 0 ≤ qR γ p := (exp_pos _).le
  have hmeas : ∀ i j, Measurable fun ω => Mb γ m i j (innerSampleC X 0 (radius m) ω) ^ p :=
    fun i j => ((measurable_Mb γ m i j).comp (measurable_innerSampleC hX 0 _)).pow_const p
  calc ∫⁻ ω, Sf γ m (innerSampleC X 0 (radius m) ω) ^ p ∂P
      ≤ ∫⁻ ω, ∑' i, ∑ j ∈ jSet i, Mb γ m i j (innerSampleC X 0 (radius m) ω) ^ p ∂P :=
        lintegral_mono fun ω => (FracMom.rpow_tsum_le_tsum_rpow _ hp0 hp1).trans
          (ENNReal.tsum_le_tsum fun i => rpow_finset_sum_le _ _ hp0 hp1)
    _ = ∑' i, ∑ j ∈ jSet i, ∫⁻ ω, Mb γ m i j (innerSampleC X 0 (radius m) ω) ^ p ∂P := by
        rw [lintegral_tsum fun i => (Finset.measurable_sum _ fun j _ => hmeas i j).aemeasurable]
        congr 1; funext i
        exact lintegral_finsetSum _ fun j _ => hmeas i j
    _ ≤ ∑' i, ∑ j ∈ jSet i, ENNReal.ofReal (B * q0 ^ i) :=
        ENNReal.tsum_le_tsum fun i => Finset.sum_le_sum fun j hj =>
          lintegral_Mb_rpow_le' hX γ hp0 hp1 hj
    _ ≤ ∑' i, ENNReal.ofReal (8 * B * qR γ p ^ i) := ENNReal.tsum_le_tsum fun i => by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← hq, mul_pow]
        calc ((jSet i).card : ℝ) * (B * q0 ^ i) ≤ 8 * 2 ^ i * (B * q0 ^ i) :=
              mul_le_mul_of_nonneg_right (card_jSet_le i) (mul_nonneg hB0 (pow_nonneg hq00 _))
          _ = 8 * B * (2 ^ i * q0 ^ i) := by ring
    _ = ENNReal.ofReal (∑' i, 8 * B * qR γ p ^ i) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (by linarith) (pow_nonneg hqn _))
          ((summable_geometric_of_lt_one hqn hq1).mul_left _)).symm
    _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hqn hq1, cS, hB]; ring_nf

/-- Exponent bookkeeping for the final moment bound. -/
theorem moment_exp_eq (γ : ℝ) {p p' : ℝ} (hp : p ≠ 0) (m : ℕ) :
    radius m ^ (p' * (γ ^ 2 / 2)) * exp ((2 * log 2 - 2 * log (radius m)) * (p' * γ) ^ 2 / 2) *
        (exp (-(2 * p * log 2)) ^ m) ^ (p' / p) =
      exp (log 2 * p' ^ 2 * γ ^ 2) * exp (-(log 2 * eA γ p')) ^ m := by
  rw [rpow_def_of_pos (radius_pos m), log_radius, ← exp_nat_mul, ← exp_nat_mul, ← exp_mul]
  simp only [← exp_add]
  congr 1
  unfold eA
  field_simp
  ring

/-- **Small fractional moments of the area near `0`.** For `0 < p' ≤ p ≤ 1` with
`eA(p) > 1`: `E μ_Z(B(0,2^{-m-5}) ∩ ℍ)^{p'} ≤ C 2^{-m eA(p')}`, `Z = aZ X 2`. -/
theorem lintegral_ball_rpow_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {p p' : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (he : 1 < eA γ p) (hp'0 : 0 < p') (hp'p : p' ≤ p) (m : ℕ) :
    ∫⁻ ω, qAreaMeasure γ (AreaExist.aZ X 2 ω) (Metric.ball 0 (radius (m + 5)) ∩ H) ^ p' ∂P ≤
      ENNReal.ofReal (cS γ p ^ (p' / p) *
        (exp (log 2 * p' ^ 2 * γ ^ 2) * exp (-(log 2 * eA γ p')) ^ m)) := by
  have hδ := radius_pos m
  have hδ1 := BdryExist.radius_le_one m
  have hR : |(0 : ℝ)| + radius m ≤ 2 := by rw [abs_zero]; linarith
  set A : Ω → ℝ≥0∞ := fun ω => Af X γ m ω ^ p' with hA
  set W : Ω → ℝ≥0∞ := fun ω => Sf γ m (innerSampleC X 0 (radius m) ω) ^ p' with hW
  have hφ : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (γ * x) * radius m ^ (γ ^ 2 / 2)) ^ p') :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).pow_const p'
  have hψ : Measurable (fun y : FieldSample => Sf γ m y ^ p') := (measurable_Sf γ m).pow_const p'
  have hind : IndepFun A W P := (indepFun_omega_innerSampleC hX hδ hR).comp hφ hψ
  have hAm : Measurable A := hφ.comp (FracMom.measurable_omegaAvg hX 2 0 _)
  have hWm : Measurable W := hψ.comp (measurable_innerSampleC hX 0 _)
  -- Jensen for the inner sum
  have hJ : ∫⁻ ω, W ω ∂P ≤ ENNReal.ofReal (cS γ p * exp (-(2 * p * log 2)) ^ m) ^ (p' / p) := by
    have hr0 : 0 < p' / p := div_pos hp'0 hp0
    have hr1 : p' / p ≤ 1 := (div_le_one hp0).2 hp'p
    have e : ∀ ω, W ω = (Sf γ m (innerSampleC X 0 (radius m) ω) ^ p) ^ (p' / p) := fun ω => by
      rw [hW, ← ENNReal.rpow_mul, mul_div_cancel₀ _ hp0.ne']
    simp_rw [e]
    refine (FracMom.lintegral_rpow_le_rpow_lintegral
      (((measurable_Sf γ m).comp (measurable_innerSampleC hX 0 _)).pow_const p).aemeasurable
      hr0 hr1).trans ?_
    exact ENNReal.rpow_le_rpow (lintegral_Sf_rpow_le hX γ hp0 hp1 he m) hr0.le
  have hvar : ((2 * log 2 - 2 * log (radius m)).toNNReal : ℝ) =
      2 * log 2 - 2 * log (radius m) := by
    rw [Real.coe_toNNReal]
    have := log_le_log hδ (show radius m ≤ 2 by linarith)
    linarith
  calc ∫⁻ ω, qAreaMeasure γ (AreaExist.aZ X 2 ω) (Metric.ball 0 (radius (m + 5)) ∩ H) ^ p' ∂P
      ≤ ∫⁻ ω, (A * W) ω ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_qAreaMeasure_ball_le hX (P := P) hγ hγ2 m] with ω hω
        show _ ≤ Af X γ m ω ^ p' * Sf γ m (innerSampleC X 0 (radius m) ω) ^ p'
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp'0.le]
        exact ENNReal.rpow_le_rpow hω hp'0.le
    _ = (∫⁻ ω, A ω ∂P) * ∫⁻ ω, W ω ∂P :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hAm hWm hind
    _ ≤ ENNReal.ofReal (radius m ^ (p' * (γ ^ 2 / 2)) *
          exp ((2 * log 2 - 2 * log (radius m)).toNNReal * (p' * γ) ^ 2 / 2)) *
        ENNReal.ofReal (cS γ p * exp (-(2 * p * log 2)) ^ m) ^ (p' / p) := by
        gcongr
        exact le_of_eq (lintegral_omega_factorC_rpow hX γ hδ hR hp'0.le)
    _ = _ := by
        have hcS : 0 ≤ cS γ p := by
          have hq1 : qR γ p < 1 := Real.exp_lt_one_iff.2 (by nlinarith [log_pos one_lt_two])
          rw [cS]; exact mul_nonneg (by positivity) (inv_nonneg.2 (by linarith))
        rw [hvar, ENNReal.ofReal_rpow_of_nonneg (by positivity) (div_pos hp'0 hp0).le,
          ← ENNReal.ofReal_mul (by positivity), mul_rpow hcS (by positivity), mul_left_comm,
          moment_exp_eq γ hp0.ne' m]

end WedgeFinZero
end QuantumZipper
