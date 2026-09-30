import QuantumZipper.Proofs.Zipper.TipXScaleGauss

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SC-G (2): a scaled moment bound by Cauchy–Schwarz

`lintegral_scaled_moment_le`: with `a = radius k = 2^{-k}`, `γ = √κ`, if
`E e^{pγ g} = e^{(pγ)² k log 2}` and `E Ā^q ≤ C` with `2p ≤ q`, then
`E (a^{2-κ/4} e^{γ g/2} Ā)^p ≤ (1 + C)^{1/2} (2^{-(p(2-κ/4) - p²κ/2)})^k`.

Own elementary argument: Cauchy–Schwarz (`ENNReal.lintegral_mul_le_Lp_mul_Lq`, exponents 2,2)
`E[e^{pγg/2} Ā^p] ≤ (E e^{pγg})^{1/2} (E Ā^{2p})^{1/2}` and `Ā^{2p} ≤ 1 + Ā^q` (as `2p ≤ q`).
-/

noncomputable section

open MeasureTheory

namespace QuantumZipper.WedgeUnzip

/-- `y^{2p} ≤ 1 + y^q` for `0 ≤ 2p ≤ q`. -/
theorem txsc_rpow_le_one_add {r q : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q) (y : ENNReal) :
    y ^ r ≤ 1 + y ^ q := by
  rcases le_total y 1 with h | h
  · exact (ENNReal.rpow_le_one h hr).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le h hrq).trans le_add_self

theorem lintegral_scaled_moment_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ p q : ℝ} (hκ : 0 < κ) (hp : 0 < p) (h2p : 2 * p ≤ q)
    {g : Ω → ℝ} (hg : Measurable g) (k : ℕ)
    (hmgf : ∫⁻ ω, ENNReal.ofReal (Real.exp ((p * Real.sqrt κ) * g ω)) ∂P =
      ENNReal.ofReal (Real.exp ((p * Real.sqrt κ) ^ 2 * ((k : ℝ) * Real.log 2))))
    {Abar : Ω → ENNReal} (hA : AEMeasurable Abar P) {C : ENNReal}
    (hC : ∫⁻ ω, Abar ω ^ q ∂P ≤ C) :
    ∫⁻ ω, (ENNReal.ofReal (radius k ^ (2 - κ / 4) * Real.exp (Real.sqrt κ * g ω / 2)) *
        Abar ω) ^ p ∂P ≤
      (1 + C) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(p * (2 - κ / 4) - p ^ 2 * κ / 2))) ^ k := by
  set e : ℝ := 2 - κ / 4
  set γ : ℝ := Real.sqrt κ
  set L : ℝ := (k : ℝ) * Real.log 2
  have hrad : radius k = Real.exp (-L) := txsc_radius_eq_exp k
  have hae : 0 ≤ radius k ^ e := Real.rpow_nonneg (by rw [hrad]; exact (Real.exp_pos _).le) _
  set f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (p * γ / 2 * g ω))
  set h : Ω → ENNReal := fun ω => Abar ω ^ p
  have hpt : ∀ ω, (ENNReal.ofReal (radius k ^ e * Real.exp (γ * g ω / 2)) * Abar ω) ^ p =
      ENNReal.ofReal ((radius k ^ e) ^ p) * (f * h) ω := by
    intro ω
    have hx : Real.exp (γ * g ω / 2) ^ p = Real.exp (p * γ / 2 * g ω) := by
      rw [← Real.exp_mul]; ring_nf
    simp only [f, h, Pi.mul_apply]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_mul hae,
      ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_rpow_of_nonneg hae hp.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp.le, hx, mul_assoc]
  have hfm : AEMeasurable f P := by
    refine (Measurable.ennreal_ofReal ?_).aemeasurable
    exact Real.measurable_exp.comp (hg.const_mul _)
  have hhm : AEMeasurable h P := hA.pow_const p
  -- the two Cauchy–Schwarz factors
  have hf2 : ∫⁻ ω, f ω ^ (2 : ℝ) ∂P = ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * L)) := by
    rw [← hmgf]
    refine lintegral_congr fun ω => ?_
    simp only [f]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
    congr 2; ring
  have hh2 : ∫⁻ ω, h ω ^ (2 : ℝ) ∂P ≤ 1 + C := by
    calc ∫⁻ ω, h ω ^ (2 : ℝ) ∂P ≤ ∫⁻ ω, (1 + Abar ω ^ q) ∂P := by
          refine lintegral_mono fun ω => ?_
          simp only [h]
          rw [← ENNReal.rpow_mul]
          exact txsc_rpow_le_one_add (by positivity) (by linarith) _
      _ = 1 + ∫⁻ ω, Abar ω ^ q ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + C := add_le_add le_rfl hC
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hfm hhm
  rw [hf2] at hCS
  have hsq : ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * L)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * L / 2)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
    congr 2; ring
  rw [hsq] at hCS
  have hmain : ∫⁻ ω, (f * h) ω ∂P ≤
      ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * L / 2)) * (1 + C) ^ (1 / 2 : ℝ) :=
    hCS.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hh2 (by norm_num)))
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal ((radius k ^ e) ^ p) * ∫⁻ ω, (f * h) ω ∂P
      ≤ ENNReal.ofReal ((radius k ^ e) ^ p) *
          (ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * L / 2)) * (1 + C) ^ (1 / 2 : ℝ)) :=
        mul_le_mul' le_rfl hmain
    _ = (1 + C) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(p * e - p ^ 2 * κ / 2))) ^ k := by
        rw [← mul_assoc, mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hae _),
          ← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]
        congr 2
        have hγ : γ ^ 2 = κ := Real.sq_sqrt hκ.le
        rw [hrad, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add,
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
        congr 1
        rw [mul_pow, hγ]
        simp only [L]; ring

end QuantumZipper.WedgeUnzip
