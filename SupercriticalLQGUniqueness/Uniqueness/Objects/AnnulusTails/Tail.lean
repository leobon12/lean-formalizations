import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Up




 


















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC)

 
theorem exists_kappa {q A B : ℝ} (hq : 0 < q) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ q * (A + B * Real.sqrt (6 * (κ + 3))) ≤ κ := by
  set κ : ℝ := 2 * q * A + 48 * q ^ 2 * B ^ 2 + 3 with hκdef
  have hκ3 : 3 ≤ κ := by
    have : 0 ≤ 2 * q * A + 48 * q ^ 2 * B ^ 2 := by positivity
    rw [hκdef]
    linarith
  refine ⟨κ, by linarith, ?_⟩
  have h1 : q * A ≤ κ / 2 := by rw [hκdef]; nlinarith [sq_nonneg (q * B)]
  have h2 : q * B * Real.sqrt (6 * (κ + 3)) ≤ κ / 2 := by
    have hqB : 0 ≤ q * B := mul_nonneg hq.le hB
    have hsq : q * B * Real.sqrt (6 * (κ + 3)) = Real.sqrt ((q * B) ^ 2 * (6 * (κ + 3))) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hqB]
    rw [hsq, Real.sqrt_le_left (by linarith)]
    have hκ48 : 48 * q ^ 2 * B ^ 2 ≤ κ := by rw [hκdef]; nlinarith
    have : (q * B) ^ 2 * (6 * (κ + 3)) ≤ (q * B) ^ 2 * (12 * κ) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    calc (q * B) ^ 2 * (6 * (κ + 3)) ≤ (q * B) ^ 2 * (12 * κ) := this
      _ = (48 * q ^ 2 * B ^ 2) * κ / 4 := by ring
      _ ≤ κ * κ / 4 := by gcongr
      _ = (κ / 2) ^ 2 := by ring
  nlinarith

 

theorem dyadic_index_bounds {R Λ κ : ℝ} (hR : 1 ≤ R) (hΛ : 0 < Λ) (hκ : 0 ≤ κ) :
    let n : ℕ := ⌊Real.log R / (Λ * Real.log 16)⌋₊
    Real.exp (n * Real.log 16 * Λ) ≤ R ∧
      Real.exp (-(κ * n * Real.log 16)) ≤ Real.exp (κ * Real.log 16) * R ^ (-(κ / Λ)) := by
  intro n
  have hlam : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hΛl : 0 < Λ * Real.log 16 := mul_pos hΛ hlam
  have hfl := Nat.floor_le (div_nonneg hlogR hΛl.le)
  have hfl2 := Nat.lt_floor_add_one (Real.log R / (Λ * Real.log 16))
  constructor
  · rw [← Real.exp_log hR0]
    apply Real.exp_le_exp.mpr
    have := (le_div_iff₀ hΛl).1 hfl
    linarith
  · rw [Real.rpow_def_of_pos hR0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : Real.log R < (n + 1) * (Λ * Real.log 16) := (div_lt_iff₀ hΛl).1 hfl2
    have h2 : Real.log R * (κ / Λ) ≤ (n + 1) * (Λ * Real.log 16) * (κ / Λ) :=
      mul_le_mul_of_nonneg_right h1.le (div_nonneg hκ hΛ.le)
    have h3 : (n + 1) * (Λ * Real.log 16) * (κ / Λ) = κ * n * Real.log 16 + κ * Real.log 16 := by
      field_simp
    nlinarith

 

theorem acr_lower_tail (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {a b : ℝ} (ha : 0 < a) (hab : a < b) (q : ℝ) (hq : 0 < q) :
    ∃ R₀ C : ℝ, 1 ≤ R₀ ∧ 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ R : ℝ, R₀ ≤ R → ∀ (s : Ioi (0 : ℝ)) (y : ℂ),
          P {ω | Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) <
              ENNReal.ofReal R⁻¹ * nrm ξ Q (h ω) s y} ≤ ENNReal.ofReal (C * R ^ (-q)) := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hlam : 0 < Real.log 16 := Real.log_pos (by norm_num)
  obtain ⟨κ, hκ, hqκ⟩ := exists_kappa (A := 1 + 2 * ξ * Q) (B := ξ) hq (by positivity) hξ.le
  set L : ℝ := 1 + 2 * ξ * Q + ξ * Real.sqrt (6 * (κ + 3)) with hLdef
  have hL : 0 < L := by rw [hLdef]; positivity
  obtain ⟨n₀, C₁, hC₁, hdy⟩ := acr_lower_tail_dyadic ξ Q hQ D hD ha hab κ hκ
  refine ⟨Real.exp ((n₀ + 1) * Real.log 16 * L), C₁ * Real.exp (κ * Real.log 16),
    Real.one_le_exp (by positivity), by positivity, ?_⟩
  intro Ω _ P _ h hh R hR s y
  have hR1 : 1 ≤ R := le_trans (Real.one_le_exp (by positivity)) hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨hnR, hnexp⟩ := dyadic_index_bounds hR1 hL hκ.le
  set n : ℕ := ⌊Real.log R / (L * Real.log 16)⌋₊ with hndef
  have hn : n₀ ≤ n := by
    rw [hndef]
    apply Nat.le_floor
    rw [le_div_iff₀ (mul_pos hL hlam), ← Real.exp_le_exp, Real.exp_log hR0]
    refine le_trans (Real.exp_le_exp.mpr ?_) hR
    have : (n₀ : ℝ) ≤ n₀ + 1 := by linarith
    nlinarith
  have hsub : {ω | Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) <
      ENNReal.ofReal R⁻¹ * nrm ξ Q (h ω) s y} ⊆
      {ω | Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) <
        ENNReal.ofReal (Real.exp (-(n * Real.log 16 * L))) * nrm ξ Q (h ω) s y} := by
    intro ω hω
    refine lt_of_lt_of_le hω (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hnR
  calc P {ω | Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) < ENNReal.ofReal R⁻¹ * nrm ξ Q (h ω) s y}
      ≤ P {ω | Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) <
          ENNReal.ofReal (Real.exp (-(n * Real.log 16 * L))) * nrm ξ Q (h ω) s y} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (-(κ * n * Real.log 16))) := hdy P h hh n hn s y
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (κ * Real.log 16) * R ^ (-q)) := by
        apply ENNReal.ofReal_le_ofReal
        have hpow : R ^ (-(κ / L)) ≤ R ^ (-q) := by
          apply Real.rpow_le_rpow_of_exponent_le hR1
          rw [neg_le_neg_iff, le_div_iff₀ hL]
          rw [hLdef]
          linarith
        calc C₁ * Real.exp (-(κ * n * Real.log 16))
            ≤ C₁ * (Real.exp (κ * Real.log 16) * R ^ (-(κ / L))) := by gcongr
          _ ≤ C₁ * (Real.exp (κ * Real.log 16) * R ^ (-q)) := by gcongr
          _ = C₁ * Real.exp (κ * Real.log 16) * R ^ (-q) := by ring

 

theorem around_upper_tail (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {a b : ℝ} (ha : 0 < a) (hab : a < b) (q : ℝ) (hq : 0 < q) :
    ∃ R₀ C : ℝ, 1 ≤ R₀ ∧ 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ R : ℝ, R₀ ≤ R → ∀ (s : Ioi (0 : ℝ)) (y : ℂ),
          P {ω | ENNReal.ofReal R * nrm ξ Q (h ω) s y <
              Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s)} ≤ ENNReal.ofReal (C * R ^ (-q)) := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hlam : 0 < Real.log 16 := Real.log_pos (by norm_num)
  obtain ⟨κ, hκ, hqκ⟩ := exists_kappa (A := 3) (B := ξ) hq (by norm_num) hξ.le
  set H : ℝ := 3 + ξ * Real.sqrt (6 * (κ + 3)) with hHdef
  have hH : 0 < H := by rw [hHdef]; positivity
  obtain ⟨n₀, C₁, hC₁, hdy⟩ := around_upper_tail_dyadic ξ Q hQ D hD ha hab κ hκ
  refine ⟨Real.exp ((n₀ + 1) * Real.log 16 * H), C₁ * Real.exp (κ * Real.log 16),
    Real.one_le_exp (by positivity), by positivity, ?_⟩
  intro Ω _ P _ h hh R hR s y
  have hR1 : 1 ≤ R := le_trans (Real.one_le_exp (by positivity)) hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨hnR, hnexp⟩ := dyadic_index_bounds hR1 hH hκ.le
  set n : ℕ := ⌊Real.log R / (H * Real.log 16)⌋₊ with hndef
  have hn : n₀ ≤ n := by
    rw [hndef]
    apply Nat.le_floor
    rw [le_div_iff₀ (mul_pos hH hlam), ← Real.exp_le_exp, Real.exp_log hR0]
    refine le_trans (Real.exp_le_exp.mpr ?_) hR
    have : (n₀ : ℝ) ≤ n₀ + 1 := by linarith
    nlinarith
  have hsub : {ω | ENNReal.ofReal R * nrm ξ Q (h ω) s y <
      Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s)} ⊆
      {ω | ENNReal.ofReal (Real.exp (n * Real.log 16 * H)) * nrm ξ Q (h ω) s y <
        Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s)} := by
    intro ω hω
    exact lt_of_le_of_lt (mul_le_mul' (ENNReal.ofReal_le_ofReal hnR) le_rfl) hω
  calc P {ω | ENNReal.ofReal R * nrm ξ Q (h ω) s y < Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s)}
      ≤ P {ω | ENNReal.ofReal (Real.exp (n * Real.log 16 * H)) * nrm ξ Q (h ω) s y <
          Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (-(κ * n * Real.log 16))) := hdy P h hh n hn s y
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (κ * Real.log 16) * R ^ (-q)) := by
        apply ENNReal.ofReal_le_ofReal
        have hpow : R ^ (-(κ / H)) ≤ R ^ (-q) := by
          apply Real.rpow_le_rpow_of_exponent_le hR1
          rw [neg_le_neg_iff, le_div_iff₀ hH]
          rw [hHdef]
          linarith
        calc C₁ * Real.exp (-(κ * n * Real.log 16))
            ≤ C₁ * (Real.exp (κ * Real.log 16) * R ^ (-(κ / H))) := by gcongr
          _ ≤ C₁ * (Real.exp (κ * Real.log 16) * R ^ (-q)) := by gcongr
          _ = C₁ * Real.exp (κ * Real.log 16) * R ^ (-q) := by ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
