import HigherDimLQGContinuity.MomentsW2.Scale

/-!
# Uniform scale tail at the middle-shell cutoff

This file turns the reusable cluster, field and CRUDE estimates into one
geometric lower-tail estimate at every coarse scale below the cutoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP
open HigherDimLFPP.DGZ (cbox)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- Gaussian coarse-field estimate with exponential decay in the dyadic scale. -/
theorem w2_coarse_geom (hκ : IsLFPPKernel κ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b μ ξ A : ℝ}, 0 < b → UHyp d κ b μ ξ →
      2 * b * (Real.sqrt (2 * d) + 2 * C / Real.log 2) ≤ A →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H → ∀ m : ℕ, 1 ≤ m →
          P {ω | ∃ z ∈ cbox (0 : Rd d) R,
            A * m * Real.log 2 < -(ξ * H m z ω)} ≤
              ENNReal.ofReal (2 * (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m))) := by
  obtain ⟨C, hC, htail⟩ := w2_coarse_tail hκ hR
  refine ⟨C, hC, ?_⟩
  intro b μ ξ A hb hξ hA Ω _ P W H hH m hm
  have hlog0 := (DGZ.log_two_pos_lt_one).1
  have hlog1 := (DGZ.log_two_pos_lt_one).2
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqr : Real.sqrt (m * Real.log 2) ≤ m := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith only [hmreal, hlog1]
  have hbase : Real.sqrt (2 * d) * (m * Real.log 2) +
      C * Real.sqrt (m * Real.log 2) + C ≤
      (Real.sqrt (2 * d) + 2 * C / Real.log 2) * m * Real.log 2 := by
    have hc1 : C * Real.sqrt (m * Real.log 2) ≤ C * m :=
      mul_le_mul_of_nonneg_left hsqr hC
    have hc2 : C ≤ C * m := le_mul_of_one_le_right hC hmreal
    have he : (2 * C / Real.log 2) * m * Real.log 2 = 2 * C * m := by field_simp
    calc
      Real.sqrt (2 * d) * (m * Real.log 2) + C * Real.sqrt (m * Real.log 2) + C
          ≤ Real.sqrt (2 * d) * (m * Real.log 2) + 2 * C * m := by
            linarith only [hc1, hc2]
      _ = (Real.sqrt (2 * d) + 2 * C / Real.log 2) * m * Real.log 2 := by
        rw [add_mul, add_mul, he]
        ring
  have hA0 : 0 ≤ A := by
    have h0 : 0 ≤ 2 * b * (Real.sqrt (2 * d) + 2 * C / Real.log 2) := by positivity
    exact h0.trans hA
  have hthreshold : 2 * b * (Real.sqrt (2 * d) * (m * Real.log 2) +
      C * Real.sqrt (m * Real.log 2) + C) ≤ A * m * Real.log 2 := by
    have h1 := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 2 * b)
    have h2 := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ (m : ℝ) * Real.log 2)
    nlinarith only [h1, h2]
  have hgauss := htail hb hξ Ω P W H hH m hm
    (mul_nonneg (mul_nonneg hA0 (by positivity)) hlog0.le)
    hthreshold
  have he : -(A * m * Real.log 2) ^ 2 /
      (8 * b ^ 2 * (m * Real.log 2)) =
      -(A ^ 2 / (8 * b ^ 2) * m) * Real.log 2 := by
    field_simp
  rw [he] at hgauss
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  simpa only [mul_comm] using hgauss

/-- Middle-scale lower tail with a linear bad-cluster diameter. -/
theorem w2_middle_geom (hd : 2 ≤ d) (hκ : IsLFPPKernel κ)
    (hCr : CrudeLowerShape d κ) (hN : UNondegShape d κ) (hQ : UQuantCompShape d κ)
    {b μ r₁ r₂ : ℝ} (hb : 0 < b) (hμ : 0 < μ)
    (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : ℝ, 2 * b * (Real.sqrt (2 * d) + 2 * C / Real.log 2) ≤ A →
        ∀ L : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
            (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
            DGZ.IsDyadicRealization κ P W H → ∀ m n : ℕ, 1 ≤ m → m ≤ n →
              ((2 * L * m : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ m + 8 * (2 : ℝ)⁻¹ ^ m ≤ r₁ - r₂ →
              P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
                DGZ.aQ P H ξ n 2⁻¹ <
                  (c₀ / 4) * (2 : ℝ) ^ (-((A + 1 + b ^ 2 / 2) * m))} ≤
                ENNReal.ofReal (2 * (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m))) +
                  ENNReal.ofReal ((2 * r₁ + 3) ^ d *
                    (2 : ℝ) ^ (((d : ℝ) - L) * m)) := by
  obtain ⟨c₀, hc₀, hnorm⟩ := w2_normalized_tail hd hκ hCr hN hQ hb hμ
  obtain ⟨C, hC, hcoarse⟩ := w2_coarse_geom hκ (R := r₁ + 1) (by linarith)
  refine ⟨c₀, hc₀, C, hC, ?_⟩
  intro A hA L ξ hξ Ω _ P W H hH m n hm hmn hgeom
  let N : ℕ := ⌈r₁ / ((2 : ℝ)⁻¹ ^ m)⌉₊
  have hNb := w2_ceil_bounds (by linarith : 0 ≤ r₁) m
  dsimp only at hNb
  have hs2 : (2 : ℝ)⁻¹ ^ m ≤ 1 / 2 := by
    calc
      (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ (1 : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1 / 2 := by norm_num
  have htail := hnorm ξ hξ Ω P W H hH m n hmn r₁ r₂ (A * m * Real.log 2)
    hr₂.le hr hs2 N (2 * L * m) hNb.1 hgeom
  rw [w2_threshold_eq] at htail
  have hf := hcoarse hb hξ hA Ω P W H hH m hm
  have hp := w2_peierls_le (d := d) (L := L) (m := m) hNb.2
  exact htail.trans (add_le_add hf hp)

/-- The coarse field at depth `n ≤ m` still has a Gaussian tail in the larger scale `m`. -/
theorem w2_coarse_late_geom (hκ : IsLFPPKernel κ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b μ ξ A : ℝ}, 0 < b → UHyp d κ b μ ξ →
      2 * b * (Real.sqrt (2 * d) + 2 * C / Real.log 2) ≤ A →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H → ∀ m n : ℕ, 1 ≤ n → n ≤ m →
          P {ω | ∃ z ∈ cbox (0 : Rd d) R,
            A * m * Real.log 2 < -(ξ * H n z ω)} ≤
              ENNReal.ofReal (2 * (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m))) := by
  obtain ⟨C, hC, htail⟩ := w2_coarse_tail hκ hR
  refine ⟨C, hC, ?_⟩
  intro b μ ξ A hb hξ hA Ω _ P W H hH m n hn hnm
  have hlog0 := (DGZ.log_two_pos_lt_one).1
  have hlog1 := (DGZ.log_two_pos_lt_one).2
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnmreal : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hsqr : Real.sqrt (n * Real.log 2) ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith only [hnreal, hlog1]
  have hbase : Real.sqrt (2 * d) * (n * Real.log 2) +
      C * Real.sqrt (n * Real.log 2) + C ≤
      (Real.sqrt (2 * d) + 2 * C / Real.log 2) * n * Real.log 2 := by
    have hc1 : C * Real.sqrt (n * Real.log 2) ≤ C * n :=
      mul_le_mul_of_nonneg_left hsqr hC
    have hc2 : C ≤ C * n := le_mul_of_one_le_right hC hnreal
    have he : (2 * C / Real.log 2) * n * Real.log 2 = 2 * C * n := by field_simp
    calc
      _ ≤ Real.sqrt (2 * d) * (n * Real.log 2) + 2 * C * n := by linarith only [hc1, hc2]
      _ = _ := by rw [add_mul, add_mul, he]; ring
  have hA0 : 0 ≤ A := by
    have h0 : 0 ≤ 2 * b * (Real.sqrt (2 * d) + 2 * C / Real.log 2) := by positivity
    exact h0.trans hA
  have hthreshold : 2 * b * (Real.sqrt (2 * d) * (n * Real.log 2) +
      C * Real.sqrt (n * Real.log 2) + C) ≤ A * m * Real.log 2 := by
    have h1 := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 2 * b)
    have h2 := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ (n : ℝ) * Real.log 2)
    have h3 := mul_le_mul_of_nonneg_left hnmreal hA0
    nlinarith only [h1, h2, h3, hlog0]
  have ht : 0 ≤ A * m * Real.log 2 := by positivity
  have hgauss := htail hb hξ Ω P W H hH n hn ht hthreshold
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 8 * b ^ 2 * (n * Real.log 2) := by positivity
  have hsq : (m : ℝ) * n ≤ (m : ℝ) ^ 2 :=
    by simpa only [pow_two] using mul_le_mul_of_nonneg_left hnmreal hm0
  have hexp : -(A * m * Real.log 2) ^ 2 /
      (8 * b ^ 2 * (n * Real.log 2)) ≤
      -(A ^ 2 / (8 * b ^ 2) * m) * Real.log 2 := by
    apply (div_le_iff₀ hden).2
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg _
    have hprod := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg hA2 (sq_nonneg (Real.log 2)))
    calc
      -(A * m * Real.log 2) ^ 2 =
          -(A ^ 2 * Real.log 2 ^ 2 * (m : ℝ) ^ 2) := by ring
      _ ≤ -(A ^ 2 * Real.log 2 ^ 2 * ((m : ℝ) * n)) := neg_le_neg hprod
      _ = -(A ^ 2 / (8 * b ^ 2) * m) * Real.log 2 *
          (8 * b ^ 2 * (n * Real.log 2)) := by field_simp
  have hpower : Real.exp (-(A ^ 2 / (8 * b ^ 2) * m) * Real.log 2) =
      (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  exact hgauss.trans (ENNReal.ofReal_le_ofReal (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← hpower, Real.exp_le_exp]
    exact hexp))

/-- The direct estimate reaches the same threshold when the cutoff is shallower. -/
theorem w2_late_threshold_le {c w b A : ℝ} {m n : ℕ}
    (hw : 0 ≤ w) (hnm : n ≤ m)
    (hsmall : c * (2 : ℝ)⁻¹ ^ m ≤ w) :
    (c / 4) * (2 : ℝ) ^ (-((A + 1 + b ^ 2 / 2) * m)) ≤
      w * Real.exp (-(A * m * Real.log 2)) / (4 * (2 : ℝ) ^ (b ^ 2 * n / 2)) := by
  rw [← w2_threshold_eq]
  have hpow : (2 : ℝ) ^ (b ^ 2 * n / 2) ≤
      (2 : ℝ) ^ (b ^ 2 * m / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hmn : (n : ℝ) ≤ m := by exact_mod_cast hnm
    nlinarith only [hmn, sq_nonneg b]
  have he : Real.exp (-(A * m * Real.log 2)) =
      (Real.exp (A * m * Real.log 2))⁻¹ := by rw [Real.exp_neg]
  rw [he]
  have he' : c * (2 : ℝ)⁻¹ ^ m /
      (4 * Real.exp (A * m * Real.log 2) * (2 : ℝ) ^ (b ^ 2 * m / 2)) =
      (c * (2 : ℝ)⁻¹ ^ m * (Real.exp (A * m * Real.log 2))⁻¹ / 4) /
      (2 : ℝ) ^ (b ^ 2 * m / 2) := by ring
  rw [he']
  have hfac : 0 ≤ (Real.exp (A * m * Real.log 2))⁻¹ / 4 := by positivity
  have hnum := mul_le_mul_of_nonneg_right hsmall hfac
  calc
    (c * (2 : ℝ)⁻¹ ^ m * (Real.exp (A * m * Real.log 2))⁻¹ / 4) /
        (2 : ℝ) ^ (b ^ 2 * m / 2) ≤
        (w * (Real.exp (A * m * Real.log 2))⁻¹ / 4) /
          (2 : ℝ) ^ (b ^ 2 * m / 2) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith only [hnum]
    _ ≤ (w * (Real.exp (A * m * Real.log 2))⁻¹ / 4) /
          (2 : ℝ) ^ (b ^ 2 * n / 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by ring

/-- The zero-th dyadic band vanishes almost surely. -/
theorem w2_coarse_zero (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : DGZ.IsDyadicRealization κ P W H) (ξ t R : ℝ) (ht : 0 ≤ t) :
    P {ω | ∃ z ∈ cbox (0 : Rd d) R, t < -(ξ * H 0 z ω)} = 0 := by
  have hzero := DGZ.ae_forall_eq_zero_of_isBandVersion_self hκ hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  refine measure_mono_null ?_ (ae_iff.1 hzero)
  intro ω hω
  obtain ⟨z, _, hz⟩ := hω
  have hh : H 0 z ω ≠ 0 := by
    intro he
    rw [he, mul_zero, neg_zero] at hz
    exact (not_lt_of_ge ht) hz
  exact fun ha => hh (ha z)

end HigherDimLQGContinuity
