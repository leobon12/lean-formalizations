import HigherDimLQGContinuity.MomentsW1.CoarseAnalytic

/-!
# Uniform coarse-envelope tail

The one-scale Gaussian estimate is summed over all dyadic scales. The spatial logarithmic penalty
has a coefficient independent of the slope above `√(2d)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

universe u

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox)
open HigherDimLQGMetric.DGZ

variable {d : ℕ}

private theorem wnZR_geometric_tsum {K α r u : ℝ} (hK : 0 ≤ K) (hα : 0 < α) :
    (∑' m : ℕ, ENNReal.ofReal (K * Real.exp (-α * m) * Real.exp (-r * u))) =
      ENNReal.ofReal (K / (1 - Real.exp (-α)) * Real.exp (-r * u)) := by
  have hg0 : 0 ≤ Real.exp (-α) := (Real.exp_pos _).le
  have hg1 : Real.exp (-α) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hα)
  have hden : 0 < 1 - Real.exp (-α) := by linarith
  have hterm (m : ℕ) : ENNReal.ofReal (K * Real.exp (-α * m) * Real.exp (-r * u)) =
      ENNReal.ofReal (K * Real.exp (-r * u)) *
        (ENNReal.ofReal (Real.exp (-α))) ^ m := by
    calc
      ENNReal.ofReal (K * Real.exp (-α * m) * Real.exp (-r * u))
          = ENNReal.ofReal ((K * Real.exp (-r * u)) * Real.exp (-α) ^ m) := by
              congr 1
              rw [← Real.exp_nat_mul]
              ring_nf
      _ = ENNReal.ofReal (K * Real.exp (-r * u)) *
            (ENNReal.ofReal (Real.exp (-α))) ^ m := by
              rw [ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le),
                ENNReal.ofReal_pow hg0]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hg0]
  rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul (div_nonneg hK hden.le),
    ENNReal.ofReal_div_of_pos hden]
  rw [div_eq_mul_inv]
  ac_rfl

/-- The extended coarse envelope has an exponential tail, including infinite excess. -/
theorem wnZRext_tail (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R u : ℝ, 1 ≤ R → 0 ≤ u →
          P {ω | ENNReal.ofReal u < wnZRext (d := d) R Q CZ H ω} ≤
            ENNReal.ofReal (K * Real.exp (-(Real.sqrt (2 * d) / 2) * u)) := by
  obtain ⟨C, hC, hOne⟩ := wnZR_oneScale_tail (d := d) hκ
  obtain ⟨CZ, hCZ, hParams⟩ := wnZR_exists_coarse_parameters d hd hC
  refine ⟨CZ, hCZ, ?_⟩
  intro Q hQ
  obtain ⟨K₀, α, hK₀, hα, hParam⟩ := hParams Q hQ
  let K : ℝ := K₀ / (1 - Real.exp (-α))
  have hgeom : Real.exp (-α) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hα)
  have hden : 0 < 1 - Real.exp (-α) := by linarith
  have hK : 0 < K := div_pos hK₀ hden
  refine ⟨K, hK, ?_⟩
  intro Ω _ P W H hH R u hR hu
  let r : ℝ := Real.sqrt (2 * d) / 2
  let q : ℝ := (Q + Real.sqrt (2 * d)) / 2
  let g : ℝ := (Q - Real.sqrt (2 * d)) / 2
  let c₂ : ℝ := 2 * (C + d + 1)
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have hzero : P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
      Q * 0 * Real.log 2 + CZ * Real.log (2 + R) + u < H 0 z ω} = 0 := by
    simpa only [Nat.cast_zero, mul_zero, zero_mul, zero_add] using
      wnZR_zero_scale_null hκ hH R CZ u (add_nonneg (mul_nonneg hCZ.le hlog) hu)
  have hper (m : ℕ) :
      P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
        Q * m * Real.log 2 + CZ * Real.log (2 + R) + u < H m z ω} ≤
        ENNReal.ofReal (K₀ * Real.exp (-α * m) * Real.exp (-r * u)) := by
    rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm
    · simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at hzero ⊢
      rw [hzero]
      exact zero_le
    · have hm1 : 1 ≤ m := hm
      obtain ⟨hthreshold, hanalytic⟩ := hParam m hm1 R u hR hu
      let a : ℝ := q * (m * Real.log 2) + Real.sqrt (2 * d) * Real.log (2 + R) + u / 2
      let b : ℝ := g * (m * Real.log 2) + c₂ * Real.log (2 + R) + u / 2
      have hq0 : 0 ≤ q := by dsimp [q]; linarith [Real.sqrt_nonneg (2 * d)]
      have hg0 : 0 ≤ g := by dsimp [g]; linarith [Real.sqrt_nonneg (2 * d)]
      have hc₂0 : 0 ≤ c₂ := by dsimp [c₂]; positivity
      have hmL : 0 ≤ (m : ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hb : 0 ≤ b := by dsimp [b]; positivity
      have hsub : {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
          Q * m * Real.log 2 + CZ * Real.log (2 + R) + u < H m z ω} ⊆
          {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5), a + C + b < H m z ω} := by
        rintro ω ⟨z, hz, hlt⟩
        exact ⟨z, hz, lt_of_le_of_lt hthreshold hlt⟩
      have hgauss := hOne hH m R a b ha hb
      have hreal : ((Osc.grid (0 : Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ) *
          (2 * Real.exp (-a ^ 2 / (2 * Real.log (1 / ((2 : ℝ)⁻¹ ^ m)))) +
            2 * Real.exp (-b ^ 2 / C)) ≤
          K₀ * Real.exp (-α * m) * Real.exp (-r * u) := by
        simpa only [a, b, r, q, g, c₂, log_one_div_inv_two_pow, neg_div] using hanalytic
      have hENN : ((Osc.grid (0 : Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ≥0∞) *
          ENNReal.ofReal
            (2 * Real.exp (-a ^ 2 / (2 * Real.log (1 / ((2 : ℝ)⁻¹ ^ m)))) +
              2 * Real.exp (-b ^ 2 / C)) ≤
          ENNReal.ofReal (K₀ * Real.exp (-α * m) * Real.exp (-r * u)) := by
        have h := ENNReal.ofReal_le_ofReal hreal
        simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h
      exact (measure_mono hsub).trans (hgauss.trans hENN)
  calc
    P {ω | ENNReal.ofReal u < wnZRext (d := d) R Q CZ H ω}
        ≤ ∑' m : ℕ, P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
          Q * m * Real.log 2 + CZ * Real.log (2 + R) + u < H m z ω} :=
            wnZRext_tail_tsum P H R Q CZ u
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (K₀ * Real.exp (-α * m) * Real.exp (-r * u)) :=
      ENNReal.tsum_le_tsum hper
    _ = ENNReal.ofReal (K * Real.exp (-r * u)) := by
      exact wnZR_geometric_tsum hK₀.le hα

/-- The real-valued coarse envelope has the same exponential tail. -/
theorem wnZR_tail (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R u : ℝ, 1 ≤ R → 0 ≤ u →
          P {ω | u < wnZR (d := d) R Q CZ H ω} ≤
            ENNReal.ofReal (K * Real.exp (-(Real.sqrt (2 * d) / 2) * u)) := by
  obtain ⟨CZ, hCZ, htail⟩ := wnZRext_tail hd hκ
  refine ⟨CZ, hCZ, ?_⟩
  intro Q hQ
  obtain ⟨K, hK, htail⟩ := htail Q hQ
  refine ⟨K, hK, ?_⟩
  intro Ω _ P W H hH R u hR hu
  have hsub : {ω | u < wnZR (d := d) R Q CZ H ω} ⊆
      {ω | ENNReal.ofReal u < wnZRext (d := d) R Q CZ H ω} := by
    intro ω hω
    by_contra hnot
    have hle : wnZRext (d := d) R Q CZ H ω ≤ ENNReal.ofReal u := le_of_not_gt hnot
    have hreal : wnZR (d := d) R Q CZ H ω ≤ u :=
      ENNReal.toReal_le_of_le_ofReal hu hle
    exact (not_lt_of_ge hreal) hω
  exact (measure_mono hsub).trans (htail hH R u hR hu)

/-- Almost-sure finiteness from a specified extended coarse tail. -/
theorem wnZRext_finite_ae_of_tail (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (CZ : ℝ) (_hCZ : 0 < CZ)
    (htail : ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R u : ℝ, 1 ≤ R → 0 ≤ u →
          P {ω | ENNReal.ofReal u < wnZRext (d := d) R Q CZ H ω} ≤
            ENNReal.ofReal (K * Real.exp (-(Real.sqrt (2 * d) / 2) * u))) :
    ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R : ℝ, 1 ≤ R →
          ∀ᵐ ω ∂P, wnZRext (d := d) R Q CZ H ω ≠ ⊤ := by
  intro Q hQ
  obtain ⟨K, hK, htail⟩ := htail Q hQ
  intro Ω _ P W H hH R hR
  letI : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  let E : Set Ω := {ω | wnZRext (d := d) R Q CZ H ω = ⊤}
  have hle (n : ℕ) : P.real E ≤ K * Real.exp (-(Real.sqrt (2 * d) / 2) * n) := by
    have hsub : E ⊆ {ω | ENNReal.ofReal (n : ℝ) < wnZRext (d := d) R Q CZ H ω} := by
      intro ω hω
      change wnZRext (d := d) R Q CZ H ω = ⊤ at hω
      simp [hω]
    have hb := (measure_mono hsub).trans
      (htail (P := P) (W := W) (H := H) hH R n hR (Nat.cast_nonneg n))
    have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hb
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  have hr : 0 < Real.sqrt (2 * d) / 2 := by
    have : (0 : ℝ) < (2 * d) := by positivity
    positivity
  have htend : Filter.Tendsto
      (fun n : ℕ => K * Real.exp (-(Real.sqrt (2 * d) / 2) * n))
      Filter.atTop (nhds 0) := by
    have hn : Filter.Tendsto (fun n : ℕ => Real.sqrt (2 * d) / 2 * (n : ℝ))
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hr tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hn).const_mul K
  have hzero : P.real E = 0 := by
    have hP : 0 ≤ P.real E := measureReal_nonneg
    have hP' : P.real E ≤ 0 := ge_of_tendsto' htend hle
    exact le_antisymm hP' hP
  have hnull : P E = 0 := (measureReal_eq_zero_iff (measure_ne_top P E)).1 hzero
  apply ae_iff.mpr
  simpa only [ne_eq, not_not, E] using hnull

/-- The extended supremum is finite almost surely, so the real envelope bounds the field there. -/
theorem wnZRext_finite_ae (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R : ℝ, 1 ≤ R →
          ∀ᵐ ω ∂P, wnZRext (d := d) R Q CZ H ω ≠ ⊤ := by
  obtain ⟨CZ,hCZ,htail⟩ := wnZRext_tail hd hκ
  exact ⟨CZ,hCZ,wnZRext_finite_ae_of_tail hd CZ hCZ htail⟩

end HigherDimLQGContinuity
