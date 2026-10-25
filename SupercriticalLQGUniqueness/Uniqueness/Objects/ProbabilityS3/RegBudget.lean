import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegGlobalTail




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem exists_s3_budget
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (pbar : Ioo (0 : ℝ) 1) :
    ∃ cReg : ℝ, 0 < cReg ∧ cReg < 1 ∧ ∃ k0 : ℕ, 48 ≤ k0 ∧
      ∀ (C : Objects.CorrectedEvent.Constants), C.c_reg ≤ cReg → k0 ≤ C.k0 →
        μ {g | ¬ Objects.CorrectedEvent.S3 C (D g)} ≤
          ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨p, c, cReg, hp0, hp1, hc0, hcR0, hcR1, hgeo⟩ :=
    s3_failure_geometric μ hμ ξ Q D hD
  let coeff : ℝ≥0∞ := 1162 * 2^144 * ENNReal.ofReal c
  let q : ℝ≥0∞ := 1/16
  let δ : ℝ≥0∞ := ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
  have hδ : 0 < δ := by
    dsimp [δ]
    apply ENNReal.ofReal_pos.mpr
    have hp : (pbar : ℝ) < 1 := pbar.property.2
    linarith
  have hq : q < 1 := by dsimp [q]; norm_num
  have hcoeff : coeff ≠ ⊤ := by
    dsimp [coeff]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun k : ℕ => coeff * q^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) (Or.inr hcoeff)
  have hev : ∀ᶠ k : ℕ in atTop, 48 ≤ k ∧ coeff * q^k < δ := by
    filter_upwards [eventually_ge_atTop 48, hlim.eventually (eventually_lt_nhds hδ)]
      with k hk hlt
    exact ⟨hk, hlt⟩
  obtain ⟨k0, hk0, hsmall⟩ := hev.exists
  refine ⟨cReg, hcR0, hcR1, k0, hk0, ?_⟩
  intro C hC hK
  have hkC : 48 ≤ C.k0 := hk0.trans hK
  have hpow : q^C.k0 ≤ q^k0 :=
    pow_le_pow_of_le_one (by simp) hq.le hK
  calc
    μ {g | ¬ Objects.CorrectedEvent.S3 C (D g)} ≤ coeff * q^C.k0 := hgeo C hC hkC
    _ ≤ coeff * q^k0 := by gcongr
    _ ≤ δ := hsmall.le

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
