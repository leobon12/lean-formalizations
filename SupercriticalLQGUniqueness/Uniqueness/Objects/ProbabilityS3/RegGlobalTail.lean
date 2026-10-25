import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegTailNumeric




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory LQGMetric.Blueprint
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem s3_failure_geometric
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ p c cReg : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 0 < cReg ∧ cReg < 1 ∧
      ∀ (C : Objects.CorrectedEvent.Constants), C.c_reg ≤ cReg → 48 ≤ C.k0 →
        μ {g | ¬ Objects.CorrectedEvent.S3 C (D g)} ≤
          (1162 : ℝ≥0∞) * (2 : ℝ≥0∞)^144 * ENNReal.ofReal c *
            ((1/16 : ℝ≥0∞)^C.k0) := by
  have ha : 0 < 72 * Real.log 2 := by
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨p, c, cReg, hp0, hp1, hc0, hcR0, hcR1, hgrid⟩ :=
    s3_grid_failure_tail μ hμ ξ Q D hD (72 * Real.log 2) ha
  refine ⟨p, c, cReg, hp0, hp1, hc0, hcR0, hcR1, ?_⟩
  intro C hC hk0
  let bad : ℕ → Set LQGMetric.DistC := fun k =>
    {g | ∃ z ∈ Objects.CorrectedEvent.regSites C k,
      ¬ 2 * ((Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
        (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) z)).card ≥
        Objects.CorrectedEvent.regK k}
  have hset : {g | ¬ Objects.CorrectedEvent.S3 C (D g)} = ⋃ n : ℕ, bad (n+C.k0) := by
    ext g
    constructor
    · intro hg
      change ¬ ∀ k : ℕ, C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k,
        2 * ((Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
          (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) z)).card ≥
          Objects.CorrectedEvent.regK k at hg
      push Not at hg
      obtain ⟨k, hk, z, hz, hbad⟩ := hg
      refine Set.mem_iUnion.mpr ⟨k-C.k0, ?_⟩
      change ∃ z ∈ Objects.CorrectedEvent.regSites C ((k-C.k0)+C.k0), ¬ _
      simpa [Nat.sub_add_cancel hk] using ⟨z, hz, hbad⟩
    · intro hg
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
      change ∃ z ∈ Objects.CorrectedEvent.regSites C (n+C.k0), ¬ _ at hn
      obtain ⟨z, hz, hbad⟩ := hn
      change ¬ ∀ k : ℕ, C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k,
        2 * ((Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
          (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) z)).card ≥
          Objects.CorrectedEvent.regK k
      intro hall
      exact hbad (hall (n+C.k0) (by omega) z hz)
  rw [hset]
  calc
    μ (⋃ n : ℕ, bad (n+C.k0)) ≤ ∑' n : ℕ, μ (bad (n+C.k0)) :=
      measure_iUnion_le _
    _ ≤ ∑' n : ℕ, (1089 : ℝ≥0∞) * (2 : ℝ≥0∞)^144 *
        ENNReal.ofReal c * ((1/16 : ℝ≥0∞)^(n+C.k0)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hk : 48 ≤ n+C.k0 := by omega
      exact (hgrid C hC (n+C.k0)).trans (s3_tail_numeric c hc0.le (n+C.k0) hk)
    _ ≤ _ := Objects.ProbabilityS1S2.lattice_geometric_budget (ENNReal.ofReal c) C.k0

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
