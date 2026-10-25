import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegSitesFinite
import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.GridCount




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory LQGMetric.Blueprint
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem s3_grid_failure_tail
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (a : ℝ) (ha : 0 < a) :
    ∃ p c cReg : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 0 < cReg ∧ cReg < 1 ∧
      ∀ (C : Objects.CorrectedEvent.Constants), C.c_reg ≤ cReg → ∀ k : ℕ,
        μ {g | ∃ z ∈ Objects.CorrectedEvent.regSites C k,
          ¬ 2 * ((Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
            (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) z)).card ≥
            Objects.CorrectedEvent.regK k} ≤
          (1089 * (4 : ℝ≥0∞)^k) *
            ENNReal.ofReal (c * Real.exp (-a * Objects.CorrectedEvent.regK k)) := by
  obtain ⟨p, c, cReg, hp0, hp1, hc0, hcR0, hcR1, hsite⟩ :=
    s3_site_failure_tail μ hμ ξ Q D hD a ha
  refine ⟨p, c, cReg, hp0, hp1, hc0, hcR0, hcR1, ?_⟩
  intro C hC k
  let sites := (regSites_finite C k).toFinset
  let bad : ℂ → Set LQGMetric.DistC := fun z =>
    {g | ¬ 2 * ((Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
      (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) z)).card ≥
      Objects.CorrectedEvent.regK k}
  let ε : ℝ≥0∞ := ENNReal.ofReal (c * Real.exp (-a * Objects.CorrectedEvent.regK k))
  have hset : {g | ∃ z ∈ Objects.CorrectedEvent.regSites C k, g ∈ bad z} = ⋃ z ∈ sites, bad z := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    simp only [sites, Set.Finite.mem_toFinset]
    tauto
  have hcard : (sites.card : ℝ≥0∞) ≤ 1089 * (4 : ℝ≥0∞)^k := by
    have hn := Objects.ClauseMeasurability.regSites_ncard_le C k
    rw [Set.ncard_eq_toFinset_card _ (regSites_finite C k)] at hn
    dsimp [sites]
    exact_mod_cast hn
  change μ {g | ∃ z ∈ Objects.CorrectedEvent.regSites C k, g ∈ bad z} ≤
    (1089 * (4 : ℝ≥0∞)^k) * ε
  rw [hset]
  calc
    μ (⋃ z ∈ sites, bad z) ≤ ∑ z ∈ sites, μ (bad z) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ sites, ε := Finset.sum_le_sum (fun z _ => hsite C hC k z)
    _ = (sites.card : ℝ≥0∞) * ε := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1089 * (4 : ℝ≥0∞)^k) * ε := by gcongr

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
