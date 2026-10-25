import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegCount




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory LQGMetric.Blueprint
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem s3_site_failure_tail
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (a : ℝ) (ha : 0 < a) :
    ∃ p c cReg : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 0 < cReg ∧ cReg < 1 ∧
      ∀ (C : Objects.CorrectedEvent.Constants), C.c_reg ≤ cReg → ∀ (k : ℕ) (w : ℂ),
        μ {g | ¬ 2 * ((Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
          (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) w)).card ≥
          Objects.CorrectedEvent.regK k} ≤
          ENNReal.ofReal (c * Real.exp (-a * Objects.CorrectedEvent.regK k)) := by
  obtain ⟨p, c, cReg, hp0, hp1, hc0, hcR0, hcR1, hLM⟩ :=
    regGood_iteration_tail μ hμ ξ Q D hD a ha
  refine ⟨p, c, cReg, hp0, hp1, hc0, hcR0, hcR1, ?_⟩
  intro C hC k w
  let K := Objects.CorrectedEvent.regK k
  let base := 4^(K+1) * Objects.CorrectedEvent.lam k * C.r
  have hb : 0 < base := by
    have hr := C.rPos
    dsimp [base, Objects.CorrectedEvent.lam]
    positivity
  have htail := hLM C hC w base hb K
  have hsub : {g | ¬ 2 * ((Finset.Icc 1 K).filter
        (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) w)).card ≥ K} ⊆
      {g | (countOcc (fun i =>
          {g | Objects.CorrectedEvent.regGood C (D g) (regRadius base i) w}) K g : ℝ) <
          (1/2 : ℝ) * K} := by
    intro g hg
    have hn : 2 * ((Finset.Icc 1 K).filter
        (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) w)).card < K :=
      Nat.lt_of_not_ge hg
    have hnr : (2 : ℝ) * (((Finset.Icc 1 K).filter
        (fun j => Objects.CorrectedEvent.regGood C (D g) (4^j * Objects.CorrectedEvent.lam k * C.r) w)).card : ℝ) < K := by
      exact_mod_cast hn
    have heq := regGood_count_eq C (D g) k w
    change (countOcc (fun i => {g | Objects.CorrectedEvent.regGood C g
      (regRadius base i) w}) K (D g) : ℝ) < (1/2 : ℝ) * K
    rw [heq]
    linarith
  exact (μ.mono hsub).trans htail

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
