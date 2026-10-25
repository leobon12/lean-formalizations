import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 



















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9

open LQGMetric (DistC TestC TestC0 pair0 cmTest0 gradEnergy IsWholePlaneGFF)

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

 
theorem hasGaussianLaw_pair0_cmTest0 (hh : IsWholePlaneGFF h P) (φ : TestC) :
    HasGaussianLaw (fun ω => pair0 (h ω) (cmTest0 φ)) P :=
  hh.gaussian.hasGaussianLaw_eval (cmTest0 φ)

theorem aemeasurable_pair0_cmTest0 (hh : IsWholePlaneGFF h P) (φ : TestC) :
    AEMeasurable (fun ω => pair0 (h ω) (cmTest0 φ)) P :=
  ((LQGMetric.measurable_evalDist (cmTest0 φ).1).comp hh.measurable).aemeasurable

 
theorem integral_pair0_cmTest0 (hh : IsWholePlaneGFF h P) (φ : TestC) :
    ∫ ω, pair0 (h ω) (cmTest0 φ) ∂P = 0 :=
  hh.centered (cmTest0 φ)

 
theorem variance_pair0_cmTest0 (hh : IsWholePlaneGFF h P) (φ : TestC) :
    Var[fun ω => pair0 (h ω) (cmTest0 φ); P] = gradEnergy φ := by
  rw [← covariance_self (aemeasurable_pair0_cmTest0 hh φ)]
  exact (hh.covariance_eq (cmTest0 φ) (cmTest0 φ)).trans (LQGMetric.logCov_cmTest_cmTest φ)

 
theorem hasLaw_pair0_cmTest0 (hh : IsWholePlaneGFF h P) (φ : TestC) :
    HasLaw (fun ω => pair0 (h ω) (cmTest0 φ)) (gaussianReal 0 (gradEnergy φ).toNNReal) P := by
  have hG := hasGaussianLaw_pair0_cmTest0 hh φ
  refine ⟨aemeasurable_pair0_cmTest0 hh φ, ?_⟩
  rw [hG.map_eq_gaussianReal, integral_pair0_cmTest0 hh φ, variance_pair0_cmTest0 hh φ]

 
theorem hasSubgaussianMGF_pair0_cmTest0 (hh : IsWholePlaneGFF h P) (φ : TestC) (c : ℝ≥0)
    (hc : gradEnergy φ ≤ c) :
    HasSubgaussianMGF (fun ω => pair0 (h ω) (cmTest0 φ)) c P := by
  have hL := hasLaw_pair0_cmTest0 hh φ
  have : IsProbabilityMeasure P := (hasGaussianLaw_pair0_cmTest0 hh φ).isProbabilityMeasure
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [← mgf_pos_iff, mgf_gaussianReal hL t]
    exact Real.exp_pos _
  · rw [mgf_gaussianReal hL t]
    apply Real.exp_le_exp.mpr
    have hv : ((gradEnergy φ).toNNReal : ℝ) ≤ c := by
      rw [Real.coe_toNNReal']
      exact max_le hc c.2
    have ht : 0 ≤ t ^ 2 := sq_nonneg t
    nlinarith

 

theorem measure_lt_abs_pair0_cmTest0_le (hh : IsWholePlaneGFF h P) (φ : TestC) (c : ℝ≥0)
    (hc : gradEnergy φ ≤ c) {A : ℝ} (hA : 0 ≤ A) :
    P {ω | A < |pair0 (h ω) (cmTest0 φ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-A ^ 2 / (2 * c))) := by
  have : IsProbabilityMeasure P := (hasGaussianLaw_pair0_cmTest0 hh φ).isProbabilityMeasure
  set X : Ω → ℝ := fun ω => pair0 (h ω) (cmTest0 φ) with hXdef
  have hS : HasSubgaussianMGF X c P := hasSubgaussianMGF_pair0_cmTest0 hh φ c hc
  have hSneg : HasSubgaussianMGF (fun ω => -X ω) c P := hS.neg
  have h1 : P.real {ω | A ≤ X ω} ≤ Real.exp (-A ^ 2 / (2 * c)) := hS.measure_ge_le hA
  have h2 : P.real {ω | A ≤ -X ω} ≤ Real.exp (-A ^ 2 / (2 * c)) := hSneg.measure_ge_le hA
  have hsub : {ω | A < |X ω|} ⊆ {ω | A ≤ X ω} ∪ {ω | A ≤ -X ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    rcases le_total 0 (X ω) with hx | hx
    · left
      simp only [mem_ofPred_eq]
      rw [abs_of_nonneg hx] at hω
      exact hω.le
    · right
      simp only [mem_ofPred_eq]
      rw [abs_of_nonpos hx] at hω
      exact hω.le
  have e1 : P {ω | A ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-A ^ 2 / (2 * c))) := by
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal h1
  have e2 : P {ω | A ≤ -X ω} ≤ ENNReal.ofReal (Real.exp (-A ^ 2 / (2 * c))) := by
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal h2
  calc P {ω | A < |X ω|} ≤ P ({ω | A ≤ X ω} ∪ {ω | A ≤ -X ω}) := measure_mono hsub
    _ ≤ P {ω | A ≤ X ω} + P {ω | A ≤ -X ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-A ^ 2 / (2 * c))) +
          ENNReal.ofReal (Real.exp (-A ^ 2 / (2 * c))) := add_le_add e1 e2
    _ = ENNReal.ofReal (2 * Real.exp (-A ^ 2 / (2 * c))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

end Gaussian

 

 
theorem measurableSet_S9 (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) :
    MeasurableSet {g : DistC | Objects.CorrectedEvent.S9 C T g} := by
  have hm : Measurable fun g : DistC => pair0 g (cmTest0 T.bump) :=
    LQGMetric.measurable_evalDist (cmTest0 T.bump).1
  exact measurableSet_le hm.abs measurable_const

 
theorem not_S9_iff (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (g : DistC) :
    ¬ Objects.CorrectedEvent.S9 C T g ↔ C.A_RN < |pair0 g (cmTest0 T.bump)| := by
  unfold Objects.CorrectedEvent.S9
  exact not_le

 


theorem s9_failure_le (μ : Measure DistC) (hμ : IsWholePlaneGFF (id : DistC → DistC) μ)
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (c : ℝ≥0) (hc : gradEnergy T.bump ≤ c) :
    μ {g | ¬ Objects.CorrectedEvent.S9 C T g} ≤ ENNReal.ofReal (2 * Real.exp (-C.A_RN ^ 2 / (2 * c))) := by
  have hset : {g : DistC | ¬ Objects.CorrectedEvent.S9 C T g} =
      {g : DistC | C.A_RN < |pair0 (id g) (cmTest0 T.bump)|} := by
    ext g
    exact not_S9_iff C T g
  rw [hset]
  exact measure_lt_abs_pair0_cmTest0_le hμ T.bump c hc C.rnPos.le

 

theorem two_exp_le_budget {c pbar A : ℝ} (hc : 0 < c) (hp0 : 0 < pbar) (hp1 : pbar < 1)
    (hA : Real.sqrt (2 * c * Real.log (20 / (1 - pbar))) ≤ A) :
    2 * Real.exp (-A ^ 2 / (2 * c)) ≤ (1 - pbar) / 10 := by
  have h1p : 0 < 1 - pbar := by linarith
  have hlog : 0 < Real.log (20 / (1 - pbar)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ h1p]
    linarith
  have hsq0 : 0 ≤ Real.sqrt (2 * c * Real.log (20 / (1 - pbar))) := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := hsq0.trans hA
  have hAsq : 2 * c * Real.log (20 / (1 - pbar)) ≤ A ^ 2 := by
    have := pow_le_pow_left₀ hsq0 hA 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have hexp : -A ^ 2 / (2 * c) ≤ -Real.log (20 / (1 - pbar)) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hle : Real.exp (-A ^ 2 / (2 * c)) ≤ (1 - pbar) / 20 := by
    calc Real.exp (-A ^ 2 / (2 * c)) ≤ Real.exp (-Real.log (20 / (1 - pbar))) :=
          Real.exp_le_exp.mpr hexp
      _ = (1 - pbar) / 20 := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  linarith

 





theorem exists_s9_budget (μ : Measure DistC)
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (pbar : Ioo (0 : ℝ) 1) (Emax : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Objects.CorrectedEvent.Constants, ∀ T : Objects.CorrectedEvent.TubeData,
      gradEnergy T.bump ≤ Emax → A ≤ C.A_RN →
        μ {g | ¬ Objects.CorrectedEvent.S9 C T g} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  set c : ℝ := max Emax 1 with hcdef
  have hc1 : 1 ≤ c := le_max_right _ _
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  set A₀ : ℝ := Real.sqrt (2 * c * Real.log (20 / (1 - (pbar : ℝ)))) with hA₀def
  refine ⟨A₀ + 1, by positivity, ?_⟩
  intro C T hE hA
  have hcE : gradEnergy T.bump ≤ ((c.toNNReal : ℝ≥0) : ℝ) := by
    rw [Real.coe_toNNReal _ hc0.le]
    exact hE.trans (le_max_left _ _)
  have hfail := s9_failure_le μ hμ.1 C T c.toNNReal hcE
  rw [Real.coe_toNNReal _ hc0.le] at hfail
  refine hfail.trans (ENNReal.ofReal_le_ofReal ?_)
  exact two_exp_le_budget hc0 pbar.2.1 pbar.2.2 (by linarith)


end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9
