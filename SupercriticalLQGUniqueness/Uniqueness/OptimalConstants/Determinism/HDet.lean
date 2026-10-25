import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FirstExit.FirstExit
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.Projection
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.OrderTests.Optimal
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.ClosedEventToolkit
import LQGMetric.Meas.UM
import LQGMetric.Papers.GM.S3.DeterministicCore
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.EBL
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations




 
set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism

open LQGMetric (DistC)

#check Toolkit.MovingEndpoints.openBallPathInf_joint_borel
#check Toolkit.MovingEndpoints.boundaryBallInf_joint_borel
#check LQGMetric.UMeasurableSet.setOf_exists
#check OptimalConstants.FirstExit.LocalWitness
#check Toolkit.InternalMetrics.aeEventIn_closed_internal_family

 
theorem localWitnessCode_iff (D E : LSCMetric) (a : ℝ≥0∞)
    (z : ℂ) (r : ℝ) (hr : 0 < r) :
    (∃ u v : ℂ, Toolkit.MovingEndpoints.LocalWitnessRelation a z r ((D, E), (u, v))) ↔
      OptimalConstants.FirstExit.LocalWitness D E a z r hr := by
  constructor
  · rintro ⟨u, v, hu, hv, hne, hDpos, hDb, hEpos, hEb, hRatio⟩
    have huW : u ∈ Metric.ball z r :=
      Metric.ball_subset_ball (by linarith only [hr]) hu
    have hvW : v ∈ Metric.ball z r :=
      Metric.ball_subset_ball (by linarith only [hr]) hv
    have huK : u ∈ Metric.closedBall z r := Metric.ball_subset_closedBall huW
    have hcostD : Toolkit.MovingEndpoints.openBallPathInf D z r u v =
        D.internal (Metric.ball z r) (⟨u, huW⟩, ⟨v, hvW⟩) := rfl
    have hcostE : Toolkit.MovingEndpoints.openBallPathInf E z r u v =
        E.internal (Metric.ball z r) (⟨u, huW⟩, ⟨v, hvW⟩) := rfl
    have hbD : Toolkit.MovingEndpoints.boundaryBallInf D z r u =
        OptimalConstants.FirstExit.boundaryInternal D z r u huK :=
      Toolkit.MovingEndpoints.boundaryBallInf_eq_internal D z r huK
    have hbE : Toolkit.MovingEndpoints.boundaryBallInf E z r u =
        OptimalConstants.FirstExit.boundaryInternal E z r u huK :=
      Toolkit.MovingEndpoints.boundaryBallInf_eq_internal E z r huK
    refine ⟨u, v, hu, hv, hne, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hcostD] using hDpos
    · simpa only [hcostD, hbD] using hDb
    · simpa only [hcostE] using hEpos
    · simpa only [hcostE, hbE] using hEb
    · simpa only [hcostD, hcostE] using hRatio

  · rintro ⟨u, v, hu, hv, hne, hDpos, hDb, hEpos, hEb, hRatio⟩
    have huW : u ∈ Metric.ball z r :=
      Metric.ball_subset_ball (by linarith only [hr]) hu
    have hvW : v ∈ Metric.ball z r :=
      Metric.ball_subset_ball (by linarith only [hr]) hv
    have huK : u ∈ Metric.closedBall z r := Metric.ball_subset_closedBall huW
    have hcostD : Toolkit.MovingEndpoints.openBallPathInf D z r u v =
        D.internal (Metric.ball z r) (⟨u, huW⟩, ⟨v, hvW⟩) := rfl
    have hcostE : Toolkit.MovingEndpoints.openBallPathInf E z r u v =
        E.internal (Metric.ball z r) (⟨u, huW⟩, ⟨v, hvW⟩) := rfl
    have hbD : Toolkit.MovingEndpoints.boundaryBallInf D z r u =
        OptimalConstants.FirstExit.boundaryInternal D z r u huK :=
      Toolkit.MovingEndpoints.boundaryBallInf_eq_internal D z r huK
    have hbE : Toolkit.MovingEndpoints.boundaryBallInf E z r u =
        OptimalConstants.FirstExit.boundaryInternal E z r u huK :=
      Toolkit.MovingEndpoints.boundaryBallInf_eq_internal E z r huK
    refine ⟨u, v, hu, hv, hne, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hcostD] using hDpos
    · simpa only [hcostD, hbD] using hDb
    · simpa only [hcostE] using hEpos
    · simpa only [hcostE, hbE] using hEb
    · simpa only [hcostD, hcostE] using hRatio

 
theorem localWitnessEvent_um (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E)
    (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r) :
    LQGMetric.UMeasurableSet
      {g : DistC | OptimalConstants.FirstExit.LocalWitness (D g) (E g) a z r hr} := by
  have h := Toolkit.MovingEndpoints.LocalWitnessEvent_um D E hD hE a z r
  convert h using 1
  ext g
  exact (localWitnessCode_iff (D g) (E g) a z r hr).symm


 

theorem localWitness_congr_internal (D₁ D₂ E₁ E₂ : LSCMetric)
    (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hD : D₁.internal (Metric.closedBall z r) =
      D₂.internal (Metric.closedBall z r))
    (hE : E₁.internal (Metric.closedBall z r) =
      E₂.internal (Metric.closedBall z r)) :
    OptimalConstants.FirstExit.LocalWitness D₁ E₁ a z r hr ↔
      OptimalConstants.FirstExit.LocalWitness D₂ E₂ a z r hr := by
  have hDopen : D₁.internal (Metric.ball z r) =
      D₂.internal (Metric.ball z r) :=
    Toolkit.InternalMetrics.internal_eq_of_internal_eq D₁ D₂
      Metric.ball_subset_closedBall hD
  have hEopen : E₁.internal (Metric.ball z r) =
      E₂.internal (Metric.ball z r) :=
    Toolkit.InternalMetrics.internal_eq_of_internal_eq E₁ E₂
      Metric.ball_subset_closedBall hE
  simp only [OptimalConstants.FirstExit.LocalWitness, OptimalConstants.FirstExit.boundaryInternal,
    hDopen, hEopen, hD, hE]


 

theorem aeEventIn_localWitness
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (U : TopologicalSpace.Opens ℂ)
    (hKU : Metric.closedBall z r ⊆ (U : Set ℂ)) :
    LQGMetric.Blueprint.AEEventIn μ (LQGMetric.Blueprint.fieldSigma id U)
      {g : DistC | OptimalConstants.FirstExit.LocalWitness (D g) (E g) a z r hr} := by
  let K : Set ℂ := Metric.closedBall z r
  let F : Fin 2 → DistC → LSCMetric := fun i => if i = 0 then D else E
  let Φ : (Fin 2 → (K × K → ℝ≥0∞)) → Prop :=
    fun ρ => ∃ d e : LSCMetric,
      d.internal K = ρ 0 ∧ e.internal K = ρ 1 ∧
      OptimalConstants.FirstExit.LocalWitness d e a z r hr
  have hF : ∀ i, IsWeakLQGMetric ξ Q (F i) := by
    intro i
    fin_cases i
    · simpa [F] using hD
    · simpa [F] using hE
  have hEq : {g : DistC | Φ (fun i => (F i g).internal K)} =
      {g : DistC | OptimalConstants.FirstExit.LocalWitness (D g) (E g) a z r hr} := by
    ext g
    constructor
    · rintro ⟨d, e, hd, he, hw⟩
      have hd' : d.internal K = (D g).internal K := by simpa [F] using hd
      have he' : e.internal K = (E g).internal K := by
        simpa [F] using he
      exact (localWitness_congr_internal d (D g) e (E g) a z r hr hd' he').1 hw
    · intro hw
      refine ⟨D g, E g, ?_, ?_, hw⟩
      · rfl
      · rfl
  have hB : NullMeasurableSet
      {g : DistC | Φ (fun i => (F i g).internal K)} μ := by
    rw [hEq]
    exact (localWitnessEvent_um D E hD.measurable hE.measurable a z r hr).nullMeasurableSet μ
  have hloc := Toolkit.InternalMetrics.aeEventIn_internal_subset μ hμ ξ Q F hF K U hKU Φ hB
  rw [hEq] at hloc
  exact hloc


 

theorem aeEventIn_localWitness_addConst
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (h : Ω → DistC) (hh : LQGMetric.IsWholePlaneGFF h P)
    (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (U : TopologicalSpace.Opens ℂ)
    (hKU : Metric.closedBall z r ⊆ (U : Set ℂ))
    (c : Ω → ℝ) (hc : Measurable c) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (c ω)) U)
      {ω : Ω | OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω)) a z r hr} := by
  let g : Ω → DistC := fun ω => LQGMetric.addConst (h ω) (c ω)
  have hg : LQGMetric.IsWholePlaneGFF g P := hh.addConst hc
  letI : IsProbabilityMeasure (P.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.measurable.aemeasurable).2 inferInstance
  have hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) (P.map g) :=
    LQGMetric.GM.detGFFPlusCont (LQGMetric.GM.isWholePlaneGFF_id_map hg)
  obtain ⟨F, hFm, hFa⟩ :=
    aeEventIn_localWitness (P.map g) hμ ξ Q D E hD hE a z r hr U hKU
  have hFgm : MeasurableSet[LQGMetric.Blueprint.fieldSigma g U] (g ⁻¹' F) := by
    unfold LQGMetric.Blueprint.fieldSigma at hFm ⊢
    rcases hFm with ⟨S, hS, hFS⟩
    exact ⟨S, hS, by rw [← hFS]; rfl⟩
  have hFaP : ∀ᵐ ω ∂P,
      (OptimalConstants.FirstExit.LocalWitness (D (g ω)) (E (g ω)) a z r hr) = (g ω ∈ F) :=
    ae_of_ae_map hg.measurable.aemeasurable hFa
  have hShift := OptimalConstants.FirstExit.ae_localWitness_addConst_iff hD hE P h
    (LQGMetric.GM.detGFFPlusCont hh) c a z r hr
  refine ⟨g ⁻¹' F, hFgm, ?_⟩
  filter_upwards [hShift, hFaP] with ω hs he
  exact propext (hs.symm.trans (Iff.of_eq he))


 

theorem positiveRatio_covered_by_localWitness
    (D E : LSCMetric)
    (hD : BiLipschitz.Barrier.Barrier D) (hE : BiLipschitz.Barrier.Barrier E)
    (hLD : D.IsLengthSpace) (hLE : E.IsLengthSpace)
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hDE : ∀ u v : ℂ, E (u, v) ≤ C * D (u, v))
    (a : ℝ≥0∞) (ha : a < OptimalConstants.Ratios.upperOptimal D E) :
    ∃ n : ℕ, OptimalConstants.FirstExit.LocalWitness D E a 0 ((n : ℝ) + 1) (by positivity) := by
  unfold OptimalConstants.Ratios.upperOptimal at ha
  obtain ⟨u, hu⟩ := lt_iSup_iff.mp ha
  obtain ⟨w, hw⟩ := lt_iSup_iff.mp hu
  obtain ⟨hp, hratio⟩ := lt_iSup_iff.mp hw
  have hDu : D (u, w) < ∞ := hp.2.2.2.2
  have hEu : E (u, w) < ∞ :=
    (hDE u w).trans_lt (ENNReal.mul_lt_top hC hDu)
  obtain ⟨mD, hmD⟩ := ENNReal.exists_nat_gt hDu.ne
  obtain ⟨mE, hmE⟩ := ENNReal.exists_nat_gt hEu.ne
  obtain ⟨RD, hRD⟩ := BiLipschitz.Barrier.lt_dist_of_barrier D hD hLD u mD
  obtain ⟨RE, hRE⟩ := BiLipschitz.Barrier.lt_dist_of_barrier E hE hLE u mE
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max RD (max RE (max (2 * ‖u‖) (2 * ‖w‖))))
  let r : ℝ := (n : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hRDb : RD ≤ r := by
    have hle : RD ≤ max RD (max RE (max (2 * ‖u‖) (2 * ‖w‖))) := le_max_left _ _
    dsimp [r]
    linarith only [hn, hle]
  have hREb : RE ≤ r := by
    have hle : RE ≤ max RD (max RE (max (2 * ‖u‖) (2 * ‖w‖))) :=
      (le_max_left _ _).trans (le_max_right _ _)
    dsimp [r]
    linarith only [hn, hle]
  have huHalf : u ∈ Metric.ball 0 (r / 2) := by
    rw [Metric.mem_ball, dist_zero_right]
    have hle : 2 * ‖u‖ ≤ max RD (max RE (max (2 * ‖u‖) (2 * ‖w‖))) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    dsimp [r]
    linarith only [hn, hle]
  have hwHalf : w ∈ Metric.ball 0 (r / 2) := by
    rw [Metric.mem_ball, dist_zero_right]
    have hle : 2 * ‖w‖ ≤ max RD (max RE (max (2 * ‖u‖) (2 * ‖w‖))) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    dsimp [r]
    linarith only [hn, hle]
  have huW : u ∈ Metric.ball 0 r :=
    Metric.ball_subset_ball (by linarith only [hr]) huHalf
  have hwW : w ∈ Metric.ball 0 r :=
    Metric.ball_subset_ball (by linarith only [hr]) hwHalf
  have hBoundD : D (u, w) < OptimalConstants.FirstExit.boundaryDist D 0 r u := by
    have hlow : (mD : ℝ≥0∞) ≤ OptimalConstants.FirstExit.boundaryDist D 0 r u := by
      unfold OptimalConstants.FirstExit.boundaryDist
      refine le_iInf fun y => le_iInf fun hy => ?_
      have hyNorm : ‖y‖ = r := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hy
      exact (hRD y (hyNorm ▸ hRDb)).le
    exact hmD.trans_le hlow
  have hBoundE : E (u, w) < OptimalConstants.FirstExit.boundaryDist E 0 r u := by
    have hlow : (mE : ℝ≥0∞) ≤ OptimalConstants.FirstExit.boundaryDist E 0 r u := by
      unfold OptimalConstants.FirstExit.boundaryDist
      refine le_iInf fun y => le_iInf fun hy => ?_
      have hyNorm : ‖y‖ = r := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hy
      exact (hRE y (hyNorm ▸ hREb)).le
    exact hmE.trans_le hlow
  have hIntD := OptimalConstants.FirstExit.ambient_eq_internal_of_escape_of_barrier
    D hD hLD huW hwW hBoundD
  have hIntE := OptimalConstants.FirstExit.ambient_eq_internal_of_escape_of_barrier
    E hE hLE huW hwW hBoundE
  have hbD := OptimalConstants.FirstExit.boundaryDist_eq_internalClosedBall_of_barrier D hD hLD huW
  have hbE := OptimalConstants.FirstExit.boundaryDist_eq_internalClosedBall_of_barrier E hE hLE huW
  have hRatioMul : a * D (u, w) < E (u, w) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hp.2.2.2.1.ne') (Or.inl hDu.ne)).1 hratio
  refine ⟨n, u, w, huHalf, hwHalf, hp.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hIntD]
    exact hp.2.2.2.1
  · rw [← hIntD, ← hbD]
    exact hBoundD
  · rw [← hIntE]
    exact bot_lt_of_lt hRatioMul
  · rw [← hIntE, ← hbE]
    exact hBoundE
  · rw [← hIntD, ← hIntE]
    exact hRatioMul


 


theorem ae_positiveRatio_covered
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (a : ℝ≥0∞) :
    ∀ᵐ ω ∂P, a < OptimalConstants.Ratios.upperOptimal (D (h ω)) (E (h ω)) →
      ∃ n : ℕ, OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω))
        a 0 ((n : ℝ) + 1) (by positivity) := by
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D E hD hE
  have hplus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hh.1
  filter_upwards [BiLipschitz.Barrier.ae_barrier hD hQ P h hh,
    BiLipschitz.Barrier.ae_barrier hE hQ P h hh,
    hD.length P h hplus, hE.length P h hplus,
    hEBL P h hplus] with ω hBD hBE hLD hLE hB ha
  exact positiveRatio_covered_by_localWitness
    (D (h ω)) (E (h ω)) hBD hBE hLD hLE
    (ENNReal.ofReal K) ENNReal.ofReal_lt_top (fun u v => (hB u v).1) a ha


 

theorem exists_positive_localWitness_radius
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (a : ℝ≥0∞)
    (hpos : 0 < P {ω : Ω | a < OptimalConstants.Ratios.upperOptimal (D (h ω)) (E (h ω))}) :
    ∃ n : ℕ, 0 < P {ω : Ω | OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω))
      a 0 ((n : ℝ) + 1) (by positivity)} := by
  let G : Set Ω := {ω | a < OptimalConstants.Ratios.upperOptimal (D (h ω)) (E (h ω))}
  let E₀ : ℕ → Set Ω := fun n =>
    {ω | OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω))
      a 0 ((n : ℝ) + 1) (by positivity)}
  have hcov : ∀ᵐ ω ∂P, ω ∈ G → ∃ n, ω ∈ E₀ n :=
    ae_positiveRatio_covered ξ Q hQ D E hD hE P h hh a
  by_contra hn
  have hzero : ∀ n, P (E₀ n) = 0 := by
    intro n
    have hnot : ¬ 0 < P (E₀ n) := (not_exists.mp hn) n
    exact le_antisymm (le_of_not_gt hnot) bot_le
  have hnone : ∀ᵐ ω ∂P, ∀ n, ω ∉ E₀ n := by
    apply ae_all_iff.mpr
    intro n
    exact measure_eq_zero_iff_ae_notMem.mp (hzero n)
  have hGzero : P G = 0 := measure_eq_zero_iff_ae_notMem.mpr (by
    filter_upwards [hcov, hnone] with ω hc hn hG
    obtain ⟨n, hEn⟩ := hc hG
    exact hn n hEn)
  exact (ne_of_gt hpos) (by simpa only [G] using hGzero)


private theorem mem_ball_sub_iff (x z : ℂ) (r : ℝ) :
    x - z ∈ Metric.ball 0 r ↔ x ∈ Metric.ball z r := by
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero]

private theorem mem_closedBall_sub_iff (x z : ℂ) (r : ℝ) :
    x - z ∈ Metric.closedBall 0 r ↔ x ∈ Metric.closedBall z r := by
  simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]

private theorem mem_sphere_sub_iff (x z : ℂ) (r : ℝ) :
    x - z ∈ Metric.sphere 0 r ↔ x ∈ Metric.sphere z r := by
  simp only [Metric.mem_sphere, dist_eq_norm, sub_zero]

private theorem image_sub_ball (z : ℂ) (r : ℝ) :
    (fun w : ℂ => w - z) '' Metric.ball z r = Metric.ball 0 r := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_ball_sub_iff w z r).2 hw
  · intro hx
    refine ⟨x + z, ?_, by simp only [add_sub_cancel_right]⟩
    exact (mem_ball_sub_iff (x + z) z r).1 (by simpa only [add_sub_cancel_right] using hx)

private theorem image_sub_closedBall (z : ℂ) (r : ℝ) :
    (fun w : ℂ => w - z) '' Metric.closedBall z r = Metric.closedBall 0 r := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_closedBall_sub_iff w z r).2 hw
  · intro hx
    refine ⟨x + z, ?_, by simp only [add_sub_cancel_right]⟩
    exact (mem_closedBall_sub_iff (x + z) z r).1
      (by simpa only [add_sub_cancel_right] using hx)

private theorem internal_translate_ball (D E : LSCMetric) (z : ℂ) (r : ℝ)
    (h : ∀ x y : ℂ, E (x - z, y - z) = D (x, y))
    {x y : ℂ} (hx : x ∈ Metric.ball z r) (hy : y ∈ Metric.ball z r) :
    E.internal (Metric.ball 0 r)
      (⟨x - z, (mem_ball_sub_iff x z r).2 hx⟩,
       ⟨y - z, (mem_ball_sub_iff y z r).2 hy⟩) =
      D.internal (Metric.ball z r) (⟨x, hx⟩, ⟨y, hy⟩) := by
  have hscale : ∀ x y : ℂ, E (x - z, y - z) =
      (1 : ℝ≥0∞) * D (x, y) := by simpa only [one_mul] using h
  have hi := OptimalConstants.FirstExit.internal_translate_scale
    (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) z hscale
    (Metric.ball z r) ⟨x, hx⟩ ⟨y, hy⟩
  unfold LSCMetric.internal at hi ⊢
  simpa only [image_sub_ball, one_mul] using hi

private theorem internal_translate_closedBall (D E : LSCMetric) (z : ℂ) (r : ℝ)
    (h : ∀ x y : ℂ, E (x - z, y - z) = D (x, y))
    {x y : ℂ} (hx : x ∈ Metric.closedBall z r)
    (hy : y ∈ Metric.closedBall z r) :
    E.internal (Metric.closedBall 0 r)
      (⟨x - z, (mem_closedBall_sub_iff x z r).2 hx⟩,
       ⟨y - z, (mem_closedBall_sub_iff y z r).2 hy⟩) =
      D.internal (Metric.closedBall z r) (⟨x, hx⟩, ⟨y, hy⟩) := by
  have hscale : ∀ x y : ℂ, E (x - z, y - z) =
      (1 : ℝ≥0∞) * D (x, y) := by simpa only [one_mul] using h
  have hi := OptimalConstants.FirstExit.internal_translate_scale
    (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) z hscale
    (Metric.closedBall z r) ⟨x, hx⟩ ⟨y, hy⟩
  unfold LSCMetric.internal at hi ⊢
  simpa only [image_sub_closedBall, one_mul] using hi

private theorem boundaryInternal_translate (D E : LSCMetric) (z : ℂ) (r : ℝ)
    (h : ∀ x y : ℂ, E (x - z, y - z) = D (x, y))
    {u : ℂ} (hu : u ∈ Metric.closedBall z r) :
    OptimalConstants.FirstExit.boundaryInternal E 0 r (u - z) ((mem_closedBall_sub_iff u z r).2 hu) =
      OptimalConstants.FirstExit.boundaryInternal D z r u hu := by
  unfold OptimalConstants.FirstExit.boundaryInternal
  apply le_antisymm
  · refine le_iInf fun y => le_iInf fun hy => ?_
    have hy' : y - z ∈ Metric.sphere 0 r := (mem_sphere_sub_iff y z r).2 hy
    have hyK : y ∈ Metric.closedBall z r := Metric.sphere_subset_closedBall hy
    calc
      (⨅ y' ∈ Metric.sphere 0 r,
        E.internal (Metric.closedBall 0 r)
          (⟨u - z, (mem_closedBall_sub_iff u z r).2 hu⟩,
           ⟨y', Metric.sphere_subset_closedBall ‹y' ∈ Metric.sphere 0 r›⟩))
        ≤ E.internal (Metric.closedBall 0 r)
          (⟨u - z, (mem_closedBall_sub_iff u z r).2 hu⟩,
           ⟨y - z, Metric.sphere_subset_closedBall hy'⟩) := iInf₂_le _ hy'
      _ = D.internal (Metric.closedBall z r) (⟨u, hu⟩, ⟨y, hyK⟩) :=
        internal_translate_closedBall D E z r h hu hyK
  · refine le_iInf fun y => le_iInf fun hy => ?_
    have hy' : y + z ∈ Metric.sphere z r := by
      exact (mem_sphere_sub_iff (y + z) z r).1
        (by simpa only [add_sub_cancel_right] using hy)
    have hyK : y + z ∈ Metric.closedBall z r := Metric.sphere_subset_closedBall hy'
    have hcost := internal_translate_closedBall D E z r h hu hyK
    have hcost' : E.internal (Metric.closedBall 0 r)
        (⟨u - z, (mem_closedBall_sub_iff u z r).2 hu⟩,
         ⟨y, Metric.sphere_subset_closedBall hy⟩) =
        D.internal (Metric.closedBall z r) (⟨u, hu⟩, ⟨y + z, hyK⟩) := by
      simpa only [add_sub_cancel_right] using hcost
    calc
      (⨅ y' ∈ Metric.sphere z r,
        D.internal (Metric.closedBall z r)
          (⟨u, hu⟩,
           ⟨y', Metric.sphere_subset_closedBall ‹y' ∈ Metric.sphere z r›⟩))
        ≤ D.internal (Metric.closedBall z r) (⟨u, hu⟩, ⟨y + z, hyK⟩) :=
          iInf₂_le _ hy'
      _ = E.internal (Metric.closedBall 0 r)
          (⟨u - z, (mem_closedBall_sub_iff u z r).2 hu⟩,
           ⟨y, Metric.sphere_subset_closedBall hy⟩) := hcost'.symm

 
theorem localWitness_translate_iff
    (D E D' E' : LSCMetric) (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hD : ∀ x y : ℂ, D' (x - z, y - z) = D (x, y))
    (hE : ∀ x y : ℂ, E' (x - z, y - z) = E (x, y)) :
    OptimalConstants.FirstExit.LocalWitness D' E' a 0 r hr ↔ OptimalConstants.FirstExit.LocalWitness D E a z r hr := by
  constructor
  · rintro ⟨u₀, v₀, hu₀, hv₀, hne₀, hDpos₀, hDb₀, hEpos₀, hEb₀, hRatio₀⟩
    let u : ℂ := u₀ + z
    let v : ℂ := v₀ + z
    have hu : u ∈ Metric.ball z (r / 2) :=
      (mem_ball_sub_iff u z (r / 2)).1 (by simpa only [u, add_sub_cancel_right] using hu₀)
    have hv : v ∈ Metric.ball z (r / 2) :=
      (mem_ball_sub_iff v z (r / 2)).1 (by simpa only [v, add_sub_cancel_right] using hv₀)
    have huW : u ∈ Metric.ball z r :=
      Metric.ball_subset_ball (by linarith only [hr]) hu
    have hvW : v ∈ Metric.ball z r :=
      Metric.ball_subset_ball (by linarith only [hr]) hv
    have huK : u ∈ Metric.closedBall z r := Metric.ball_subset_closedBall huW
    have hDi := internal_translate_ball D D' z r hD huW hvW
    have hEi := internal_translate_ball E E' z r hE huW hvW
    have hDb := boundaryInternal_translate D D' z r hD huK
    have hEb := boundaryInternal_translate E E' z r hE huK
    refine ⟨u, v, hu, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro he
      apply hne₀
      have he' := congrArg (fun x : ℂ => x - z) he
      simpa only [u, v, add_sub_cancel_right] using he'
    · rw [← hDi]
      simpa only [u, v, add_sub_cancel_right] using hDpos₀
    · rw [← hDi, ← hDb]
      simpa only [u, v, add_sub_cancel_right] using hDb₀
    · rw [← hEi]
      simpa only [u, v, add_sub_cancel_right] using hEpos₀
    · rw [← hEi, ← hEb]
      simpa only [u, v, add_sub_cancel_right] using hEb₀
    · rw [← hDi, ← hEi]
      simpa only [u, v, add_sub_cancel_right] using hRatio₀
  · rintro ⟨u, v, hu, hv, hne, hDpos, hDb, hEpos, hEb, hRatio⟩
    have hu₀ : u - z ∈ Metric.ball 0 (r / 2) :=
      (mem_ball_sub_iff u z (r / 2)).2 hu
    have hv₀ : v - z ∈ Metric.ball 0 (r / 2) :=
      (mem_ball_sub_iff v z (r / 2)).2 hv
    have huW : u ∈ Metric.ball z r :=
      Metric.ball_subset_ball (by linarith only [hr]) hu
    have hvW : v ∈ Metric.ball z r :=
      Metric.ball_subset_ball (by linarith only [hr]) hv
    have huK : u ∈ Metric.closedBall z r := Metric.ball_subset_closedBall huW
    have hDi := internal_translate_ball D D' z r hD huW hvW
    have hEi := internal_translate_ball E E' z r hE huW hvW
    have hDb' := boundaryInternal_translate D D' z r hD huK
    have hEb' := boundaryInternal_translate E E' z r hE huK
    refine ⟨u - z, v - z, hu₀, hv₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro he
      apply hne
      have he' := congrArg (fun x : ℂ => x + z) he
      simpa only [sub_add_cancel] using he'
    · simpa only [hDi] using hDpos
    · simpa only [hDi, hDb'] using hDb
    · simpa only [hEi] using hEpos
    · simpa only [hEi, hEb'] using hEb
    · simpa only [hDi, hEi] using hRatio


 
theorem probability_localWitness_translate
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r) :
    P {ω : Ω | OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω)) a z r hr} =
    P {ω : Ω | OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω)) a 0 r hr} := by
  let t : Ω → DistC := fun ω => translateDist z (h ω)
  let k : Ω → DistC := fun ω => LQGMetric.addConst (t ω) (-LQGMetric.circleAvg (h ω) 1 z)
  have ht : LQGMetric.IsWholePlaneGFF t P := by
    simpa only [t, translateDist_eq_affineComp_one] using hh.1.affineComp one_pos z
  have hk : IsNormalizedWholePlaneGFF k P := by
    simpa only [k, t] using normalized_translate_sub_circleAvg hh z
  have htrans : ∀ᵐ ω ∂P,
      OptimalConstants.FirstExit.LocalWitness (D (t ω)) (E (t ω)) a 0 r hr ↔
      OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω)) a z r hr := by
    filter_upwards [hD.translation P h (LQGMetric.GM.detGFFPlusCont hh.1) z,
      hE.translation P h (LQGMetric.GM.detGFFPlusCont hh.1) z]
      with ω hd he
    apply localWitness_translate_iff
    · intro x y
      have hx := hd (x - z) (y - z)
      simpa only [t, translateDist_eq_affineComp_one, sub_add_cancel] using hx
    · intro x y
      have hx := he (x - z) (y - z)
      simpa only [t, translateDist_eq_affineComp_one, sub_add_cancel] using hx
  have hshift : ∀ᵐ ω ∂P,
      OptimalConstants.FirstExit.LocalWitness (D (k ω)) (E (k ω)) a 0 r hr ↔
      OptimalConstants.FirstExit.LocalWitness (D (t ω)) (E (t ω)) a 0 r hr := by
    simpa only [k] using OptimalConstants.FirstExit.ae_localWitness_addConst_iff hD hE P t
      (LQGMetric.GM.detGFFPlusCont ht) (fun ω => -LQGMetric.circleAvg (h ω) 1 z)
      a 0 r hr
  have hS : NullMeasurableSet
      {g : DistC | OptimalConstants.FirstExit.LocalWitness (D g) (E g) a 0 r hr} (P.map h) :=
    (localWitnessEvent_um D E hD.measurable hE.measurable a 0 r hr).nullMeasurableSet _
  have hSk : NullMeasurableSet
      {g : DistC | OptimalConstants.FirstExit.LocalWitness (D g) (E g) a 0 r hr} (P.map k) :=
    (localWitnessEvent_um D E hD.measurable hE.measurable a 0 r hr).nullMeasurableSet _
  calc
    P {ω : Ω | OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω)) a z r hr} =
      P {ω : Ω | OptimalConstants.FirstExit.LocalWitness (D (k ω)) (E (k ω)) a 0 r hr} := by
        apply measure_congr
        filter_upwards [htrans, hshift] with ω ht hs
        exact propext (ht.symm.trans hs.symm)
    _ = (P.map k) {g : DistC | OptimalConstants.FirstExit.LocalWitness (D g) (E g) a 0 r hr} := by
      exact (Measure.map_apply₀ hk.1.measurable.aemeasurable hSk).symm
    _ = (P.map h) {g : DistC | OptimalConstants.FirstExit.LocalWitness (D g) (E g) a 0 r hr} := by
      rw [show P.map k = P.map h from by simpa only [k, t] using
        map_normalized_translate_sub_circleAvg hh z]
    _ = P {ω : Ω | OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω)) a 0 r hr} := by
      exact Measure.map_apply₀ hh.1.measurable.aemeasurable hS


 
theorem positive_upperCut_eq_one
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (a : ℝ≥0∞)
    (hpos : 0 < P {ω : Ω | a < OptimalConstants.Ratios.upperOptimal (D (h ω)) (E (h ω))}) :
    P {ω : Ω | a < OptimalConstants.Ratios.upperOptimal (D (h ω)) (E (h ω))} = 1 := by
  obtain ⟨n, hn⟩ := exists_positive_localWitness_radius ξ Q hQ D E hD hE P h hh a hpos
  let r : ℝ := (n : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let R : ℝ := r + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let W : ℂ → Set Ω := fun z =>
    {ω | OptimalConstants.FirstExit.LocalWitness (D (h ω)) (E (h ω)) a z r hr}
  let G : Set Ω := {ω | a < OptimalConstants.Ratios.upperOptimal (D (h ω)) (E (h ω))}
  have hWpos : 0 < P (W 0) := by simpa only [W, r] using hn
  have hWloc (z : ℂ) (c : Ω → ℝ) (hc : Measurable c) :
      LQGMetric.Blueprint.AEEventIn P
        (LQGMetric.Blueprint.fieldSigma
          (fun ω => LQGMetric.addConst (h ω) (c ω))
          (LQGMetric.Blueprint.ballO z R)) (W z) := by
    apply aeEventIn_localWitness_addConst P ξ Q D E hD hE h hh.1 a z r hr
      (LQGMetric.Blueprint.ballO z R) ?_ c hc
    exact Metric.closedBall_subset_ball (by dsimp [R]; linarith)
  have hWprob (k : ℕ) : P (W (R • ((4 * k : ℝ) : ℂ))) = P (W 0) := by
    exact probability_localWitness_translate ξ Q D E hD hE P h hh a _ r hr
  have hWsub (k : ℕ) : W (R • ((4 * k : ℝ) : ℂ)) ≤ᵐ[P] G := by
    have hplus : LQGMetric.IsGFFPlusCont h P :=
      LQGMetric.GM.detGFFPlusCont hh.1
    filter_upwards [BiLipschitz.Barrier.ae_barrier hD hQ P h hh,
      BiLipschitz.Barrier.ae_barrier hE hQ P h hh,
      hD.length P h hplus, hE.length P h hplus]
      with ω hBD hBE hLD hLE hw
    exact OptimalConstants.FirstExit.localWitness_lt_upperOptimal (D (h ω)) (E (h ω)) hLD hLE
      (fun γ s t hγ _ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hBD hLD hγ)
      (fun γ s t hγ _ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hBE hLE hγ)
      hr hw
  let p₀ : ℝ := (P (W 0)).toReal
  have hp₀ : 0 < p₀ := ENNReal.toReal_pos hWpos.ne' (measure_ne_top P _)
  have hp₀le : ENNReal.ofReal p₀ ≤ P (W 0) := by
    rw [ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact LQGMetric.GM.measure_eq_one_of_L2_7
    (LQGMetric.GM.gm_L2_7 LQGMetric.MarkovFinal.lmLem2_1 LQGMetric.MQ.mqLem4_1Gen)
    hh.1 hR hp₀ hWloc (fun k => (hWprob k).symm ▸ hp₀le) hWsub


 
theorem finite_pair_of_acrossDist_lt_top (D : LSCMetric) (A : EuclideanAnnulus)
    (hA : acrossDist D A < ⊤) :
    ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair D u v := by
  obtain ⟨u, hu, v, hv, hfin⟩ := by
    simpa only [acrossDist, iInf_lt_top, exists_prop] using hA
  have huv : u ≠ v := by
    intro he
    have hu' : dist u A.center = A.innerRadius := by
      simpa only [EuclideanAnnulus.innerBoundary, Metric.mem_sphere] using hu
    have hv' : dist v A.center = A.outerRadius := by
      simpa only [EuclideanAnnulus.outerBoundary, Metric.mem_sphere] using hv
    have hrad : A.innerRadius = A.outerRadius := by rw [← hu', ← hv', he]
    exact (ne_of_lt A.2.2) hrad
  refine ⟨u, v, (OptimalConstants.Ratios.ratioPair_iff_finite_positive D u v).2 ⟨huv, ?_, hfin⟩⟩
  exact lt_of_le_of_ne bot_le (Ne.symm (fun hz => huv (D.isExtMetric.2.1 u v hz)))


 
theorem ae_lt_top_of_twoSidedTight
    {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ≥0∞)
    (hX : IsTwoSidedTight P X) (i : ι) :
    ∀ᵐ ω ∂P, X i ω < ⊤ := by
  have hzero : P {ω | X i ω = ⊤} = 0 := by
    by_contra hn
    have hp : 0 < P {ω | X i ω = ⊤} := pos_iff_ne_zero.mpr hn
    have hptop : P {ω | X i ω = ⊤} ≠ ⊤ := measure_ne_top P _
    have hpr : 0 < (P {ω | X i ω = ⊤}).toReal :=
      ENNReal.toReal_pos hp.ne' hptop
    obtain ⟨M, hM, hTail⟩ := hX.2
      ((P {ω | X i ω = ⊤}).toReal / 2) (by linarith)
    have hsubset : {ω | X i ω = ⊤} ⊆
        {ω | ENNReal.ofReal M < X i ω} := by
      intro ω hω
      change X i ω = ⊤ at hω
      simpa only [Set.mem_ofPred_eq, hω] using (ENNReal.ofReal_lt_top (r := M))
    have hle : P {ω | X i ω = ⊤} ≤
        ENNReal.ofReal ((P {ω | X i ω = ⊤}).toReal / 2) :=
      (measure_mono hsubset).trans (hTail i).1
    have hreal : (P {ω | X i ω = ⊤}).toReal ≤
        (P {ω | X i ω = ⊤}).toReal / 2 := by
      apply (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤
        (P {ω | X i ω = ⊤}).toReal / 2)).mp
      simpa only [ENNReal.ofReal_toReal hptop] using hle
    linarith
  change {ω | X i ω < ⊤} ∈ ae P
  apply mem_ae_iff.mpr
  simpa only [Set.compl_setOf, not_lt, top_le_iff] using hzero


 
theorem ae_finitePair_of_tightness
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair (D (h ω)) u v := by
  let A : EuclideanAnnulus := ⟨((0 : ℂ), (1 : ℝ), (2 : ℝ)), by norm_num, by norm_num⟩
  let r : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  let X : Set.Ioi (0 : ℝ) → Ω → ℝ≥0∞ := fun s ω =>
    ENNReal.ofReal ((s : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) s 0))) *
      acrossDist (D (h ω)) (A.dilate s s.2)
  have hV : IsTwoSidedTight P X :=
    (hD.tightness P h hh
      (fun s ω => LQGMetric.circleAvg (h ω) s 0)
      (fun s => ae_isCircleAverage_old hh.1 s 0) A).1
  filter_upwards [ae_lt_top_of_twoSidedTight P X hV r] with ω hfin
  have hcoef : 0 < ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r 0))) := by
    dsimp [r]
    positivity
  have hAfin : acrossDist (D (h ω)) (A.dilate r r.2) < ⊤ := by
    by_contra hn
    have ht : acrossDist (D (h ω)) (A.dilate r r.2) = ⊤ := eq_top_iff.mpr (not_lt.mp hn)
    have hcf : ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r 0))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hcoef).ne'
    have : X r ω = ⊤ := by simpa only [X, ht] using ENNReal.mul_top hcf
    exact (ne_top_of_lt hfin) this
  exact finite_pair_of_acrossDist_lt_top (D (h ω)) (A.dilate r r.2) hAfin


 
theorem ae_eq_essSup_of_positive_cut_eq_one
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ≥0∞)
    (hXm : AEMeasurable X P)
    (hCut : ∀ a : ℝ≥0∞, 0 < P {ω | a < X ω} → P {ω | a < X ω} = 1) :
    ∀ᵐ ω ∂P, X ω = essSup X P := by
  let c := essSup X P
  let d := essInf X P
  have hc : ∀ᵐ ω ∂P, X ω ≤ c := ae_le_essSup
  have hd : ∀ᵐ ω ∂P, d ≤ X ω := ae_essInf_le
  have hdc : d ≤ c := by
    obtain ⟨ω, hdω, hcω⟩ := (hd.and hc).exists
    exact hdω.trans hcω
  have hcd : c ≤ d := by
    by_contra hn
    have hdc' : d < c := lt_of_not_ge hn
    obtain ⟨a, hda, hac⟩ := exists_between hdc'
    have hpUpper : 0 < P {ω | a < X ω} := by
      by_contra hp
      have hz : P {ω | a < X ω} = 0 := (not_lt.mp hp).antisymm bot_le
      have hle : ∀ᵐ ω ∂P, X ω ≤ a := by
        change {ω | X ω ≤ a} ∈ ae P
        apply mem_ae_iff.mpr
        simpa only [Set.compl_ofPred, not_le] using hz
      exact (not_lt_of_ge (essSup_le_of_ae_le a hle)) hac
    have hfull : ∀ᵐ ω ∂P, a < X ω := by
      apply (mem_ae_iff_prob_eq_one₀
        (nullMeasurableSet_lt aemeasurable_const hXm)).2
      exact hCut a hpUpper
    have hpLower : 0 < P {ω | X ω < a} := by
      by_contra hp
      have hz : P {ω | X ω < a} = 0 := (not_lt.mp hp).antisymm bot_le
      have hle : ∀ᵐ ω ∂P, a ≤ X ω := by
        change {ω | a ≤ X ω} ∈ ae P
        apply mem_ae_iff.mpr
        simpa only [Set.compl_ofPred, not_le] using hz
      exact (not_lt_of_ge (le_essInf_of_ae_le a hle)) hda
    have hzero : P {ω | X ω < a} = 0 := by
      have hnot : ∀ᵐ ω ∂P, ¬ X ω < a := hfull.mono fun ω hω => not_lt.mpr hω.le
      simpa only [ae_iff, not_not] using hnot
    exact (not_lt_of_ge hzero.le) hpLower
  filter_upwards [hc, hd] with ω hcω hdω
  exact le_antisymm hcω (hcd.trans hdω)


 
theorem normalized_id_map
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    IsNormalizedWholePlaneGFF (id : DistC → DistC) (P.map h) := by
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  have hμold : LQGMetric.IsNormalizedWPGFF (id : DistC → DistC) (P.map h) := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hh.1, ?_⟩
    have hS : MeasurableSet {g : DistC | LQGMetric.circleAvg g 1 0 = 0} :=
      measurableSet_eq_fun (LQGMetric.measurable_circleAvg_left 1 0) measurable_const
    exact (ae_map_iff hh.1.measurable.aemeasurable hS).2 hold.2
  exact isNormalizedWholePlaneGFF_iff_old.mpr hμold

 
theorem biLipBound_of_symmetric_ebl (K : ℝ) (hK : 1 ≤ K)
    (D E : LSCMetric)
    (hb : ∀ z w : ℂ, E (z, w) ≤ ENNReal.ofReal K * D (z, w) ∧
      D (z, w) ≤ ENNReal.ofReal K * E (z, w)) :
    OptimalConstants.Ratios.BiLipBound D E (ENNReal.ofReal K)⁻¹ (ENNReal.ofReal K) := by
  have hK0 : ENNReal.ofReal K ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < K)).ne'
  intro u v
  constructor
  · calc
      (ENNReal.ofReal K)⁻¹ * D (u, v) ≤
          (ENNReal.ofReal K)⁻¹ * ((ENNReal.ofReal K) * E (u, v)) := by
            gcongr
            exact (hb u v).2
      _ = E (u, v) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK0 ENNReal.ofReal_ne_top, one_mul]
  · exact (hb u v).1


 
theorem upperOptimal_ae_constant
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      (∀ᵐ g ∂μ, OptimalConstants.Ratios.upperOptimal (D g) (E g) = c) := by
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D E hD hE
  have hμplus : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.detGFFPlusCont hμ.1
  have hB : ∀ᵐ g ∂μ,
      OptimalConstants.Ratios.BiLipBound (D g) (E g)
        (ENNReal.ofReal K)⁻¹ (ENNReal.ofReal K) := by
    filter_upwards [hEBL μ id hμplus] with g hg
    exact biLipBound_of_symmetric_ebl K hK (D g) (E g) hg
  have hp : ∀ᵐ g ∂μ, ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair (D g) u v :=
    ae_finitePair_of_tightness ξ Q D hD μ id hμ
  have hc : 0 < (ENNReal.ofReal K)⁻¹ :=
    ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  let X : DistC → ℝ≥0∞ := fun g => OptimalConstants.Ratios.upperOptimal (D g) (E g)
  have hXm : AEMeasurable X μ := by
    simpa only [X] using (OptimalConstants.OrderTests.aeMeasurable_optima μ D E
      hD.measurable hE.measurable hc hB hp).2
  have hcut (a : ℝ≥0∞) (hpos : 0 < μ {g | a < X g}) :
      μ {g | a < X g} = 1 :=
    positive_upperCut_eq_one ξ Q hQ D E hD hE μ id hμ a hpos
  have hconst := ae_eq_essSup_of_positive_cut_eq_one μ X hXm hcut
  have hreg : ∀ᵐ g ∂μ, 0 < X g ∧ X g < ⊤ := by
    filter_upwards [hB, hp] with g hb hpair
    have hopt := OptimalConstants.Ratios.optimal_pos_finite_of_biLipBound hc ENNReal.ofReal_lt_top hb hpair
    exact ⟨hopt.1.trans_le hopt.2.1, hopt.2.2⟩
  obtain ⟨g, hgconst, hgreg⟩ := (hconst.and hreg).exists
  exact ⟨essSup X μ, by simpa only [← hgconst] using hgreg.1,
    by simpa only [← hgconst] using hgreg.2, hconst⟩


 
theorem ratioPair_iff_of_symmetric_ebl (K : ℝ) (hK : 1 ≤ K)
    (D E : LSCMetric)
    (hb : ∀ z w : ℂ, E (z, w) ≤ ENNReal.ofReal K * D (z, w) ∧
      D (z, w) ≤ ENNReal.ofReal K * E (z, w))
    (u v : ℂ) :
    OptimalConstants.Ratios.RatioPair D u v ↔ OptimalConstants.Ratios.RatioPair E u v := by
  have hKpos : 0 < ENNReal.ofReal K :=
    ENNReal.ofReal_pos.mpr (by linarith : 0 < K)
  have hKfin : ENNReal.ofReal K < ⊤ := ENNReal.ofReal_lt_top
  constructor
  · intro hp
    obtain ⟨hne, hDpos, hDfin⟩ := (OptimalConstants.Ratios.ratioPair_iff_finite_positive D u v).1 hp
    have hEfin : E (u, v) < ⊤ :=
      (hb u v).1.trans_lt (ENNReal.mul_lt_top hKfin hDfin)
    have hEpos : 0 < E (u, v) := by
      by_contra hn
      have hEz : E (u, v) = 0 := (not_lt.mp hn).antisymm bot_le
      have hDz : D (u, v) = 0 := by
        apply le_antisymm _ zero_le
        simpa only [hEz, mul_zero] using (hb u v).2
      exact (ne_of_gt hDpos) hDz
    exact (OptimalConstants.Ratios.ratioPair_iff_finite_positive E u v).2 ⟨hne, hEpos, hEfin⟩
  · intro hp
    obtain ⟨hne, hEpos, hEfin⟩ := (OptimalConstants.Ratios.ratioPair_iff_finite_positive E u v).1 hp
    have hDfin : D (u, v) < ⊤ :=
      (hb u v).2.trans_lt (ENNReal.mul_lt_top hKfin hEfin)
    have hDpos : 0 < D (u, v) := by
      by_contra hn
      have hDz : D (u, v) = 0 := (not_lt.mp hn).antisymm bot_le
      have hEz : E (u, v) = 0 := by
        apply le_antisymm _ zero_le
        simpa only [hDz, mul_zero] using (hb u v).1
      exact (ne_of_gt hEpos) hEz
    exact (OptimalConstants.Ratios.ratioPair_iff_finite_positive D u v).2 ⟨hne, hDpos, hDfin⟩


 
theorem lowerOptimal_eq_inv_upperOptimal_of_ebl (K : ℝ) (hK : 1 ≤ K)
    (D E : LSCMetric)
    (hb : ∀ z w : ℂ, E (z, w) ≤ ENNReal.ofReal K * D (z, w) ∧
      D (z, w) ≤ ENNReal.ofReal K * E (z, w)) :
    OptimalConstants.Ratios.lowerOptimal D E = (OptimalConstants.Ratios.upperOptimal E D)⁻¹ := by
  unfold OptimalConstants.Ratios.lowerOptimal OptimalConstants.Ratios.upperOptimal
  simp only [ENNReal.inv_iSup]
  refine iInf_congr fun u => iInf_congr fun v => ?_
  refine iInf_congr_Prop (ratioPair_iff_of_symmetric_ebl K hK D E hb u v) ?_
  intro hp
  have hfin := ((OptimalConstants.Ratios.ratioPair_iff_finite_positive E u v).1 hp).2.2
  have hpos := ((OptimalConstants.Ratios.ratioPair_iff_finite_positive E u v).1 hp).2.1
  exact (ENNReal.inv_div (Or.inl hfin.ne) (Or.inl hpos.ne')).symm


 
theorem hDET_proved :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
    ∀ (D D' : DistC → LSCMetric), IsWeakLQGMetric ξ Q D →
      IsWeakLQGMetric ξ Q D' →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∃ cMinus cPlus : ℝ≥0∞,
      0 < cMinus ∧ cMinus < ⊤ ∧ 0 < cPlus ∧ cPlus < ⊤ ∧
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) ∧
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) := by
  intro ξ Q hQ D D' hD hD' Ω _ P _ h hh
  let μ : Measure DistC := P.map h
  letI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hh.1.measurable.aemeasurable).2 inferInstance
  have hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ :=
    normalized_id_map P h hh
  obtain ⟨cPlus, hcPlus0, hcPlusTop, hPlus⟩ :=
    upperOptimal_ae_constant ξ Q hQ D D' hD hD' μ hμ
  obtain ⟨cSwap, hcSwap0, hcSwapTop, hSwap⟩ :=
    upperOptimal_ae_constant ξ Q hQ D' D hD' hD μ hμ
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D D' hD hD'
  have hμplus : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.detGFFPlusCont hμ.1
  have hMinus : ∀ᵐ g ∂μ,
      OptimalConstants.Ratios.lowerOptimal (D g) (D' g) = cSwap⁻¹ := by
    filter_upwards [hEBL μ id hμplus, hSwap] with g hb hs
    rw [lowerOptimal_eq_inv_upperOptimal_of_ebl K hK (D g) (D' g) hb, hs]
  have hMinusP : ∀ᵐ ω ∂P,
      OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cSwap⁻¹ :=
    ae_of_ae_map hh.1.measurable.aemeasurable hMinus
  have hPlusP : ∀ᵐ ω ∂P,
      OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus :=
    ae_of_ae_map hh.1.measurable.aemeasurable hPlus
  refine ⟨cSwap⁻¹, cPlus, ?_, ?_, hcPlus0, hcPlusTop, hMinusP, hPlusP⟩
  · exact ENNReal.inv_pos.mpr hcSwapTop.ne
  · exact ENNReal.inv_lt_top.mpr hcSwap0


end SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism
