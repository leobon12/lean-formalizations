import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldShiftMarginal




 



set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

theorem ae_shieldAt_normPsi_iff
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (g : LQGMetric.DistC → LQGMetric.DistC)
    (hg : LQGMetric.IsGFFPlusCont g μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants) (t : ℝ) :
    ∀ᵐ x ∂μ,
      Objects.Excursions.shieldAt C (D (LQGMetric.GM.normPsi (g x))) t ↔
        Objects.Excursions.shieldAt C (D (g x)) t := by
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ g hg ξ Q D hD
    (fun x => -(g x LQGMetric.GM.psiOne))] with x hx
  exact Objects.ShieldLocality.shieldAt_iff_of_dist_scale C (D (g x))
    (D (LQGMetric.GM.normPsi (g x)))
    (ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g x LQGMetric.GM.psiOne))))
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
    (fun u v => hx (u, v)) t

 

theorem exists_shield_marginal_center
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants) :
    ∃ C₁ K₀ q : ℝ,
      1 ≤ C₁ ∧ 0 ≤ K₀ ∧
      q = Real.exp (-LQGMetric.gradEnergy (shieldAnnBump K₀)) / 4 ∧
      0 < q ∧ q < 1 ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF
          (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (t : ℝ), 0 < t →
          ENNReal.ofReal q ≤ μ {g | Objects.Excursions.shieldAt C (D g) t} := by
  obtain ⟨C₁, K₀, hC₁, hK₀, _, Hshift⟩ :=
    exists_shield_shift_half ξ Q D hD C
  let G : ℝ := LQGMetric.gradEnergy (shieldAnnBump K₀)
  let q : ℝ := Real.exp (-G) / 4
  have hq : 0 < q := by positivity
  have hq1 : q < 1 := by
    have hG0 : 0 ≤ G := by unfold G LQGMetric.gradEnergy; positivity
    have hExp : Real.exp (-G) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    dsimp [q]
    linarith
  refine ⟨C₁, K₀, q, hC₁, hK₀, rfl, hq, hq1, ?_⟩
  intro μ _ hμ t ht
  let φ : LQGMetric.TestC := shieldBumpAt K₀ t 0
  let f : C(ℂ, ℝ) := LQGMetric.testCont φ
  let E : Set LQGMetric.DistC :=
    {g | Objects.Excursions.shieldAt C (D (LQGMetric.GM.normPsi g)) t}
  have hEm : MeasurableSet E :=
    Objects.ShieldLocality.measurableSet_shieldAt C
      (D ∘ LQGMetric.GM.normPsi)
      (hD.measurable.comp LQGMetric.GM.measurable_normPsi) t ht
  have hEinv : ∀ (g : LQGMetric.DistC) (c : ℝ),
      LQGMetric.addConst g c ∈ E ↔ g ∈ E := by
    intro g c
    simp only [E, Set.mem_ofPred_eq, LQGMetric.GM.normPsi_addConst]
  obtain ⟨CT, hCT, hCTeq⟩ := LQGMetric.GM.exists_pair0_preimage hEm hEinv
  have hpre0 : μ E = LQGMetric.lawPair0 id μ CT := by
    rw [LQGMetric.lawPair0,
      Measure.map_apply (LQGMetric.measurable_pair0_comp hμ.1) hCT]
    congr 1
    ext g
    exact hCTeq g
  have hpreφ : μ {g | LQGMetric.addFun g f ∈ E} =
      LQGMetric.lawPair0
        (fun g => LQGMetric.addFun g (LQGMetric.testCont φ)) μ CT := by
    rw [LQGMetric.lawPair0,
      Measure.map_apply (by simpa only [id_eq] using
        (LQGMetric.measurable_pair0_addFun hμ.1 φ)) hCT]
    congr 1
    ext g
    exact hCTeq _
  have hwhole : LQGMetric.IsGFFPlusCont id μ :=
    LQGMetric.GM.detGFFPlusCont hμ.1
  have hae0 := ae_shieldAt_normPsi_iff μ id hwhole ξ Q D hD C t
  have haeφ := ae_shieldAt_normPsi_iff μ (fun g => LQGMetric.addFun g f)
    (Objects.ProbabilityS7S9.isGFFPlusCont_addFun' hμ.1 f) ξ Q D hD C t
  have hEq0 : E =ᵐ[μ] {g | Objects.Excursions.shieldAt C (D g) t} := by
    filter_upwards [hae0] with g hg
    exact propext hg
  have hEqφ : {g | LQGMetric.addFun g f ∈ E} =ᵐ[μ]
      {g | Objects.Excursions.shieldAt C (D (LQGMetric.addFun g f)) t} := by
    filter_upwards [haeφ] with g hg
    exact propext hg
  have hφprob : ENNReal.ofReal (1 / 2 : ℝ) ≤
      μ {g | LQGMetric.addFun g f ∈ E} := by
    rw [measure_congr hEqφ]
    exact Hshift μ hμ t ht
  have hCS := TwoScale.S36.measureReal_lawPair0_addFun_le_sqrt hμ.1 φ hCT
  have hGφ : LQGMetric.gradEnergy φ = G := gradEnergy_shieldBumpAt K₀ ht 0
  rw [hGφ] at hCS
  let a : ℝ := (LQGMetric.lawPair0
    (fun g => LQGMetric.addFun g (LQGMetric.testCont φ)) μ).real CT
  let b : ℝ := (LQGMetric.lawPair0 id μ).real CT
  have ha : 1 / 2 ≤ a := by
    dsimp only [a]
    rw [measureReal_def, ← hpreφ]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hφprob
  have hsq : a ^ 2 ≤ b * Real.exp G :=
    (Real.le_sqrt' (by linarith)).mp hCS
  have hb : Real.exp (-G) / 4 ≤ b := by
    have hhalf : (1 / 2 : ℝ) ^ 2 ≤ a ^ 2 :=
      pow_le_pow_left₀ (by norm_num) ha 2
    have hexp : Real.exp (-G) * Real.exp G = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      Real.exp (-G) / 4 = (1 / 2) ^ 2 * Real.exp (-G) := by ring
      _ ≤ a ^ 2 * Real.exp (-G) :=
        mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le
      _ ≤ b * Real.exp G * Real.exp (-G) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
      _ = b := by rw [mul_assoc, mul_comm (Real.exp G), hexp, mul_one]
  rw [← measure_congr hEq0, hpre0]
  have := TwoScale.S36.isProbabilityMeasure_lawPair0 hμ.1
  have hfinal : LQGMetric.lawPair0 id μ CT = ENNReal.ofReal b := by
    dsimp only [b]
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hfinal]
  exact ENNReal.ofReal_le_ofReal hb

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
