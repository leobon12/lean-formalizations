import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51Budget
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51Iface
import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Centre




 












set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC addConst)

theorem blockFamily_nonempty (δ : ℝ) (m : ℕ) : (blockFamily δ m).Nonempty := by
  obtain ⟨j, hj⟩ := Finset.card_pos.1 (shapeData_card_pos δ m)
  exact ⟨(1, j), Finset.mem_product.2 ⟨by simp [orientations], hj⟩⟩

 
theorem blockGood_of_budgets {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD' : IsWeakLQGMetric ξ Q D') (hGFF : IsNormalizedWholePlaneGFF h P) {cm : ℝ} (hcm : 0 < cm)
    (hReg : ∀ᵐ ω ∂P,
      (∀ (γ : ℝ → ℂ) (a b : ℝ), (D' (h ω)).IsCurve γ a b → ContinuousOn γ (Icc a b)) ∧
      (D' (h ω)).IsLengthSpace ∧ ∀ p : ℂ × ℂ, D (h ω) p ≤ ENNReal.ofReal cm⁻¹ * D' (h ω) p)
    {pLM cLM : ℝ}
    (hLM : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsWholePlaneGFF h P →
        ∀ (z : ℂ) (r : ℕ → ℝ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ 1 / 4) →
          (∀ k, AEEventIn P
            (fieldSigma (fun ω => addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) z))
              (annulus z (1 / 4 * r k) (3 / 4 * r k))) (E k)) →
          (∀ k, ENNReal.ofReal pLM ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < 3 / 4 * K} ≤
            ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * K)))
    (a : Ioo (3 / 4 : ℝ) 1) (Cmid : Ioi (0 : ℝ)) (θ : Ioi (0 : ℝ)) (p : Ioo (0 : ℝ) 1)
    {lam R : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1 / 100) (hlamcm : lam ≤ cm) (hR : 1 ≤ R)
    (hmarg : ∀ (μ : Measure DistC) [IsProbabilityMeasure μ],
      IsNormalizedWholePlaneGFF (id : DistC → DistC) μ → ∀ (w : ℂ) (s : Ioi (0 : ℝ)),
        ENNReal.ofReal pLM ≤ μ {g | GEv ξ Q lam R D' w s g})
    (m : ℕ) (hm2 : 2 * (1 / 4 : ℝ) ^ m ≤ (1 - (a : ℝ)) ^ 2)
    (hE20 : (2 * R ^ 2 + 1) * (2 * (1 / 4 : ℝ) ^ m) ^ (θ : ℝ) ≤ lam ^ 2)
    (hUb : ((8 * (2 * gridHalf (lam * Objects.Density.endptScale m) + 1) : ℕ) : ℝ) *
        (cLM * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) ≤ (p : ℝ) / 8)
    (Ksh : ℕ)
    (hShield : ∀ b : ℝ, 0 < b →
      (P.map h) {g | ¬ shieldData lam b Ksh (D g)} ≤ ENNReal.ofReal (blockMarginal p lam m)) :
    BlockGood P h D D' ξ Q a Cmid θ p lam m Ksh := by
  intro b hb hH
  set μ : Measure DistC := P.map h with hμdef
  have hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ := Objects.ProbabilityS7S9.normalizedGFF_id_map' P h hGFF
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hGFF.1.measurable.aemeasurable).2 inferInstance
  have hhm : AEMeasurable h P := hGFF.1.measurable.aemeasurable
  let bI : Ioi (0 : ℝ) := ⟨b, hb⟩
  set δ : ℝ := lam * Objects.Density.endptScale m with hδdef
  set N : ℕ := (shapeData δ m).card with hNdef
  have hN : 0 < N := shapeData_card_pos δ m
  let H : Set Ω := {ω | OptimalConstants.Ratios.HtildeEvent D D' (ξ : ℝ) Q bI a Cmid θ (h ω)}
  let Hn : Fin 4 → Set Ω := fun i => {ω | HtHalf D D' bI a Cmid θ (orient i) (h ω)}
  let U : Set Ω := {ω | UEv (ξ : ℝ) Q lam R D' b hb a δ m (h ω)}
  let RegS : Set Ω := {ω |
    (∀ (γ : ℝ → ℂ) (a b : ℝ), (D' (h ω)).IsCurve γ a b → ContinuousOn γ (Icc a b)) ∧
      (D' (h ω)).IsLengthSpace ∧ ∀ p : ℂ × ℂ, D (h ω) p ≤ ENNReal.ofReal cm⁻¹ * D' (h ω) p}
  let J : Fin 4 → Finset (ℝ × ℝ × ℝ) := fun _ => shapeData δ m
  let F : Fin 4 → (ℝ × ℝ × ℝ) → Set Ω := fun i j =>
    {ω | coreAt lam b a (orient i) j.2.1 j.2.2 (j.1 * b) Cmid (D (h ω)) (D' (h ω))}
  let Sh : Set Ω := {ω | shieldData lam b Ksh (D (h ω))}
  have hJ : ∀ i, (J i).Nonempty := fun _ => Finset.card_pos.1 hN
  have hcover : H ⊆ ⋃ i, Hn i := by
    intro ω hω
    obtain ⟨i, hi⟩ := htilde_half_cover D D' (ξ : ℝ) Q bI a Cmid θ (h ω) hω
    exact mem_iUnion.2 ⟨i, hi⟩
  have hU : P Uᶜ ≤ ENNReal.ofReal p / 4 / 2 := by
    have h1 : P Uᶜ ≤ μ {g | ¬ UEv (ξ : ℝ) Q lam R D' b hb a δ m g} :=
      Measure.le_map_apply hhm {g | ¬ UEv (ξ : ℝ) Q lam R D' b hb a δ m g}
    have h2 := measure_not_UEv_le hLM μ hμ ξ Q D' hD' lam R (hmarg μ hμ) b hb a δ m
    have h3 : ((8 * (2 * gridHalf δ + 1) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) ≤
          ENNReal.ofReal ((p : ℝ) / 8) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hUb
    rw [ofReal_div_eight]
    exact h1.trans (h2.trans h3)
  have hRegnull : P RegSᶜ = 0 := ae_iff.mp hReg
  have hcore : ∀ i, Hn i ∩ U ∩ RegS ⊆ ⋃ j ∈ J i, F i j := by
    rintro i ω ⟨⟨hHn, hUω⟩, hc, hL, hcomp⟩
    obtain ⟨j, hj, hcj⟩ := core_of_half (ξ := (ξ : ℝ)) (Q := Q) (lam := lam) (R := R) D D' (h ω)
      hc hL hcm hcomp bI a Cmid θ m i hlam hlam1 hlamcm hR hm2 hE20 hHn hUω
    exact mem_biUnion hj hcj
  have hSh : P Shᶜ ≤ ENNReal.ofReal p / 4 / 2 / N / 2 := by
    have h1 : P Shᶜ ≤ μ {g | ¬ shieldData lam b Ksh (D g)} :=
      Measure.le_map_apply hhm {g | ¬ shieldData lam b Ksh (D g)}
    rw [ofReal_div_chain _ N hN]
    exact h1.trans (hShield b hb)
  obtain ⟨i, j, hj, hbound⟩ := Objects.Blocks.t51_bookkeeping P H U RegS Sh Hn J hJ F N (fun _ => le_rfl)
    ENNReal.ofReal_ne_top hH hcover hU hRegnull hcore hSh
  refine ⟨(orient i, j), Finset.mem_product.2 ⟨orient_mem i, hj⟩, ?_⟩
  intro C T hClam hTb hTa hTn hTu hTv hTs
  have hset : h ⁻¹' {g | Objects.Excursions.blockRaw C T Ksh (Cmid : ℝ) D D' g} = F i j ∩ Sh := by
    ext ω
    exact blockRaw_iff_core_shield C T Ksh Cmid D D' (h ω) hClam hTb hTa hTn hTu hTv hTs
  calc ENNReal.ofReal (blockMarginal p lam m) = ENNReal.ofReal p / 4 / 2 / N / 2 := by
        rw [ofReal_div_chain _ N hN]
        rfl
    _ ≤ P (F i j ∩ Sh) := hbound
    _ = P (h ⁻¹' {g | Objects.Excursions.blockRaw C T Ksh (Cmid : ℝ) D D' g}) := by rw [hset]
    _ ≤ (P.map h) {g | Objects.Excursions.blockRaw C T Ksh (Cmid : ℝ) D D' g} := Measure.le_map_apply hhm _

theorem stage1_lam_le_hundredth {ξ : Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (s : Objects.Density.T58Stage1 ξ Q cm cp Kann p0 pbar) : s.lam ≤ 1 / 100 := by
  have hcp : 0 < cp := s.cm_pos.trans s.cm_lt_cp
  have hq : (cm / cp) ^ 2 < 1 := by
    have h1 : cm / cp < 1 := (div_lt_one hcp).2 s.cm_lt_cp
    have h0 : 0 ≤ cm / cp := div_nonneg s.cm_pos.le hcp.le
    nlinarith
  have hmin : min cm (min cp⁻¹ ((cm / cp) ^ 2)) < 1 :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) hq
  have h10 : 0 < (10 : ℝ) ^ (-(100 : ℤ)) := zpow_pos (by norm_num) _
  have htiny : (10 : ℝ) ^ (-(100 : ℤ)) ≤ 1 / 100 := by
    rw [zpow_neg]
    norm_num
  have : s.lam < (10 : ℝ) ^ (-(100 : ℤ)) := by
    calc s.lam < (10 : ℝ) ^ (-(100 : ℤ)) * min cm (min cp⁻¹ ((cm / cp) ^ 2)) := s.lam_small
      _ ≤ (10 : ℝ) ^ (-(100 : ℤ)) * 1 := mul_le_mul_of_nonneg_left hmin.le h10.le
      _ = (10 : ℝ) ^ (-(100 : ℤ)) := mul_one _
  exact (this.trans_le htiny).le

theorem stage1_lam_le_cm {ξ : Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (s : Objects.Density.T58Stage1 ξ Q cm cp Kann p0 pbar) : s.lam ≤ cm := by
  have h10p : 0 < (10 : ℝ) ^ (-(100 : ℤ)) := zpow_pos (by norm_num) _
  have h10 : (10 : ℝ) ^ (-(100 : ℤ)) ≤ 1 := by
    rw [zpow_neg]
    norm_num
  have : s.lam < cm := by
    calc s.lam < (10 : ℝ) ^ (-(100 : ℤ)) * min cm (min cp⁻¹ ((cm / cp) ^ 2)) := s.lam_small
      _ ≤ (10 : ℝ) ^ (-(100 : ℤ)) * cm := mul_le_mul_of_nonneg_left (min_le_left _ _) h10p.le
      _ ≤ 1 * cm := mul_le_mul_of_nonneg_right h10 s.cm_pos.le
      _ = cm := one_mul _
  exact this.le

 
theorem t51Statement_holds : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric),
    IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
    IsNormalizedWholePlaneGFF h P → ∀ cMinus cPlus : ℝ≥0∞,
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
    ∀ (hstrict : cMinus < cPlus), 0 < Q → ∀ (hcm : 0 < cMinus) (hcp : cPlus < ⊤),
    ∀ (θ : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1) (p : Set.Ioo (0 : ℝ) 1)
      (pbar : Set.Ioo (0 : ℝ) 1),
      T51Statement P h D D' ξ Q cMinus.toReal cPlus.toReal a θ p pbar
        (Objects.Density.toReal_pos_of_pos hcm hcp hstrict) (Objects.Density.toReal_lt_of_lt hcp hstrict) := by
  intro Ω _ P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict hQ hcm hcp θ a p pbar
  set cm := cMinus.toReal with hcmdef
  set cp := cPlus.toReal with hcpdef
  have hcmR : 0 < cm := Objects.Density.toReal_pos_of_pos hcm hcp hstrict
  have hcmTop : cMinus ≠ ⊤ := (hstrict.trans hcp).ne
  set μ : Measure DistC := P.map h with hμdef
  have hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ := Objects.ProbabilityS7S9.normalizedGFF_id_map' P h hGFF
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hGFF.1.measurable.aemeasurable).2 inferInstance
  
  obtain ⟨pLM, cLM, -, hpLM1, hcLM0, hLM⟩ := Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open (1 / 4)
    (3 / 4) (by norm_num) (by norm_num) (by norm_num) (2 * Real.log 16)
    (by positivity) (3 / 4) (by norm_num) (by norm_num)
  
  have hRex : ∀ s : Objects.Density.T58Stage1 ξ Q cm cp a p pbar, ∃ R : ℝ, 1 ≤ R ∧
      ∀ (μ : Measure DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : DistC → DistC) μ → ∀ (w : ℂ) (s' : Ioi (0 : ℝ)),
          ENNReal.ofReal pLM ≤ μ {g | GEv ξ Q s.lam R D' w s' g} :=
    fun s => exists_GEv_radius ξ Q hQ D' hD' s.lam s.lam_pos pLM hpLM1
  choose Rf hRf1 hRf using hRex
  
  have hplus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hGFF.1
  have hReg : ∀ᵐ ω ∂P,
      (∀ (γ : ℝ → ℂ) (a b : ℝ), (D' (h ω)).IsCurve γ a b → ContinuousOn γ (Icc a b)) ∧
      (D' (h ω)).IsLengthSpace ∧ ∀ p : ℂ × ℂ, D (h ω) p ≤ ENNReal.ofReal cm⁻¹ * D' (h ω) p := by
    filter_upwards [BiLipschitz.Barrier.ae_curves_continuous hD' hQ P h hGFF, hD'.2.1 P h hplus,
      ae_optimal_allPairs_sample P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus]
      with ω h1 h2 h3
    refine ⟨h1.2.1, h2, fun q => ?_⟩
    have hinv : ENNReal.ofReal cm⁻¹ = cMinus⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hcmR, hcmdef, ENNReal.ofReal_toReal hcmTop]
    rw [hinv]
    calc D (h ω) q = cMinus⁻¹ * (cMinus * D (h ω) q) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hcm.ne' hcmTop, one_mul]
      _ ≤ cMinus⁻¹ * D' (h ω) q := by gcongr; exact (h3 q).1
  
  refine ⟨fun s m => 2 * (1 / 4 : ℝ) ^ m ≤ (1 - (a : ℝ)) ^ 2 ∧
      (2 * Rf s ^ 2 + 1) * (2 * (1 / 4 : ℝ) ^ m) ^ (θ : ℝ) ≤ s.lam ^ 2 ∧
      ((8 * (2 * gridHalf (s.lam * Objects.Density.endptScale m) + 1) : ℕ) : ℝ) *
        (cLM * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) ≤ (p : ℝ) / 8, ?_, ?_⟩
  · intro s
    have ha1 : (0 : ℝ) < (1 - (a : ℝ)) ^ 2 := pow_pos (by linarith [a.2.2]) 2
    have hp8 : (0 : ℝ) < (p : ℝ) / 8 := by linarith [p.2.1]
    exact (eventually_two_quarter_le ha1).and ((eventually_E20 (Rf s) θ.2 s.lam_pos).and
      (eventually_union_budget s.lam_pos (by linarith [stage1_lam_le_hundredth s]) hcLM0.le hp8))
  · rintro s m ⟨hm2, hE20, hUb⟩
    have hlam1 := stage1_lam_le_hundredth s
    have hlamcm := stage1_lam_le_cm s
    by_cases hC : ∃ C₀ : Objects.CorrectedEvent.Constants, C₀.lamConst = s.lam
    · obtain ⟨C₀, hC₀⟩ := hC
      obtain ⟨_, _, q, _, _, _, hq, hq1, hMarg⟩ := Objects.Shield.exists_shield_marginal_energy ξ Q D hD C₀
      obtain ⟨aS, cS, haS, _, Hfail⟩ := Objects.Shield.shield_failure_le μ hμ ξ Q D hD C₀ q hq hq1
        (hMarg μ hμ)
      have hpr : 0 < blockMarginal p s.lam m := blockMarginal_pos p.2.1 _ _
      have hlim : Tendsto (fun K : ℕ => cS * Real.exp (-aS * K)) atTop (𝓝 0) := by
        have hneg : Tendsto (fun K : ℕ => -aS * (K : ℝ)) atTop atBot :=
          tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
        simpa only [Function.comp_def, mul_zero] using
          (Real.tendsto_exp_atBot.comp hneg).const_mul cS
      filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds hpr)] with Ksh hK1 hKs
      refine blockGood_of_budgets P h ξ Q D D' hD' hGFF hcmR hReg hLM a _ θ p s.lam_pos hlam1
        hlamcm (hRf1 s) (hRf s) m hm2 hE20 hUb Ksh ?_
      intro b hb
      let T₀ : Objects.CorrectedEvent.TubeData :=
        { r := b, rho := 1, alpha := 0, K := 1, Kpos := Nat.one_pos, orientation := 1,
          psiU := 0, psiV := 0, blockRadius := 0, lambda := 0, A_endpt := 0, mollifier := 0,
          bump := 0, netRadius := 0, netSites := ∅ }
      have hT₀ : T₀.rho * T₀.r = b := one_mul b
      have hset : {g | ¬ shieldData s.lam b Ksh (D g)} = {g | ¬ Objects.Excursions.shield C₀ T₀ Ksh (D g)} := by
        ext g
        simp only [mem_ofPred_eq, shield_iff_shieldData C₀ T₀ Ksh (D g) hC₀ hT₀]
      rw [hset]
      exact (Hfail T₀ Ksh (by rw [hT₀]; exact hb) hK1).trans (ENNReal.ofReal_le_ofReal hKs.le)
    · filter_upwards with Ksh
      intro b hb _
      obtain ⟨x, hx⟩ := blockFamily_nonempty (s.lam * Objects.Density.endptScale m) m
      exact ⟨x, hx, fun C _ hClam => absurd ⟨C, hClam⟩ hC⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
