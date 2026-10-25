import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.Bad
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit.OptPos




 
























set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

 
theorem G_mono_kappa (d e : LSCMetric) (r : Ioi (0 : ℝ)) {κ κ' : Ioi (0 : ℝ)}
    (hκ : (κ' : ℝ) ≤ κ) (C : Ioi (0 : ℝ)) (hG : OptimalConstants.Ratios.G d e r κ C) : OptimalConstants.Ratios.G d e r κ' C := by
  obtain ⟨z, w, hz, hw, hRP, hle⟩ := hG
  refine ⟨z, w, hz, hw, hRP, hle.trans ?_⟩
  have hr : 0 ≤ (r : ℝ) := r.2.le
  have hsub : ∀ x : ℂ, Metric.ball x ((κ' : ℝ) * r) ⊆ Metric.ball x ((κ : ℝ) * r) := fun x =>
    Metric.ball_subset_ball (mul_le_mul_of_nonneg_right hκ hr)
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  exact iInf₂_le_of_le x (hsub z hx) (iInf₂_le y (hsub w hy))

 
theorem eventClause3_mono (d : LSCMetric) (z : ℂ) {r q a a' : ℝ} (hr : 0 < r) (haa : a ≤ a')
    (h3 : TwoScale.S36Events.EventClause3 d z r q a) : TwoScale.S36Events.EventClause3 d z r q a' := by
  intro P s t hP v w hv hvw hvs hws hseg
  refine h3 P s t hP v w hv hvw hvs hws fun τ hτ => ⟨(hseg τ hτ).1, fun hb => (hseg τ hτ).2 ?_⟩
  exact Metric.ball_subset_ball (mul_le_mul_of_nonneg_right haa hr.le) hb

theorem exists_q_small (q₁ X θ : ℝ) (hq₁ : 0 < q₁) (hθ : 0 < θ) :
    ∃ q : Ioo (0 : ℝ) (1 / 100), (q : ℝ) ≤ q₁ ∧ X ≤ (q : ℝ) ^ (-θ) := by
  have hlim : Tendsto (fun x : ℝ => x ^ (-θ)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), X ≤ x ^ (-θ) := hlim.eventually_ge_atTop X
  have h2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < min q₁ (1 / 100) :=
    (eventually_lt_nhds (lt_min hq₁ (by norm_num))).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  obtain ⟨x, hx1, hx2, hx3⟩ := (h1.and (h2.and h3)).exists
  exact ⟨⟨x, hx3, lt_of_lt_of_le hx2 (min_le_right _ _)⟩,
    (lt_of_lt_of_le hx2 (min_le_left _ _)).le, hx1⟩

theorem eight_zpow_neg (n : ℕ) : (8 : ℝ) ^ (-(n : ℤ)) = (1 / 8 : ℝ) ^ n := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

theorem exists_n_threshold (κ A : ℝ) (hκ : 0 < κ) (hA : 0 ≤ A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (8 : ℝ) ^ (-(n : ℤ)) ≤ κ / 32 ∧
      A * ((8 : ℝ) ^ (-(n : ℤ))) ^ 96 ≤ κ / 4 := by
  set x : ℝ := min (κ / 32) (κ / (4 * (A + 1))) with hxdef
  have hx : 0 < x := lt_min (by positivity) (by positivity)
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hx (show (1 / 8 : ℝ) < 1 by norm_num)
  refine ⟨n₀, fun n hn => ?_⟩
  have hε : (8 : ℝ) ^ (-(n : ℤ)) < x := by
    rw [eight_zpow_neg]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hn₀
  have hε0 : 0 ≤ (8 : ℝ) ^ (-(n : ℤ)) := by positivity
  have hε1 : (8 : ℝ) ^ (-(n : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  refine ⟨hε.le.trans (min_le_left _ _), ?_⟩
  have h96 : ((8 : ℝ) ^ (-(n : ℤ))) ^ 96 ≤ (8 : ℝ) ^ (-(n : ℤ)) :=
    pow_le_of_le_one hε0 hε1 (by norm_num)
  have hx2 : x ≤ κ / (4 * (A + 1)) := min_le_right _ _
  have hfrac : A * (κ / (4 * (A + 1))) ≤ κ / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc A * ((8 : ℝ) ^ (-(n : ℤ))) ^ 96 ≤ A * (8 : ℝ) ^ (-(n : ℤ)) :=
        mul_le_mul_of_nonneg_left h96 hA
    _ ≤ A * (κ / (4 * (A + 1))) := mul_le_mul_of_nonneg_left (hε.le.trans hx2) hA
    _ ≤ κ / 4 := hfrac

 

 
theorem ae_allPairs_upper (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ, D' (h ω) (z, w) ≤ cPlus * D (h ω) (z, w) := by
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D D' hD hD'
  have hGFFPlus : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.detGFFPlusCont hh.1
  have hB : ∀ᵐ ω ∂P, OptimalConstants.Ratios.BiLipBound (D (h ω)) (D' (h ω))
      (ENNReal.ofReal K)⁻¹ (ENNReal.ofReal K) := by
    filter_upwards [hEBL P h hGFFPlus] with ω hb
    exact OptimalConstants.Determinism.biLipBound_of_symmetric_ebl K hK (D (h ω)) (D' (h ω)) hb
  have hPair := OptimalConstants.Determinism.ae_finitePair_of_tightness ξ Q D hD P h hh
  have hLower : 0 < (ENNReal.ofReal K)⁻¹ := ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  filter_upwards [OptimalConstants.Ratios.ae_allPairs_of_ae_optima P (fun ω => D (h ω)) (fun ω => D' (h ω))
    hLower hB hPair hMinus hPlus] with ω hb z w
  exact (hb z w).2

 
theorem ae_lower_eq_inv_upper_swap (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) =
      (OptimalConstants.Ratios.upperOptimal (D' (h ω)) (D (h ω)))⁻¹ := by
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D D' hD hD'
  filter_upwards [hEBL P h (LQGMetric.GM.detGFFPlusCont hh.1)] with ω hb
  exact OptimalConstants.Determinism.lowerOptimal_eq_inv_upperOptimal_of_ebl K hK (D (h ω)) (D' (h ω)) hb

 

 

theorem upper_core (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (cPlus : ℝ≥0∞) (hcP0 : 0 < cPlus) (hcPt : cPlus < ⊤)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hE3D : ∀ p : ℝ, 0 < p → ∀ q : Ioo (0 : ℝ) (1 / 100), ∃ a₀ : Ioo (1 - (q : ℝ)) 1,
      ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        P {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a₀} ≤ ENNReal.ofReal p) :
    ∃ θ : Ioi (0 : ℝ), ∃ a : Ioo (3 / 4 : ℝ) 1, ∃ p : Ioo (0 : ℝ) 1,
      ∀ Ctop : Ioo (0 : ℝ) cPlus.toReal, ∃ n₁ : ℕ, ∀ n ≥ n₁,
        3 * n ≤ 4 * (EndSaving.Interfaces.upperGood P h D D' (ξ : ℝ) Q a θ ⟨Ctop, Ctop.property.1⟩ p n).card := by
  
  obtain ⟨cMinus, cPlus', hm0, hmt, -, -, hMinus, hPlus'⟩ :=
    OptimalConstants.Determinism.hDET_proved ξ Q hQ D D' hD hD' P h hh
  have hcc : cPlus' = cPlus := by
    obtain ⟨ω, h1, h2⟩ := (hPlus'.and hPlus).exists
    exact h1.symm.trans h2
  rw [hcc] at hPlus'
  
  obtain ⟨plm, clm, hplm0, hplm1, hclm0, hcover⟩ := cover_prob
  set ps : ℝ := (1 - plm) / 2 with hpsdef
  have hps0 : 0 < ps := by rw [hpsdef]; linarith
  have hps1 : ps < 1 := by rw [hpsdef]; linarith
  have hps4 : 0 < ps / 4 := by positivity
  have hps4' : ps / 4 < 1 := by linarith
  have h12 : 1 - 2 * ps = plm := by rw [hpsdef]; ring
  
  obtain ⟨θ, q₁, hq₁, hE1⟩ := E1_prob ξ Q D hD ps hps0
  set Cm : ℝ := cMinus.toReal with hCmdef
  set Cp : ℝ := cPlus.toReal with hCpdef
  have hCm : 0 < Cm := ENNReal.toReal_pos hm0.ne' hmt.ne
  have hCp : 0 < Cp := ENNReal.toReal_pos hcP0.ne' hcPt.ne
  
  obtain ⟨M₁, M₂, hM₁, hM₂, hE2⟩ := E2_prob ξ Q hQ D hD θ Cm Cp (ps / 4) hps4 hps4'
  have hk : 0 < Cm / (2 * Cp) := by positivity
  obtain ⟨q, hqq₁, hqM⟩ := exists_q_small q₁ (M₂ / (Cm / (2 * Cp))) θ hq₁ θ.2
  have hE2q : M₂ ≤ Cm / (2 * Cp) * (q : ℝ) ^ (-(θ : ℝ)) := by
    calc M₂ = Cm / (2 * Cp) * (M₂ / (Cm / (2 * Cp))) := by field_simp
      _ ≤ Cm / (2 * Cp) * (q : ℝ) ^ (-(θ : ℝ)) := mul_le_mul_of_nonneg_left hqM hk.le
  
  obtain ⟨a₀, hE3⟩ := hE3D (ps / 4) hps4 q
  have hM₁' : 0 < 1 / (M₁ + 1) := by positivity
  set aval : ℝ := max (a₀ : ℝ) (1 - 1 / (M₁ + 1)) with havaldef
  have ha1 : aval < 1 := max_lt a₀.2.2 (by linarith)
  have ha0 : 1 - (q : ℝ) < aval := lt_of_lt_of_le a₀.2.1 (le_max_left _ _)
  set a : Ioo (1 - (q : ℝ)) 1 := ⟨aval, ha0, ha1⟩ with hadef
  have haval : (a : ℝ) = aval := rfl
  have haM : M₁ ≤ (1 - (a : ℝ))⁻¹ := by
    have h1 : 1 - (a : ℝ) ≤ (M₁ + 1)⁻¹ := by
      rw [haval, ← one_div]
      have := le_max_right (a₀ : ℝ) (1 - 1 / (M₁ + 1))
      linarith
    have h2 : 0 < 1 - (a : ℝ) := by rw [haval]; linarith
    have h3 : M₁ + 1 ≤ (1 - (a : ℝ))⁻¹ :=
      (le_inv_comm₀ h2 (show (0 : ℝ) < M₁ + 1 by positivity)).mp h1
    linarith
  have hE3a : ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
      P {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a} ≤ ENNReal.ofReal (ps / 4) := by
    intro z r
    have hsub : {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a} ⊆
        {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a₀} := by
      intro ω hω h3
      exact hω (eventClause3_mono (D (h ω)) z r.2
        (show (a₀ : ℝ) ≤ aval from le_max_left _ _) h3)
    exact (measure_mono hsub).trans (hE3 z r)
  
  obtain ⟨K, hE4⟩ := E4_prob ξ Q D hD a (ps / 4) hps4 hps4'
  refine ⟨θ, aWin a, ⟨ps, hps0, hps1⟩, ?_⟩
  intro Ctop
  set C : Ioi (0 : ℝ) := ⟨Ctop, Ctop.property.1⟩ with hCdef
  have hC0 : 0 < (C : ℝ) := C.2
  have hCCp : (C : ℝ) < Cp := Ctop.property.2
  have hK1 : (1 : ℝ) < K := K.2
  set C'v : ℝ := (C : ℝ) + (2 * K + 1) / (2 * K + 2) * (Cp - C) with hC'def
  have hfrac1 : (K : ℝ) / ((K : ℝ) + 1) < (2 * K + 1) / (2 * K + 2) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hfrac2 : (2 * (K : ℝ) + 1) / (2 * K + 2) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hgap : (C : ℝ) + (K : ℝ) / ((K : ℝ) + 1) * (Cp - (C : ℝ)) < C'v := by
    have := mul_lt_mul_of_pos_right hfrac1 (sub_pos.mpr hCCp)
    linarith
  have hC'Cp : C'v < Cp := by
    have := mul_lt_mul_of_pos_right hfrac2 (sub_pos.mpr hCCp)
    linarith
  have hC'0 : 0 < C'v := by
    have : 0 < (2 * (K : ℝ) + 1) / (2 * K + 2) * (Cp - C) :=
      mul_pos (by positivity) (sub_pos.mpr hCCp)
    linarith
  set C' : Ioi (0 : ℝ) := ⟨C'v, hC'0⟩ with hC'Sdef
  
  have hC'lt : ENNReal.ofReal (C' : ℝ) < cPlus := by
    rw [← ENNReal.ofReal_toReal hcPt.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff hCp).mpr hC'Cp
  obtain ⟨κ₀, hκ₀⟩ := OptimalConstants.FixedUnit.positive_unit_G_of_upperOptimal_ae_constant ξ Q hQ D D' hD hD' P h
    hh cPlus hPlus C' hC'lt
  set g₀ := P {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) ⟨1, by norm_num⟩ κ₀ C'} with hg₀
  have hg₀top : g₀ ≠ ⊤ := measure_ne_top P _
  have hg₀pos : 0 < g₀.toReal := ENNReal.toReal_pos hκ₀.ne' hg₀top
  set κv : ℝ := min (min (κ₀ : ℝ) g₀.toReal) (1 / 2) with hκvdef
  have hκ0 : 0 < κv := lt_min (lt_min κ₀.2 hg₀pos) (by norm_num)
  set κ : Ioi (0 : ℝ) := ⟨κv, hκ0⟩ with hκdef
  have hGκ : ENNReal.ofReal κv ≤ P {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) ⟨1, by norm_num⟩ κ C'} := by
    calc ENNReal.ofReal κv ≤ ENNReal.ofReal g₀.toReal :=
          ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (min_le_right _ _))
      _ = g₀ := ENNReal.ofReal_toReal hg₀top
      _ ≤ _ := measure_mono fun ω hω =>
          G_mono_kappa _ _ _ (show κv ≤ κ₀ from (min_le_left _ _).trans (min_le_left _ _)) _ hω
  
  obtain ⟨J, hJ⟩ := geoCompact_prob ξ Q hQ D hD P h hh (κv / 2) (by positivity)
  set B : ℝ := (2 : ℝ) ^ (J + 1) with hBdef
  have hB0 : 0 ≤ B := by positivity
  
  have hGFFPlus : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.detGFFPlusCont hh.1
  have hW : ∀ᵐ ω ∂P, BiLipschitz.Barrier.Barrier (D (h ω)) ∧ (D (h ω)).IsLengthSpace ∧
      ∀ x y : ℂ, D' (h ω) (x, y) ≤ ENNReal.ofReal Cp * D (h ω) (x, y) := by
    filter_upwards [BiLipschitz.Barrier.ae_barrier hD hQ P h hh, hD.2.1 P h hGFFPlus,
      ae_allPairs_upper ξ Q D D' hD hD' P h hh cMinus cPlus hMinus hPlus] with ω h1 h2 h3
    refine ⟨h1, h2, fun x y => ?_⟩
    rw [hCpdef, ENNReal.ofReal_toReal hcPt.ne]
    exact h3 x y
  have hWnull : P {ω | ¬ (BiLipschitz.Barrier.Barrier (D (h ω)) ∧ (D (h ω)).IsLengthSpace ∧
      ∀ x y : ℂ, D' (h ω) (x, y) ≤ ENNReal.ofReal Cp * D (h ω) (x, y))} = 0 := by
    rw [ae_iff] at hW
    exact hW
  
  obtain ⟨n₀, hn₀⟩ := exists_n_threshold κv (clm * (200 * (B + 1) + 3) ^ 2) hκ0 (by positivity)
  refine ⟨max n₀ 8, fun n hn => ?_⟩
  have hn8 : 8 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hεκ, hbudget⟩ := hn₀ n (le_trans (le_max_left _ _) hn)
  by_contra hcount
  push Not at hcount
  
  set good := EndSaving.Interfaces.upperGood P h D D' (ξ : ℝ) Q (aWin a) θ C ps n with hgooddef
  set R := (Finset.Icc n (2 * n)).filter (fun j => ¬ ENNReal.ofReal ps ≤
    P {ω | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q (EndSaving.Interfaces.dyadicRadius j) (aWin a) C θ (h ω)}) with hRdef
  have hcard : good.card + R.card = n + 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.Icc n (2 * n))
      (fun j => ENNReal.ofReal ps ≤
        P {ω | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q (EndSaving.Interfaces.dyadicRadius j) (aWin a) C θ (h ω)})
    rw [Nat.card_Icc] at h
    have h' : 2 * n + 1 - n = n + 1 := by omega
    rw [h'] at h
    exact h
  have hRcard : n ≤ 8 * R.card := by omega
  have hRsub : R ⊆ Finset.Icc n (2 * n) := Finset.filter_subset _ _
  
  have hsite : ∀ (w : ℂ), ∀ j ∈ R, ENNReal.ofReal plm ≤ P {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D'
      (ξ : ℝ) Q w (EndSaving.Interfaces.dyadicRadius j) q a K C θ cMinus.toReal cPlus.toReal} := by
    intro w j hj
    have hjbad := (Finset.mem_filter.mp hj).2
    have hH : P {ω | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q (EndSaving.Interfaces.dyadicRadius j) (aWin a) C θ (h ω)} ≤
        ENNReal.ofReal ps := (not_le.mp hjbad).le
    have hL := attained_prob_of_clauses P h hh ξ Q D D' hD hD' w (EndSaving.Interfaces.dyadicRadius j) q a K C θ
      Cm Cp ps hps0.le (hE1 q hqq₁ P h hh w _) (hE2 q a haM hE2q P h hh w _) (hE3a w _)
      (hE4 P h hh w _) hH
    rw [h12] at hL
    exact hL
  
  obtain ⟨S, hSm, hSc, hScov⟩ := hcover P h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hcPt hMinus
    hPlus q a K C θ B hB0 n (by omega) R hRsub hRcard hsite
  
  have hsub : {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) ⟨1, by norm_num⟩ κ C'} ⊆
      (Sᶜ ∪ {ω | ¬ GeoCompactEvent (D (h ω)) J}) ∪
        {ω | ¬ (BiLipschitz.Barrier.Barrier (D (h ω)) ∧ (D (h ω)).IsLengthSpace ∧
          ∀ x y : ℂ, D' (h ω) (x, y) ≤ ENNReal.ofReal Cp * D (h ω) (x, y))} := by
    intro ω hG
    by_contra hno
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hno
    obtain ⟨⟨hωS, hωJ⟩, hωB, hωL, hωC⟩ := hno
    exact not_G_of_cover (D (h ω)) (D' (h ω)) hωB hωL (ξ : ℝ) Q q a K C θ Cm Cp C' κ hCCp.le
      hgap hωC n J hεκ hωJ (hScov ω hωS) hG
  have hupper : P {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) ⟨1, by norm_num⟩ κ C'} ≤
      ENNReal.ofReal (κv / 4) + ENNReal.ofReal (κv / 2) := by
    calc P {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) ⟨1, by norm_num⟩ κ C'}
        ≤ P ((Sᶜ ∪ {ω | ¬ GeoCompactEvent (D (h ω)) J}) ∪
          {ω | ¬ (BiLipschitz.Barrier.Barrier (D (h ω)) ∧ (D (h ω)).IsLengthSpace ∧
            ∀ x y : ℂ, D' (h ω) (x, y) ≤ ENNReal.ofReal Cp * D (h ω) (x, y))}) :=
          measure_mono hsub
      _ ≤ P (Sᶜ ∪ {ω | ¬ GeoCompactEvent (D (h ω)) J}) + 0 := by
          rw [← hWnull]
          exact measure_union_le _ _
      _ ≤ P Sᶜ + P {ω | ¬ GeoCompactEvent (D (h ω)) J} := by
          rw [add_zero]
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (κv / 4) + ENNReal.ofReal (κv / 2) :=
          add_le_add (hSc.trans (ENNReal.ofReal_le_ofReal hbudget)) hJ
  have hsum : ENNReal.ofReal (κv / 4) + ENNReal.ofReal (κv / 2) < ENNReal.ofReal κv := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff hκ0).mpr (by linarith)
  exact lt_irrefl _ ((hGκ.trans hupper).trans_lt hsum)

 

 

theorem lower_core (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (cMinus : ℝ≥0∞) (hm0 : 0 < cMinus) (hmt : cMinus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hE3D' : ∀ p : ℝ, 0 < p → ∀ q : Ioo (0 : ℝ) (1 / 100), ∃ a₀ : Ioo (1 - (q : ℝ)) 1,
      ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        P {ω | ¬ TwoScale.S36Events.EventClause3 (D' (h ω)) z r q a₀} ≤ ENNReal.ofReal p) :
    ∀ Cmid : {x : ℝ // cMinus.toReal < x},
      ∃ κ : Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
        3 * n ≤ 4 * (EndSaving.Interfaces.lowerGood P h D D' κ
          ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card := by
  intro Cmid
  set cS : ℝ≥0∞ := cMinus⁻¹ with hcSdef
  have hswap : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D' (h ω)) (D (h ω)) = cS := by
    filter_upwards [ae_lower_eq_inv_upper_swap ξ Q D D' hD hD' P h hh, hMinus] with ω h1 h2
    rw [hcSdef, ← h2, h1, inv_inv]
  have hcS0 : 0 < cS := ENNReal.inv_pos.mpr hmt.ne
  have hcSt : cS < ⊤ := ENNReal.inv_lt_top.mpr hm0
  have hCm0 : 0 < cMinus.toReal := ENNReal.toReal_pos hm0.ne' hmt.ne
  have hCmid0 : 0 < (Cmid : ℝ) := hCm0.trans Cmid.property
  have hcSr : cS.toReal = (cMinus.toReal)⁻¹ := ENNReal.toReal_inv cMinus
  set Cv : ℝ := (Cmid : ℝ)⁻¹ with hCvdef
  have hCv0 : 0 < Cv := inv_pos.mpr hCmid0
  have hCvlt : Cv < cS.toReal := by
    rw [hcSr]
    exact (inv_lt_inv₀ hCmid0 hCm0).mpr Cmid.property
  set ζ : ℝ := min (1 / 2) ((cS.toReal - Cv) / 2) with hζdef
  have hζ0 : 0 < ζ := lt_min (by norm_num) (by linarith)
  have hζle : ζ ≤ (cS.toReal - Cv) / 2 := min_le_right _ _
  set CH : ℝ := Cv + ζ with hCHdef
  have hCH0 : 0 < CH := by positivity
  have hCHlt : CH < cS.toReal := by linarith
  obtain ⟨θ, a, p, hup⟩ := upper_core ξ Q hQ D' D hD' hD P h hh cS hcS0 hcSt hswap hE3D'
  obtain ⟨n₁, hn₁⟩ := hup ⟨CH, hCH0, hCHlt⟩
  
  obtain ⟨-, -, -, -, κ₁, hHG⟩ := OptimalConstants.FixedUnit.ae_HEvent_to_GEvent ξ Q hQ D' D hD' hD P h hh a θ ζ hζ0
  set κv : ℝ := min (min (κ₁ : ℝ) (p : ℝ)) (1 / 2) with hκvdef
  have hκ0 : 0 < κv := lt_min (lt_min κ₁.2 p.2.1) (by norm_num)
  have hκκ₁ : κv ≤ κ₁ := (min_le_left _ _).trans (min_le_left _ _)
  refine ⟨⟨κv, hκ0⟩, n₁, fun n hn => (hn₁ n hn).trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro j hj
  rw [EndSaving.Interfaces.upperGood, Finset.mem_filter] at hj
  rw [EndSaving.Interfaces.lowerGood, Finset.mem_filter]
  refine ⟨hj.1, ?_⟩
  have hζC : ζ < CH := by linarith
  have hCeq : (⟨CH - ζ, sub_pos.mpr hζC⟩ : Ioi (0 : ℝ)) =
      ⟨((Cmid : ℝ))⁻¹, inv_pos.mpr hCmid0⟩ := by
    apply Subtype.ext
    change CH - ζ = (Cmid : ℝ)⁻¹
    rw [hCHdef]
    ring
  calc ENNReal.ofReal κv ≤ ENNReal.ofReal (p : ℝ) :=
        ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (min_le_right _ _))
    _ ≤ P {ω | OptimalConstants.Ratios.HEvent D' D (ξ : ℝ) Q (EndSaving.Interfaces.dyadicRadius j) a ⟨CH, hCH0⟩ θ (h ω)} := hj.2
    _ ≤ P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (EndSaving.Interfaces.dyadicRadius j) ⟨κv, hκ0⟩
          ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩} := by
      apply measure_mono_ae
      filter_upwards [hHG] with ω hω hH
      have hG : OptimalConstants.Ratios.G (D' (h ω)) (D (h ω)) (EndSaving.Interfaces.dyadicRadius j) κ₁
          ⟨CH - ζ, sub_pos.mpr hζC⟩ := hω (EndSaving.Interfaces.dyadicRadius j) ⟨CH, hCH0⟩ hζC hH
      rw [hCeq] at hG
      exact (OptimalConstants.Ratios.Gtilde_iff_swap (D (h ω)) (D' (h ω)) (EndSaving.Interfaces.dyadicRadius j) ⟨κv, hκ0⟩
        ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩).mpr
        (G_mono_kappa _ _ _ hκκ₁ _ hG)

 

 

theorem hS36upper_of_E3
    (hE3 : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q → ∀ D : DistC → LSCMetric,
      IsWeakLQGMetric ξ Q D → ∀ p : ℝ, 0 < p → ∀ q : Set.Ioo (0 : ℝ) (1 / 100),
      ∃ a₀ : Set.Ioo (1 - (q : ℝ)) 1,
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)),
          P {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a₀} ≤ ENNReal.ofReal p) :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cPlus : ℝ≥0∞, 0 < cPlus → cPlus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∃ θ : Set.Ioi (0 : ℝ),
        ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
          ∃ p : Set.Ioo (0 : ℝ) 1,
            ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
              ∃ n₁ : ℕ, ∀ n ≥ n₁,
                3 * n ≤ 4 * (EndSaving.Interfaces.upperGood P h D D' ξ Q a θ
                  ⟨Ctop, Ctop.property.1⟩ p n).card := by
  intro ξ Q hQ D D' hD hD' Ω _ P _ h hh cPlus hcP0 hcPt hPlus
  exact upper_core ξ Q hQ D D' hD hD' P h hh cPlus hcP0 hcPt hPlus fun p hp q => by
    obtain ⟨a₀, ha₀⟩ := hE3 ξ Q hQ D hD p hp q
    exact ⟨a₀, fun z r => ha₀ P h hh z r⟩

 

theorem hS36lower_of_E3
    (hE3 : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q → ∀ D : DistC → LSCMetric,
      IsWeakLQGMetric ξ Q D → ∀ p : ℝ, 0 < p → ∀ q : Set.Ioo (0 : ℝ) (1 / 100),
      ∃ a₀ : Set.Ioo (1 - (q : ℝ)) 1,
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)),
          P {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a₀} ≤ ENNReal.ofReal p) :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus : ℝ≥0∞, 0 < cMinus → cMinus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        ∀ Cmid : {x : ℝ // cMinus.toReal < x},
          ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
            3 * n ≤ 4 * (EndSaving.Interfaces.lowerGood P h D D' κ
              ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card := by
  intro ξ Q hQ D D' hD hD' Ω _ P _ h hh cMinus hm0 hmt hMinus
  exact lower_core ξ Q hQ D D' hD hD' P h hh cMinus hm0 hmt hMinus fun p hp q => by
    obtain ⟨a₀, ha₀⟩ := hE3 ξ Q hQ D' hD' p hp q
    exact ⟨a₀, fun z r => ha₀ P h hh z r⟩

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
