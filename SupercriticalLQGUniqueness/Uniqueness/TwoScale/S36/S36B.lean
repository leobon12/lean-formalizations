import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.S36
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.BadB
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.E3Clause




 






















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

 
def gridLen (ε : ℝ) : ℝ := Real.log ε⁻¹ / Real.log 8

 
def gridIdx (ε : ℝ) : Finset ℕ := Finset.Icc ⌈gridLen ε⌉₊ ⌊2 * gridLen ε⌋₊

theorem eight_zpow_eq_exp (k : ℕ) : (8 : ℝ) ^ (-(k : ℤ)) = Real.exp (-(k : ℝ) * Real.log 8) := by
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num)]
  congr 1
  push_cast
  ring

theorem gridLen_nonneg {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ gridLen ε :=
  div_nonneg (Real.log_nonneg ((one_le_inv₀ hε0).mpr hε1)) (Real.log_pos (by norm_num)).le

theorem eight_zpow_le_iff {ε : ℝ} (hε0 : 0 < ε) (k : ℕ) :
    (8 : ℝ) ^ (-(k : ℤ)) ≤ ε ↔ gridLen ε ≤ k := by
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  rw [eight_zpow_eq_exp, ← Real.le_log_iff_exp_le hε0, gridLen, div_le_iff₀ hlog8, Real.log_inv]
  constructor <;> intro h <;> linarith

theorem sq_le_eight_zpow_iff {ε : ℝ} (hε0 : 0 < ε) (k : ℕ) :
    ε ^ 2 ≤ (8 : ℝ) ^ (-(k : ℤ)) ↔ (k : ℝ) ≤ 2 * gridLen ε := by
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  rw [eight_zpow_eq_exp, ← Real.log_le_iff_le_exp (pow_pos hε0 2), Real.log_pow, gridLen,
    Real.log_inv, mul_div_assoc', le_div_iff₀ hlog8]
  push_cast
  constructor <;> intro h <;> linarith

theorem mem_gridIdx_iff {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (k : ℕ) :
    k ∈ gridIdx ε ↔ ε ^ 2 ≤ (8 : ℝ) ^ (-(k : ℤ)) ∧ (8 : ℝ) ^ (-(k : ℤ)) ≤ ε := by
  have hL := gridLen_nonneg hε0 hε1
  rw [gridIdx, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by linarith),
    sq_le_eight_zpow_iff hε0, eight_zpow_le_iff hε0]
  exact and_comm

theorem card_gridIdx_ge {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    gridLen ε - 1 ≤ ((gridIdx ε).card : ℝ) := by
  have hL : 0 ≤ gridLen ε := gridLen_nonneg hε0 hε1
  unfold gridIdx
  rw [Nat.card_Icc]
  have ha : (⌈gridLen ε⌉₊ : ℝ) < gridLen ε + 1 := Nat.ceil_lt_add_one hL
  have hb : 2 * gridLen ε < (⌊2 * gridLen ε⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hab : ⌈gridLen ε⌉₊ ≤ ⌊2 * gridLen ε⌋₊ + 1 := by
    have h1 : (⌈gridLen ε⌉₊ : ℝ) < (⌊2 * gridLen ε⌋₊ : ℝ) + 2 := by linarith
    have h2 : ⌈gridLen ε⌉₊ < ⌊2 * gridLen ε⌋₊ + 2 := by exact_mod_cast h1
    omega
  rw [Nat.cast_sub hab]
  push_cast
  linarith

theorem one_le_of_mem_gridIdx {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {k : ℕ}
    (hk : k ∈ gridIdx ε) : 1 ≤ k := by
  have hk' := ((mem_gridIdx_iff hε0 hε1.le k).mp hk).2
  by_contra h0
  have hk0 : k = 0 := by omega
  rw [hk0] at hk'
  norm_num at hk'
  linarith

theorem eight_le_gridLen {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ (8 : ℝ) ^ (-(8 : ℤ))) :
    8 ≤ gridLen ε := by
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h1 : Real.log ε ≤ Real.log ((8 : ℝ) ^ (-(8 : ℤ))) := Real.log_le_log hε0 hε
  rw [Real.log_zpow] at h1
  rw [gridLen, le_div_iff₀ hlog8, Real.log_inv]
  push_cast at h1
  linarith

 

theorem exists_eps_threshold (κ A : ℝ) (hκ : 0 < κ) (hA : 0 ≤ A) :
    ∃ ε₀ : Ioo (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ε ≤ κ / 32 ∧ A * ε ^ 96 ≤ κ / 4 ∧ 8 ≤ gridLen ε := by
  have h8 : 0 < (8 : ℝ) ^ (-(8 : ℤ)) := by positivity
  have h8' : (8 : ℝ) ^ (-(8 : ℤ)) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by norm_num)
  set x : ℝ := min (min (κ / 32) (κ / (4 * (A + 1)))) ((8 : ℝ) ^ (-(8 : ℤ))) with hxdef
  have hx0 : 0 < x := lt_min (lt_min (by positivity) (by positivity)) h8
  have hx1 : x < 1 := (min_le_right _ _).trans_lt h8'
  refine ⟨⟨x, hx0, hx1⟩, fun ε hε0 hεx => ?_⟩
  change ε ≤ x at hεx
  have hε1 : ε ≤ 1 := hεx.trans hx1.le
  have hεκ : ε ≤ κ / 32 := hεx.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεA : ε ≤ κ / (4 * (A + 1)) := hεx.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε8 : ε ≤ (8 : ℝ) ^ (-(8 : ℤ)) := hεx.trans (min_le_right _ _)
  refine ⟨hεκ, ?_, eight_le_gridLen hε0 hε8⟩
  have h96 : ε ^ 96 ≤ ε := pow_le_of_le_one hε0.le hε1 (by norm_num)
  have hfrac : A * (κ / (4 * (A + 1))) ≤ κ / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc A * ε ^ 96 ≤ A * ε := mul_le_mul_of_nonneg_left h96 hA
    _ ≤ A * (κ / (4 * (A + 1))) := mul_le_mul_of_nonneg_left hεA hA
    _ ≤ κ / 4 := hfrac

 
def relGood {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ Q : ℝ) (a : Ioo (3 / 4 : ℝ) 1) (θ C : Ioi (0 : ℝ)) (p : ℝ)
    (b : Ioi (0 : ℝ)) (ε : ℝ) : Finset ℕ :=
  (gridIdx ε).filter fun k =>
    ENNReal.ofReal p ≤ P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (relRad b k) a C θ (h ω)}

 

 

theorem attained_good_rel (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (cPlus : ℝ≥0∞) (hcP0 : 0 < cPlus) (hcPt : cPlus < ⊤)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) :
    ∃ θ : Ioi (0 : ℝ), ∃ a : Ioo (3 / 4 : ℝ) 1, ∃ p : Ioo (0 : ℝ) 1,
      ∀ Ctop : Ioo (0 : ℝ) cPlus.toReal, ∃ C' : Ioi (0 : ℝ),
        (Ctop : ℝ) < C' ∧ (C' : ℝ) < cPlus.toReal ∧
        ∀ κ : Ioi (0 : ℝ), ∃ ε₀ : Ioo (0 : ℝ) 1, ∀ (b : Ioi (0 : ℝ)) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          ENNReal.ofReal (κ : ℝ) ≤ P {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) b κ C'} →
          (3 / 4 : ℝ) * gridLen ε ≤
            ((relGood P h D D' (ξ : ℝ) Q a θ ⟨Ctop, Ctop.property.1⟩ p b ε).card : ℝ) := by
  
  obtain ⟨cMinus, cPlus', hm0, hmt, -, -, hMinus, hPlus'⟩ :=
    OptimalConstants.Determinism.hDET_proved ξ Q hQ D D' hD hD' P h hh
  have hcc : cPlus' = cPlus := by
    obtain ⟨ω, h1, h2⟩ := (hPlus'.and hPlus).exists
    exact h1.symm.trans h2
  rw [hcc] at hPlus'
  
  obtain ⟨plm, clm, hplm0, hplm1, hclm0, hcover⟩ := cover_probB
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
  
  obtain ⟨a₀, hE3⟩ := E3_prob ξ Q hQ D hD (ps / 4) hps4 q
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
    exact (measure_mono hsub).trans (hE3 P h hh z r)
  
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
  have hfrac0 : 0 < (2 * (K : ℝ) + 1) / (2 * K + 2) * (Cp - C) :=
    mul_pos (by positivity) (sub_pos.mpr hCCp)
  have hgap : (C : ℝ) + (K : ℝ) / ((K : ℝ) + 1) * (Cp - (C : ℝ)) < C'v := by
    have := mul_lt_mul_of_pos_right hfrac1 (sub_pos.mpr hCCp)
    linarith
  have hC'Cp : C'v < Cp := by
    have := mul_lt_mul_of_pos_right hfrac2 (sub_pos.mpr hCCp)
    linarith
  have hCC' : (C : ℝ) < C'v := by linarith
  have hC'0 : 0 < C'v := by linarith
  set C' : Ioi (0 : ℝ) := ⟨C'v, hC'0⟩ with hC'Sdef
  refine ⟨C', hCC', hC'Cp, ?_⟩
  intro κ
  have hκ0 : 0 < (κ : ℝ) := κ.2
  
  obtain ⟨J, hJ2, hJ⟩ := geoCompactB_prob ξ Q hQ D hD ((κ : ℝ) / 2) (by positivity)
  
  obtain ⟨ε₀, hε₀⟩ := exists_eps_threshold κ (clm * (200 * ((2 : ℝ) ^ (J + 1) + 1) + 3) ^ 2)
    hκ0 (by positivity)
  refine ⟨ε₀, ?_⟩
  intro b ε hε0 hεε₀ hGκ
  obtain ⟨hεκ, hbudget, hL8⟩ := hε₀ ε hε0 hεε₀
  have hε1 : ε < 1 := hεε₀.trans_lt ε₀.2.2
  
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
  by_contra hcount
  push Not at hcount
  
  set good := relGood P h D D' (ξ : ℝ) Q (aWin a) θ C ps b ε with hgooddef
  set R := (gridIdx ε).filter (fun k => ¬ ENNReal.ofReal ps ≤
    P {ω | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q (relRad b k) (aWin a) C θ (h ω)}) with hRdef
  have hcard : good.card + R.card = (gridIdx ε).card :=
    Finset.card_filter_add_card_filter_not (s := gridIdx ε) _
  have hgrid := card_gridIdx_ge hε0 hε1.le
  have hcardR : (good.card : ℝ) + R.card = (gridIdx ε).card := by exact_mod_cast hcard
  have hRcard : gridLen ε ≤ 8 * R.card := by linarith
  have hRne : R.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    have hR0 : R.card = 0 := by omega
    rw [hR0, Nat.cast_zero, mul_zero] at hRcard
    linarith
  have hRk : ∀ k ∈ R, 1 ≤ k ∧ ε ^ 2 ≤ (8 : ℝ) ^ (-(k : ℤ)) ∧ (8 : ℝ) ^ (-(k : ℤ)) ≤ ε := by
    intro k hk
    have hkI : k ∈ gridIdx ε := Finset.mem_of_mem_filter k hk
    exact ⟨one_le_of_mem_gridIdx hε0 hε1 hkI, (mem_gridIdx_iff hε0 hε1.le k).mp hkI⟩
  have hrate := exp_rate_le_eps hε0 R.card hRcard
  
  have hsite : ∀ (w : ℂ), ∀ k ∈ R, ENNReal.ofReal plm ≤ P {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D'
      (ξ : ℝ) Q w (relRad b k) q a K C θ cMinus.toReal cPlus.toReal} := by
    intro w k hk
    have hkbad := (Finset.mem_filter.mp hk).2
    have hH : P {ω | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q (relRad b k) (aWin a) C θ (h ω)} ≤
        ENNReal.ofReal ps := (not_le.mp hkbad).le
    have hL := attained_prob_of_clauses P h hh ξ Q D D' hD hD' w (relRad b k) q a K C θ
      Cm Cp ps hps0.le (hE1 q hqq₁ P h hh w _) (hE2 q a haM hE2q P h hh w _) (hE3a w _)
      (hE4 P h hh w _) hH
    rw [h12] at hL
    exact hL
  
  obtain ⟨S, hSm, hSc, hScov⟩ := hcover P h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hcPt hMinus
    hPlus q a K C θ ((2 : ℝ) ^ (J + 1)) (by positivity) b ε hε0 hε1.le R hRne hRk hrate hsite
  
  have hsub : {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) b κ C'} ⊆
      (Sᶜ ∪ {ω | ¬ GeoCompactEventB (D (h ω)) J b}) ∪
        {ω | ¬ (BiLipschitz.Barrier.Barrier (D (h ω)) ∧ (D (h ω)).IsLengthSpace ∧
          ∀ x y : ℂ, D' (h ω) (x, y) ≤ ENNReal.ofReal Cp * D (h ω) (x, y))} := by
    intro ω hG
    by_contra hno
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hno
    obtain ⟨⟨hωS, hωJ⟩, hωB, hωL, hωC⟩ := hno
    exact not_G_of_coverB (D (h ω)) (D' (h ω)) hωB hωL (ξ : ℝ) Q q a K C θ Cm Cp C' κ hCCp.le
      hgap hωC b hε0 hεκ hJ2 hωJ (hScov ω hωS) hG
  have hupper : P {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) b κ C'} ≤
      ENNReal.ofReal ((κ : ℝ) / 4) + ENNReal.ofReal ((κ : ℝ) / 2) := by
    calc P {ω | OptimalConstants.Ratios.G (D (h ω)) (D' (h ω)) b κ C'}
        ≤ P ((Sᶜ ∪ {ω | ¬ GeoCompactEventB (D (h ω)) J b}) ∪
          {ω | ¬ (BiLipschitz.Barrier.Barrier (D (h ω)) ∧ (D (h ω)).IsLengthSpace ∧
            ∀ x y : ℂ, D' (h ω) (x, y) ≤ ENNReal.ofReal Cp * D (h ω) (x, y))}) :=
          measure_mono hsub
      _ ≤ P (Sᶜ ∪ {ω | ¬ GeoCompactEventB (D (h ω)) J b}) + 0 := by
          rw [← hWnull]
          exact measure_union_le _ _
      _ ≤ P Sᶜ + P {ω | ¬ GeoCompactEventB (D (h ω)) J b} := by
          rw [add_zero]
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal ((κ : ℝ) / 4) + ENNReal.ofReal ((κ : ℝ) / 2) :=
          add_le_add (hSc.trans (ENNReal.ofReal_le_ofReal hbudget)) (hJ P h hh b)
  have hsum : ENNReal.ofReal ((κ : ℝ) / 4) + ENNReal.ofReal ((κ : ℝ) / 2) <
      ENNReal.ofReal (κ : ℝ) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff hκ0).mpr (by linarith)
  exact lt_irrefl _ ((hGκ.trans hupper).trans_lt hsum)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
