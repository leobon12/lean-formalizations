import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.E3Grid




 



















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

theorem exists_small_m (c α lam p : ℝ) (hc : 0 < c) (hα : 0 < α) (hlam : 0 < lam) (hp : 0 < p)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, 1 ≤ m ∧ c * Real.exp (-α * m) / lam ≤ p ∧ (1 / 5 : ℝ) ^ m ≤ δ := by
  obtain ⟨m₁, hm₁⟩ := exists_pow_lt_of_lt_one (show 0 < p * lam / c by positivity)
    (show Real.exp (-α) < 1 from Real.exp_lt_one_iff.mpr (by linarith))
  obtain ⟨m₂, hm₂⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 5 : ℝ) < 1 by norm_num)
  refine ⟨max (max m₁ m₂) 1, le_max_right _ _, ?_, ?_⟩
  · have hle : Real.exp (-α) ^ (max (max m₁ m₂) 1) ≤ Real.exp (-α) ^ m₁ :=
      pow_le_pow_of_le_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith)).le
        ((le_max_left _ _).trans (le_max_left _ _))
    have hexp : Real.exp (-α * (max (max m₁ m₂) 1 : ℕ)) = Real.exp (-α) ^ (max (max m₁ m₂) 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp, div_le_iff₀ hlam]
    have := (hle.trans hm₁.le)
    rw [le_div_iff₀ hc] at this
    linarith
  · exact (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      ((le_max_right _ _).trans (le_max_left _ _))).trans hm₂.le

 

theorem e3_num_eps (e : ℝ) (he0 : 0 < e) (he1 : e ≤ 1 / 5) : e ^ 2 / 16 ≤ e / 80 := by
  nlinarith

theorem e3_num_near {ε r : ℝ} {N : ℕ} (hε : 0 < ε) (hr : 0 < r) (hN0 : 0 < N)
    (hN : 4 * Real.pi / ε < N) :
    (1 - (1 - ε / 2)) * r + Real.pi * r / N < ε * r := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNε : 4 * Real.pi < N * ε := by rwa [div_lt_iff₀ hε] at hN
  have h1 : Real.pi * r / N < ε * r / 4 := by
    rw [div_lt_iff₀ hNr]
    have := mul_lt_mul_of_pos_right hNε hr
    nlinarith
  have h2 : (1 - (1 - ε / 2)) * r = ε * r / 2 := by ring
  rw [h2]
  have : 0 < ε * r := mul_pos hε hr
  linarith

theorem e3_num_scale_ge {e r : ℝ} {k m : ℕ} (he0 : 0 < e) (hr : 0 < r) (hkm : k ≤ m)
    (hedef : e = (1 / 5 : ℝ) ^ m) : e ^ 2 / 16 * r ≤ leScale (e / 4 * r) k := by
  have hpow : (1 / 5 : ℝ) ^ m ≤ (1 / 5 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hkm
  rw [← hedef] at hpow
  unfold leScale
  have : e * e ≤ e * (1 / 5 : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow he0.le
  have h2 : e ^ 2 / 16 * r = e * e * r / 16 := by ring
  have h3 : e / 4 * r * (1 / 5 : ℝ) ^ k / 4 = e * (1 / 5 : ℝ) ^ k * r / 16 := by ring
  rw [h2, h3]
  have := mul_le_mul_of_nonneg_right this hr.le
  linarith

theorem e3_num_scale_le {e r : ℝ} {k : ℕ} (he0 : 0 < e) (he1 : e ≤ 1 / 5) (hr : 0 < r) :
    3 * leScale (e / 4 * r) k ≤ r / 2 := by
  have hpow : (1 / 5 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold leScale
  have h1 : e * (1 / 5 : ℝ) ^ k ≤ 1 / 5 := by
    calc e * (1 / 5 : ℝ) ^ k ≤ e * 1 := mul_le_mul_of_nonneg_left hpow he0.le
      _ ≤ 1 / 5 := by linarith
  have h3 : 3 * (e / 4 * r * (1 / 5 : ℝ) ^ k / 4) = 3 * (e * (1 / 5 : ℝ) ^ k) * r / 16 := by ring
  rw [h3]
  have := mul_le_mul_of_nonneg_right h1 hr.le
  nlinarith

theorem e3_num_final {q ε lam r card N : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hε : 0 < ε) (hr : 0 < r)
    (hlam : lam = q / (16 * Real.pi)) (hεq : ε ≤ q / 6) (hcard : card < lam * (N + 1))
    (hN : N ≤ 4 * Real.pi / ε + 2) :
    2 * (ε * r) * (card + 1) ≤ q * r := by
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have h1 : card + 1 ≤ lam * (4 * Real.pi / ε + 3) + 1 := by
    have : lam * (N + 1) ≤ lam * (4 * Real.pi / ε + 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hlam0.le
    linarith
  have h2 : 2 * (ε * r) * (lam * (4 * Real.pi / ε + 3) + 1) =
      r * (8 * Real.pi * lam + 6 * ε * lam + 2 * ε) := by
    field_simp
    ring
  have h3 : 8 * Real.pi * lam = q / 2 := by
    rw [hlam]
    field_simp
    ring
  have h4 : lam ≤ 1 / 6 := by
    rw [hlam, div_le_iff₀ (by positivity)]
    have := Real.pi_gt_three
    linarith
  have h5 : 6 * ε * lam ≤ ε := by
    have h6 : 6 * lam ≤ 1 := by linarith
    calc 6 * ε * lam = ε * (6 * lam) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h6 hε.le
      _ = ε := mul_one ε
  have h7 : 8 * Real.pi * lam + 6 * ε * lam + 2 * ε ≤ q := by linarith
  calc 2 * (ε * r) * (card + 1) ≤ 2 * (ε * r) * (lam * (4 * Real.pi / ε + 3) + 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = r * (8 * Real.pi * lam + 6 * ε * lam + 2 * ε) := h2
    _ ≤ r * q := mul_le_mul_of_nonneg_left h7 hr.le
    _ = q * r := mul_comm _ _

 
theorem E3_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∀ p : ℝ, 0 < p → ∀ q : Ioo (0 : ℝ) (1 / 100), ∃ a₀ : Ioo (1 - (q : ℝ)) 1,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
          P {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a₀} ≤ ENNReal.ofReal p := by
  obtain ⟨α, c, hα, hc, hgood⟩ := good_point_prob ξ Q hQ D hD
  intro p hp q
  have hq0 : 0 < (q : ℝ) := q.2.1
  have hq1 : (q : ℝ) < 1 / 100 := q.2.2
  set lam : ℝ := (q : ℝ) / (16 * Real.pi) with hlamdef
  have hlam : 0 < lam := by positivity
  obtain ⟨m, hm1, hmp, hme⟩ := exists_small_m c α lam p hc hα hlam hp ((q : ℝ) / 6) (by positivity)
  set e : ℝ := (1 / 5 : ℝ) ^ m with hedef
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 5 := by
    have h := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 5 by norm_num)
      (show (1 / 5 : ℝ) ≤ 1 by norm_num) hm1
    rw [pow_one] at h
    exact h
  set ε : ℝ := e ^ 2 / 16 with hεdef
  have hε0 : 0 < ε := by positivity
  have hεe : ε ≤ e / 80 := e3_num_eps e he0 he1
  have hεq : ε ≤ (q : ℝ) / 6 := by
    have : ε ≤ e := by linarith
    linarith
  set a₀v : ℝ := 1 - ε / 2 with ha₀def
  have ha₀1 : a₀v < 1 := by linarith
  have ha₀q : 1 - (q : ℝ) < a₀v := by linarith
  refine ⟨⟨a₀v, ha₀q, ha₀1⟩, ?_⟩
  intro Ω _ P _ h hh z r
  have hr : (0 : ℝ) < r := r.2
  set ρ₀ : ℝ := e / 4 * r with hρ₀def
  have hρ₀ : 0 < ρ₀ := by positivity
  set N : ℕ := ⌈4 * Real.pi / ε⌉₊ + 1 with hNdef
  have hN0 : 0 < N := Nat.succ_pos _
  have hNbig : 4 * Real.pi / ε < N := by
    have := Nat.le_ceil (4 * Real.pi / ε)
    rw [hNdef]
    push_cast
    linarith
  have hNle : (N : ℝ) ≤ 4 * Real.pi / ε + 2 := by
    rw [hNdef]
    push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 4 * Real.pi / ε by positivity)
    linarith
  
  have hnear : (1 - a₀v) * r + Real.pi * r / N < ε * r := by
    rw [ha₀def]
    exact e3_num_near hε0 hr hN0 hNbig
  have hsm : ∀ k ∈ Finset.Icc 1 m, ε * r ≤ leScale ρ₀ k := by
    intro k hk
    rw [hεdef, hρ₀def]
    exact e3_num_scale_ge he0 hr (Finset.mem_Icc.mp hk).2 hedef
  have hs1 : ∀ k ∈ Finset.Icc 1 m, 3 * leScale ρ₀ k ≤ r / 2 := by
    intro k _
    rw [hρ₀def]
    exact e3_num_scale_le he0 he1 hr
  
  let Bad : ℕ → Set Ω := fun j => {ω | ¬ ∃ k ∈ Finset.Icc 1 m,
    RatioEv (D (h ω)) (leScale_pos hρ₀ k) (gridPt z r N j)}
  have hBadm : ∀ j, MeasurableSet (Bad j) := by
    intro j
    have hset : Bad j = (⋃ k ∈ Finset.Icc 1 m, h ⁻¹'
        {g : DistC | RatioEv (D g) (leScale_pos hρ₀ k) (gridPt z r N j)})ᶜ := by
      ext ω
      simp only [Bad, mem_ofPred_eq, mem_compl_iff, mem_iUnion, mem_preimage, exists_prop]
    rw [hset]
    exact (Finset.measurableSet_biUnion _ fun k _ =>
      (measurable_ratioEv D hD.measurable _ _).preimage hh.1.measurable).compl
  have hBadP : ∀ j, P (Bad j) ≤ ENNReal.ofReal (c * Real.exp (-α * m)) := fun j =>
    hgood P h hh (gridPt z r N j) hρ₀ m hm1
  
  let f : Ω → ℝ≥0∞ := fun ω => ∑ j ∈ Finset.range (N + 1), (Bad j).indicator 1 ω
  have hfm : Measurable f :=
    Finset.measurable_sum _ fun j _ => measurable_one.indicator (hBadm j)
  have hint : ∫⁻ ω, f ω ∂P ≤ (N + 1 : ℝ≥0∞) * ENNReal.ofReal (c * Real.exp (-α * m)) := by
    rw [lintegral_finsetSum _ fun j _ => measurable_one.indicator (hBadm j)]
    calc ∑ j ∈ Finset.range (N + 1), ∫⁻ ω, (Bad j).indicator 1 ω ∂P
        = ∑ j ∈ Finset.range (N + 1), P (Bad j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact lintegral_indicator_one (hBadm j)
      _ ≤ ∑ _j ∈ Finset.range (N + 1), ENNReal.ofReal (c * Real.exp (-α * m)) :=
          Finset.sum_le_sum fun j _ => hBadP j
      _ = (N + 1 : ℝ≥0∞) * ENNReal.ofReal (c * Real.exp (-α * m)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  set thr : ℝ≥0∞ := ENNReal.ofReal (lam * (N + 1)) with hthrdef
  have hthr0 : thr ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hthrt : thr ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmarkov : P {ω | thr ≤ f ω} ≤ ENNReal.ofReal p := by
    have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hfm.aemeasurable thr
    have h1 : P {ω | thr ≤ f ω} ≤ ((N + 1 : ℝ≥0∞) *
        ENNReal.ofReal (c * Real.exp (-α * m))) / thr := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hthr0) (Or.inl hthrt), mul_comm]
      exact hmk.trans hint
    have hN1 : ((N : ℝ≥0∞) + 1) = ENNReal.ofReal ((N : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
    have h2 : ((N + 1 : ℝ≥0∞) * ENNReal.ofReal (c * Real.exp (-α * m))) / thr =
        ENNReal.ofReal (c * Real.exp (-α * m) / lam) := by
      rw [hthrdef, hN1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
      congr 1
      field_simp
    exact h1.trans (h2.trans_le (ENNReal.ofReal_le_ofReal hmp))
  
  have hcont := BiLipschitz.Barrier.ae_curves_continuous hD hQ P h hh
  have hsub : {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a₀v} ⊆
      {ω | thr ≤ f ω} ∪ {ω | ¬ ((∀ (γ : ℝ → ℂ) (a b : ℝ), (D (h ω)).IsCurve γ a b →
        ContinuousOn γ (Icc a b)))} := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, not_not] at hno
    obtain ⟨hfω, hcω⟩ := hno
    apply hω
    
    classical
    set B : Finset ℕ := (Finset.range (N + 1)).filter fun j => ω ∈ Bad j with hBdef
    have hfB : f ω = (B.card : ℝ≥0∞) := by
      simp only [f, hBdef]
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ω ∈ Bad j <;> simp [hj]
    have hBcard : (B.card : ℝ) < lam * (N + 1) := by
      have := hfω
      rw [hfB, hthrdef, ← ENNReal.ofReal_natCast] at this
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp this
    have hgoodω : ∀ j ≤ N, j ∉ B →
        ∃ k ∈ Finset.Icc 1 m, RatioEv (D (h ω)) (leScale_pos hρ₀ k) (gridPt z r N j) := by
      intro j hj hjB
      by_contra hno
      apply hjB
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj), hno⟩
    intro P' s t hP' v w _ _ hvs hws hseg
    have hdist := segment_dist_le_of_grid (D (h ω)) hcω z hr (by linarith) hε0 hρ₀ hN0 hnear
      hsm hs1 B hgoodω hP' hvs hws (by linarith) hseg
    have hcard : ((B.image (gridPt z r N)).card : ℝ) ≤ B.card := by
      exact_mod_cast Finset.card_image_le
    have hfinal : 2 * (ε * r) * ((B.image (gridPt z r N)).card + 1) ≤ (q : ℝ) * r :=
      e3_num_final hq0 (by linarith) hε0 hr hlamdef hεq (lt_of_le_of_lt hcard hBcard) hNle
    exact hdist.trans hfinal
  have hnull : P {ω | ¬ ((∀ (γ : ℝ → ℂ) (a b : ℝ), (D (h ω)).IsCurve γ a b →
      ContinuousOn γ (Icc a b)))} = 0 := by
    rw [← ae_iff]
    filter_upwards [hcont] with ω hω
    exact hω.2.1
  calc P {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a₀v}
      ≤ P ({ω | thr ≤ f ω} ∪ {ω | ¬ ((∀ (γ : ℝ → ℂ) (a b : ℝ), (D (h ω)).IsCurve γ a b →
        ContinuousOn γ (Icc a b)))}) := measure_mono hsub
    _ ≤ P {ω | thr ≤ f ω} + P {ω | ¬ ((∀ (γ : ℝ → ℂ) (a b : ℝ), (D (h ω)).IsCurve γ a b →
        ContinuousOn γ (Icc a b)))} := measure_union_le _ _
    _ ≤ ENNReal.ofReal p := by rw [hnull, add_zero]; exact hmarkov

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
