import SupercriticalLQGUniqueness.B2.PfeLocal.L1Iter

 
















set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 

theorem l1_measure_eventually_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : ℕ → Set Ω} {x : ℝ≥0∞}
    (hle : ∀ᶠ n in atTop, μ (A n) ≤ x) : μ {ω | ∀ᶠ n in atTop, ω ∈ A n} ≤ x := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hle
  have e : {ω | ∀ᶠ n in atTop, ω ∈ A n} = ⋃ N, ⋂ n ≥ N, A n := by
    ext ω; simp only [mem_ofPred_eq, eventually_atTop, mem_iUnion, mem_iInter]
  rw [e]
  have hmono : Monotone fun N => ⋂ n ≥ N, A n := fun N N' hNN' =>
    biInter_subset_biInter_left fun n hn => le_trans hNN' hn
  rw [hmono.measure_iUnion]
  refine iSup_le fun N => ?_
  calc μ (⋂ n ≥ N, A n) ≤ μ (A (max N N₀)) :=
        measure_mono (biInter_subset_of_mem (le_max_left N N₀))
    _ ≤ x := hN₀ _ (le_max_right N N₀)

 
theorem l1_circleAvg_tendsto_prob {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    (z : ℂ) {r : ℝ} (hr : 0 < r) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => P' {ω | η < |circleAvg (hN n ω) r z - circleAvg (h' ω) r z|})
      atTop (𝓝 0) := by
  obtain ⟨hprob, hcan⟩ := PfeAxioms.normalized_canonical_model
  have hh'm : Measurable h' := hh'.1.measurable
  have hca : Measurable fun g : DistC => circleAvg g r z := measurable_circleAvg_left r z
  have hma : ∀ j, Measurable fun g : DistC => CircleAvg.mollAvg g j z r := fun j => by
    simp_rw [CircleAvg.mollAvg_eq]
    exact measurable_distOn_apply (CircleAvg.circBump j z r)
  
  have hcanon : Tendsto (fun j => normGFFLaw
      {g | η / 3 < |circleAvg g r z - CircleAvg.mollAvg g j z r|}) atTop (𝓝 0) := by
    refine l1_measure_tendsto_zero (fun j => measurableSet_lt measurable_const
      (hca.sub (hma j)).abs) ?_
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hcan.1 z hr] with g ⟨a, ha⟩
    simp only [id_eq] at ha
    have hlim : Tendsto (fun j => |circleAvg g r z - CircleAvg.mollAvg g j z r|) atTop
        (𝓝 0) := by
      rw [CircleAvg.circleAvg_eq_of_tendsto ha]
      simpa using ((tendsto_const_nhds (x := a)).sub ha).abs
    filter_upwards [(tendsto_order.1 hlim).2 (η / 3) (by positivity)] with j hj
    exact not_lt.2 hj.le
  have hlimit : Tendsto (fun j => P'
      {ω | η / 3 < |CircleAvg.mollAvg (h' ω) j z r - circleAvg (h' ω) r z|}) atTop (𝓝 0) := by
    refine l1_measure_tendsto_zero (fun j => measurableSet_lt measurable_const
      (((hma j).comp hh'm).sub (hca.comp hh'm)).abs) ?_
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hh'.1 z hr] with ω ⟨a, ha⟩
    have hlim : Tendsto (fun j => |CircleAvg.mollAvg (h' ω) j z r - circleAvg (h' ω) r z|)
        atTop (𝓝 0) := by
      rw [CircleAvg.circleAvg_eq_of_tendsto ha]
      simpa using (ha.sub (tendsto_const_nhds (x := a))).abs
    filter_upwards [(tendsto_order.1 hlim).2 (η / 3) (by positivity)] with j hj
    exact not_lt.2 hj.le
  rw [ENNReal.tendsto_nhds_zero]
  intro τ hτ
  have hτ3 : 0 < τ / 3 := ENNReal.div_pos hτ.ne' (by norm_num)
  obtain ⟨j, hj1, hj2⟩ := ((ENNReal.tendsto_nhds_zero.1 hcanon (τ / 3) hτ3).and
    (ENNReal.tendsto_nhds_zero.1 hlimit (τ / 3) hτ3)).exists
  have hmid : Tendsto (fun n => P'
      {ω | η / 3 < |CircleAvg.mollAvg (hN n ω) j z r - CircleAvg.mollAvg (h' ω) j z r|})
      atTop (𝓝 0) := by
    refine l1_measure_tendsto_zero (fun n => measurableSet_lt measurable_const
      (((hma j).comp (hNm n)).sub ((hma j).comp hh'm)).abs) ?_
    filter_upwards [hpair (CircleAvg.circBump j z r)] with ω hω
    have hlim : Tendsto (fun n => |CircleAvg.mollAvg (hN n ω) j z r -
        CircleAvg.mollAvg (h' ω) j z r|) atTop (𝓝 0) := by
      simp_rw [CircleAvg.mollAvg_eq]
      simpa using (hω.sub (tendsto_const_nhds (x := h' ω (CircleAvg.circBump j z r)))).abs
    filter_upwards [(tendsto_order.1 hlim).2 (η / 3) (by positivity)] with n hn
    exact not_lt.2 hn.le
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hmid (τ / 3) hτ3] with n hn
  have hsub : {ω | η < |circleAvg (hN n ω) r z - circleAvg (h' ω) r z|} ⊆
      (hN n ⁻¹' {g | η / 3 < |circleAvg g r z - CircleAvg.mollAvg g j z r|}) ∪
        {ω | η / 3 < |CircleAvg.mollAvg (hN n ω) j z r - CircleAvg.mollAvg (h' ω) j z r|} ∪
          {ω | η / 3 < |CircleAvg.mollAvg (h' ω) j z r - circleAvg (h' ω) r z|} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, mem_preimage] at hω ⊢
    by_contra hc
    push Not at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have := abs_sub_le (circleAvg (hN n ω) r z) (CircleAvg.mollAvg (hN n ω) j z r)
      (circleAvg (h' ω) r z)
    have := abs_sub_le (CircleAvg.mollAvg (hN n ω) j z r) (CircleAvg.mollAvg (h' ω) j z r)
      (circleAvg (h' ω) r z)
    linarith
  have hlaw : P' (hN n ⁻¹' {g | η / 3 < |circleAvg g r z - CircleAvg.mollAvg g j z r|}) =
      normGFFLaw {g | η / 3 < |circleAvg g r z - CircleAvg.mollAvg g j z r|} := by
    rw [← hNlaw n, Measure.map_apply (hNm n)
      (measurableSet_lt measurable_const (hca.sub (hma j)).abs :
        MeasurableSet {g : DistC | η / 3 < |circleAvg g r z - CircleAvg.mollAvg g j z r|})]
  calc P' {ω | η < |circleAvg (hN n ω) r z - circleAvg (h' ω) r z|}
      ≤ P' ((hN n ⁻¹' {g | η / 3 < |circleAvg g r z - CircleAvg.mollAvg g j z r|}) ∪
        {ω | η / 3 < |CircleAvg.mollAvg (hN n ω) j z r - CircleAvg.mollAvg (h' ω) j z r|} ∪
          {ω | η / 3 < |CircleAvg.mollAvg (h' ω) j z r - circleAvg (h' ω) r z|}) :=
        measure_mono hsub
    _ ≤ τ / 3 + τ / 3 + τ / 3 := by
      refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
        (add_le_add (hlaw ▸ hj1) hn)) hj2)
    _ = τ := ENNReal.add_thirds τ

 

theorem l1_annulusEvent_of_frequently (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell)
    (hcov : l1Shell ⊆ ⋃ i ∈ q, ball i (1 / 128)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (r : Set.Ioi (0 : ℝ))
    (hκ : Tendsto (fun n => (r : ℝ) *
      (m ⟨(e n : ℝ) / r, Set.mem_Ioi.mpr (div_pos (e n).2 r.2)⟩ : ℝ) / (m (e n) : ℝ)) atTop
      (𝓝 (c r : ℝ)))
    {Ch : ℝ} (hCh : 0 < Ch) (z : ℂ) (hn : ℕ → DistC) (h₀ : DistC) (Lω : LSCMetric)
    (hG : Tendsto (fun n => PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hn n))) atTop
      (𝓝 Lω))
    (hfreq : ∃ᶠ n in atTop, l1HeatGood ξ (m (e n))
      (m ⟨(e n : ℝ) / r, Set.mem_Ioi.mpr (div_pos (e n).2 r.2)⟩) (V (e n) (hn n)) q z r Ch
        (circleAvg (hn n) r z) ∧ |circleAvg (hn n) r z - circleAvg h₀ r z| ≤ 1) :
    ENNReal.ofReal ((c r : ℝ) / (16 * Ch * Real.exp ξ + 1) *
        Real.exp (ξ * circleAvg h₀ r z)) < acrossDist Lω (innerAnnulus z r r.2) ∧
      aroundDist Lω (outerAnnulus z r r.2) <
        ENNReal.ofReal ((16 * Ch * Real.exp ξ + 1) * (c r : ℝ) *
          Real.exp (ξ * circleAvg h₀ r z)) := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  set H : ℝ := circleAvg h₀ r z
  set cr : ℝ := (c r : ℝ) with hcr
  have hcr0 : 0 < cr := (c r).2
  set Ct : ℝ := 16 * Ch * Real.exp ξ + 1 with hCt
  have heξ := Real.exp_pos (ξ : ℝ)
  have hCt0 : 0 < Ct := by positivity
  set κ : ℕ → ℝ := fun n => (r : ℝ) *
      (m ⟨(e n : ℝ) / r, Set.mem_Ioi.mpr (div_pos (e n).2 r.2)⟩ : ℝ) / (m (e n) : ℝ) with hκdef
  have hev : ∀ᶠ n in atTop, cr / 2 ≤ κ n ∧ κ n ≤ 2 * cr := by
    have h1 := (tendsto_order.1 hκ).1 (cr / 2) (by linarith)
    have h2 := (tendsto_order.1 hκ).2 (2 * cr) (by linarith)
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨hn1.le, hn2.le⟩
  have hfr := hfreq.and_eventually hev
  refine ⟨?_, ?_⟩
  · 
    have h1 : ∃ᶠ n in atTop, ENNReal.ofReal (Ch⁻¹ * (cr / 2) * Real.exp (ξ * (H - 1))) ≤
        (⨅ i ∈ q, l1AcrossCost ξ (m (e n)) (V (e n) (hn n)) z r i) := by
      refine hfr.mono fun n hn' => ?_
      obtain ⟨⟨hg, hcl⟩, hκ1, -⟩ := hn'
      refine le_iInf₂ fun i hi => ?_
      refine le_trans ?_ (hg.1 i hi).le
      apply ENNReal.ofReal_le_ofReal
      have hc1 : H - 1 ≤ circleAvg (hn n) r z := by
        have := (abs_le.1 hcl).1; linarith
      have he1 : Real.exp (ξ * (H - 1)) ≤ Real.exp (ξ * circleAvg (hn n) r z) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hc1 hξ.le)
      have hCi : 0 < Ch⁻¹ := inv_pos.2 hCh
      have hκ0 : 0 ≤ κ n := le_trans (by positivity) hκ1
      exact mul_le_mul (mul_le_mul_of_nonneg_left hκ1 hCi.le) he1 (Real.exp_pos _).le
        (mul_nonneg hCi.le hκ0)
    have h2 : ENNReal.ofReal (Ch⁻¹ * (cr / 2) * Real.exp (ξ * (H - 1))) ≤
        limsup (fun n => (⨅ i ∈ q, l1AcrossCost ξ (m (e n)) (V (e n) (hn n)) z r i)) atTop :=
      Filter.le_limsup_of_frequently_le' h1
    have h3 := l1_across_limsup_le hG ξ (fun n => m (e n)) (fun n => V (e n) (hn n))
      (fun n => rfl) q hq hcov z r.2
    refine lt_of_lt_of_le ?_ (h2.trans h3)
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hexp : Real.exp (ξ * (H - 1)) = Real.exp (ξ * H) * (Real.exp ξ)⁻¹ := by
      rw [show (ξ : ℝ) * (H - 1) = ξ * H + -ξ by ring, Real.exp_add, Real.exp_neg]
    rw [hexp]
    have hX := Real.exp_pos (ξ * H)
    rw [div_mul_eq_mul_div, div_lt_iff₀ hCt0]
    have : Ch⁻¹ * (cr / 2) * (Real.exp (↑ξ * H) * (Real.exp ↑ξ)⁻¹) * Ct =
        cr * Real.exp (ξ * H) * ((Ch⁻¹ * (Real.exp ξ)⁻¹ / 2) * Ct) := by ring
    rw [this]
    have hbig : 1 < (Ch⁻¹ * (Real.exp ξ)⁻¹ / 2) * Ct := by
      rw [hCt]
      have : Ch⁻¹ * (Real.exp ↑ξ)⁻¹ / 2 * (16 * Ch * Real.exp ↑ξ + 1) =
          8 + Ch⁻¹ * (Real.exp ξ)⁻¹ / 2 := by
        field_simp; ring
      rw [this]
      have : 0 < Ch⁻¹ * (Real.exp ξ)⁻¹ / 2 := by positivity
      linarith
    have hpos : 0 < cr * Real.exp (ξ * H) := by positivity
    nlinarith
  · 
    set M₀ : ℝ := Ch * (2 * cr) * Real.exp (ξ * (H + 1)) with hM₀
    have hM₀pos : 0 < M₀ := by positivity
    have hk : ∀ k : Fin 4, liminf (fun n => l1AroundCost ξ (m (e n)) (V (e n) (hn n)) z r k)
        atTop < ENNReal.ofReal (2 * M₀) := by
      intro k
      refine lt_of_le_of_lt (liminf_le_of_frequently_le' (x := ENNReal.ofReal M₀) ?_) ?_
      · refine hfr.mono fun n hn' => ?_
        obtain ⟨⟨hg, hcl⟩, -, hκ2⟩ := hn'
        refine (hg.2 k).le.trans (ENNReal.ofReal_le_ofReal ?_)
        have hc1 : circleAvg (hn n) r z ≤ H + 1 := by
          have := (abs_le.1 hcl).2; linarith
        have he1 : Real.exp (ξ * circleAvg (hn n) r z) ≤ Real.exp (ξ * (H + 1)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hc1 hξ.le)
        have hκ0 : 0 ≤ κ n := by
          simp only [hκdef]; exact div_nonneg (mul_nonneg r.2.le (m _).2.le) (m _).2.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hκ2 hCh.le) he1 (Real.exp_pos _).le
          (mul_nonneg hCh.le (by positivity))
      · exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    have hA := l1_around_lt_of_liminf hG ξ (fun n => m (e n)) (fun n => V (e n) (hn n))
      (fun n => rfl) z r.2 _ hk
    refine lt_of_lt_of_le hA ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hexp : Real.exp (ξ * (H + 1)) = Real.exp (ξ * H) * Real.exp ξ := by
      rw [show (ξ : ℝ) * (H + 1) = ξ * H + ξ by ring, Real.exp_add]
    rw [hM₀, hexp, hCt]
    have hX := Real.exp_pos (ξ * H)
    nlinarith [mul_pos hcr0 hX]

theorem l1_measurable_countOcc {Ω : Type} [MeasurableSpace Ω] {F : ℕ → Set Ω}
    (hF : ∀ k, MeasurableSet (F k)) (K : ℕ) :
    Measurable (LQGMetric.Blueprint.countOcc F K) := by
  classical
  have e : LQGMetric.Blueprint.countOcc F K =
      fun ω => ∑ k ∈ Finset.Icc 1 K, if ω ∈ F k then 1 else 0 := by
    funext ω
    unfold LQGMetric.Blueprint.countOcc
    rw [Finset.card_filter]
  rw [e]
  exact Finset.measurable_sum _ fun k _ => Measurable.ite (hF k) measurable_const
    measurable_const

 
theorem l1_count_of_frequently {Ω : Type} (E : ℕ → ℕ → Set Ω) (T : ℕ → Set Ω) (J : ℕ)
    (ω : Ω) (x : ℝ)
    (hfreq : ∃ᶠ n in atTop, x ≤ (LQGMetric.Blueprint.countOcc (E n) J ω : ℝ))
    (himp : ∀ k ∈ Finset.Icc 1 J, (∃ᶠ n in atTop, ω ∈ E n k) → ω ∈ T k) :
    x ≤ (LQGMetric.Blueprint.countOcc T J ω : ℝ) := by
  classical
  set S : ℕ → Finset ℕ := fun n => (Finset.Icc 1 J).filter fun k => ω ∈ E n k with hS
  have hcount : ∀ n, LQGMetric.Blueprint.countOcc (E n) J ω = (S n).card := by
    intro n; unfold LQGMetric.Blueprint.countOcc; rfl
  have hmem : ∀ n, S n ∈ (Finset.Icc 1 J).powerset := fun n =>
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  obtain ⟨S₀, -, hS₀⟩ : ∃ S₀ ∈ (Finset.Icc 1 J).powerset,
      ∃ᶠ n in atTop, S n = S₀ ∧ x ≤ (S₀.card : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ᶠ n in atTop, ∀ S₀ ∈ (Finset.Icc 1 J).powerset,
        ¬ (S n = S₀ ∧ x ≤ (S₀.card : ℝ)) := by
      rw [Filter.eventually_all_finset]
      intro S₀ hS₀
      exact (hcon S₀ hS₀).mono fun n hn h => absurd h.2 (not_le.2 (hn h.1))
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hall).exists
    exact hn2 (S n) (hmem n) ⟨rfl, by rw [← hcount]; exact hn1⟩
  obtain ⟨n₀, hn₀, hx⟩ := hS₀.exists
  have hsub : S₀ ⊆ (Finset.Icc 1 J).filter fun k => ω ∈ T k := by
    intro k hk
    have hkJ : k ∈ Finset.Icc 1 J := by
      rw [← hn₀] at hk; exact (Finset.mem_filter.1 hk).1
    refine Finset.mem_filter.2 ⟨hkJ, himp k hkJ ?_⟩
    refine hS₀.mono fun n hn => ?_
    rw [← hn.1] at hk
    exact (Finset.mem_filter.1 hk).2
  calc x ≤ (S₀.card : ℝ) := hx
    _ ≤ (LQGMetric.Blueprint.countOcc T J ω : ℝ) := by
      unfold LQGMetric.Blueprint.countOcc
      exact_mod_cast Finset.card_le_card hsub

end SupercriticalLQGUniqueness.B2.PfeLocal
