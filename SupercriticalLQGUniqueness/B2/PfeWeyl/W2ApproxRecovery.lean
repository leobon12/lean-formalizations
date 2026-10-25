import SupercriticalLQGUniqueness.B2.PfeWeyl.W2Recovery

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

open PfeAxioms

 
theorem nsmul_ofReal_le (m : ℕ) {a b : ℝ} (h : (m : ℝ) * a ≤ b) :
    m • ENNReal.ofReal a ≤ ENNReal.ofReal b := by
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  exact ENNReal.ofReal_le_ofReal h

 
theorem weyl_approx_recovery
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hGlen : ∀ n, (G n).IsLengthSpace)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (M : ℝ) (hfM : ∀ z, |f z| ≤ M) (hfnM : ∀ n z, |fn n z| ≤ M)
    (hDforget : Continuous (euclidForget D))
    (W : ℕ → LSCMetric)
    (hW : ∀ n x y, W n (x, y) = weylScale ξ (fn n) (G n) (x, y))
    (hWforget : ∀ n, Continuous (euclidForget (W n)))
    (hsmall : ∀ k : ℕ,
      SmallAnnulusCosts G D (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    {z w : ℂ} (hzw : weylScale ξ f D (z, w) ≠ ⊤)
    {θ : ℝ} (hθ : 0 < θ) {η : ℝ} (hη : 0 < η) :
    ∃ x y : ℕ → ℂ, Tendsto x atTop (𝓝 z) ∧ Tendsto y atTop (𝓝 w) ∧
      ∀ᶠ n in atTop, W n (x n, y n) ≤
        ENNReal.ofReal (Real.exp (3 * ξ * θ)) *
            (weylScale ξ f D (z, w) + ENNReal.ofReal η) +
          ENNReal.ofReal η * ENNReal.ofReal (Real.exp (ξ * (M + θ + θ)) + 1) := by
  by_cases hzweq : z = w
  · subst hzweq
    refine ⟨fun _ => z, fun _ => z, tendsto_const_nhds, tendsto_const_nhds,
      Eventually.of_forall fun n => ?_⟩
    rw [(W n).isExtMetric.1 z]
    exact zero_le
  
  obtain ⟨P, L, hP, hu, hP0, hPL, hcost⟩ := exists_near_min_weyl_curve D ξ f z w hzw hη
  have hPc := continuousOn_of_isCurve_of_forget D hDforget hP
  set K₀ : Set ℂ := P '' Icc 0 L with hK₀def
  have hK₀ : IsCompact K₀ := isCompact_Icc.image_of_continuousOn hPc
  have hPK : ∀ s ∈ Icc 0 L, P s ∈ K₀ := fun s hs => mem_image_of_mem P hs
  
  obtain ⟨ρ, hρ, c, hc, hfρ, hcacross⟩ := exists_recovery_scales D f hK₀ hθ
  obtain ⟨δ₃, hδ₃, hDosc⟩ := compact_oscillation D f hK₀ hθ
  obtain ⟨c₁, -, hc₁pos, hc₁⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
  have hc₁' : 0 < c₁ := ENNReal.ofReal_pos.1 hc₁pos
  set δ : ℝ := min δ₃ c₁ with hδdef
  have hδ : 0 < δ := lt_min hδ₃ hc₁'
  have hδδ₃ : δ ≤ δ₃ := min_le_left _ _
  have hδc : ENNReal.ofReal δ < c :=
    (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_lt hc₁
  set N : ℕ := ⌈L / (δ / 2)⌉₊ + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hLδ : L / (N : ℝ) ≤ δ / 2 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hNpos]
    have h1 : L / (δ / 2) ≤ (⌈L / (δ / 2)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈L / (δ / 2)⌉₊ : ℝ) ≤ N := by
      simp only [hNdef, Nat.cast_add, Nat.cast_one]
      linarith
    have h3 : L / (δ / 2) ≤ N := h1.trans h2
    rw [div_le_iff₀ (half_pos hδ)] at h3
    linarith
  have hgrid := uniformGrid_props D hP hu hN le_rfl hLδ
  set v : ℕ → ℂ := fun i => P (uniformGrid L N i) with hvdef
  have hvK : ∀ i ≤ N, v i ∈ K₀ := fun i hi => hPK _ (hgrid.2.2.2.1 i hi)
  have hvstep : ∀ i < N, D (v i, v (i + 1)) ≤ ENNReal.ofReal (δ / 2) := fun i hi =>
    (LSCMetric.apply_le_len _ _ (hgrid.1 (Nat.le_succ i))).trans (hgrid.2.2.2.2 i hi)
  have hosc : ∀ u ∈ K₀, ∀ u' ∈ K₀, D (u, u') ≤ ENNReal.ofReal (δ / 2) →
      |f u - f u'| < θ := fun u hu u' hu' huu' =>
    hDosc u hu u' hu' (huu'.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hchain := uniformGrid_weighted_chain_le_cost D ξ hξ f hDforget hosc hP hu hPK
    hN le_rfl hLδ
  
  obtain ⟨N', v', hN'N, hv'0, hv'N, hdist, hpair, hsum⟩ := exists_dedup_chain v N
  have hv'0z : v' 0 = z := by
    rw [hv'0]
    simp only [hvdef]
    rw [hgrid.2.1, hP0]
  have hv'Nw : v' N' = w := by
    rw [hv'N]
    simp only [hvdef]
    rw [hgrid.2.2.1, hPL]
  have hN'pos : 0 < N' := by
    rcases Nat.eq_zero_or_pos N' with h | h
    · subst h
      exact absurd (hv'0z.symm.trans hv'Nw) hzweq
    · exact h
  obtain ⟨M₁, rfl⟩ : ∃ M₁, N' = M₁ + 1 := ⟨N' - 1, by omega⟩
  have hv'K : ∀ j ≤ M₁ + 1, v' j ∈ K₀ := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hj | hj
    · obtain ⟨i, hi, h1, -⟩ := hpair j hj
      rw [h1]
      exact hvK i hi.le
    · rw [hj, hv'Nw, ← hPL]
      exact hPK L ⟨hP.1, le_rfl⟩
  have hv'step : ∀ j < M₁ + 1, D (v' j, v' (j + 1)) ≤ ENNReal.ofReal (δ / 2) := by
    intro j hj
    obtain ⟨i, hi, h1, h2⟩ := hpair j hj
    rw [h1, h2]
    exact hvstep i hi
  
  set η' : ℝ := min (δ / 2) (η / ((M₁ : ℝ) + 1)) with hη'def
  have hM₁pos : (0 : ℝ) < (M₁ : ℝ) + 1 := Nat.cast_add_one_pos M₁
  have hη' : 0 < η' := lt_min (half_pos hδ) (div_pos hη hM₁pos)
  set budget : Fin (M₁ + 1) → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (Real.exp (ξ * (f (v' j) + θ + θ))) *
      (D (v' j, v' (j + 1)) + ENNReal.ofReal η') with hbudget
  have hseg : ∀ j : Fin (M₁ + 1), ∃ x y : ℕ → ℂ,
      Tendsto x atTop (𝓝 (v' j)) ∧ Tendsto y atTop (𝓝 (v' (j + 1))) ∧
      ∀ᶠ n in atTop, ∃ T : BufferedMetricTrace (W n) (univ : Set ℂ),
        T.path T.start = x n ∧ T.path T.stop = y n ∧ T.cost ≤ budget j := by
    intro j
    have hjK := hv'K j j.isLt.le
    refine weyl_segment_recovery hG hGlen hGforget ξ hξ f fn hfn W hW hθ hρ
      (f (v' j) + θ) (hfρ _ hjK) hη' ?_
    calc D (v' j, v' (j + 1)) + ENNReal.ofReal η'
        ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          add_le_add (hv'step j j.isLt) (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
          ring_nf
      _ < c := hδc
      _ ≤ acrossDist D (halfAnnulus (v' j) ρ hρ) := hcacross _ hjK hρ
  choose X Y hX hY hT using hseg
  obtain ⟨Pt, hPt⟩ := select_eventual_traces (E := W) (V := (univ : Set ℂ))
    (fun n j T => T.path T.start = X j n ∧ T.path T.stop = Y j n ∧ T.cost ≤ budget j)
    (fun n _ => constantBufferedTrace (W n) ⟨0, mem_univ _⟩) hT
  
  obtain ⟨k, hk⟩ : ∃ k : ℕ, K₀ ⊆ Metric.closedBall 0 k := by
    obtain ⟨r, hr⟩ := hK₀.isBounded.subset_closedBall 0
    obtain ⟨k, hk⟩ := exists_nat_ge r
    exact ⟨k, hr.trans (Metric.closedBall_subset_closedBall hk)⟩
  have hsmallW : SmallAnnulusCosts W D (Metric.closedBall 0 k) univ := by
    have h : SmallAnnulusCosts W D (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)) :=
      smallAnnulusCosts_weyl ξ hξ fn (hsmall k)
        (fun n p => by simpa only [Prod.mk.eta] using hW n p.1 p.2) M
        (fun n z _ => (abs_le.1 (hfnM n z)).2)
    exact smallAnnulusCosts_mono_right h (subset_univ _)
  
  have hstart : ∀ j : Fin (M₁ + 1),
      Tendsto (fun n => (Pt n j).path (Pt n j).start) atTop (𝓝 (v' j)) := fun j =>
    (hX j).congr' (by filter_upwards [hPt j] with n hn; exact hn.1.symm)
  have hstop : ∀ j : Fin (M₁ + 1),
      Tendsto (fun n => (Pt n j).path (Pt n j).stop) atTop (𝓝 (v' (j + 1))) := fun j =>
    (hY j).congr' (by filter_upwards [hPt j] with n hn; exact hn.2.1.symm)
  have hδb : 0 < η / ((M₁ : ℝ) + 1) := div_pos hη hM₁pos
  have hskel := eventually_buffered_skeleton_bound (G := W) (D := D)
    (K := Metric.closedBall 0 k) (V := (univ : Set ℂ)) hsmallW hWforget M₁ Pt
    (fun i => v' i) (fun i => v' (i + 1)) (fun i => v' (i + 1 + 1))
    (fun i => ⟨hk (hv'K _ (by omega)),
      ⟨v' (i + 1 + 1), (hdist (i + 1) (by omega)).symm,
        (hv'step (i + 1) (by omega)).trans_lt ENNReal.ofReal_lt_top⟩⟩)
    (fun i => hdist i (by omega)) (fun i => (hdist (i + 1) (by omega)).symm)
    (fun i => by simpa only [Fin.val_castSucc] using hstart (Fin.castSucc i))
    (fun i => by simpa only [Fin.val_castSucc] using hstop (Fin.castSucc i))
    (fun i => by simpa only [Fin.val_succ] using hstart i.succ)
    (fun i => by simpa only [Fin.val_succ] using hstop i.succ)
    hδb
  refine ⟨X 0, Y (Fin.last M₁), by simpa only [Fin.val_zero, hv'0z] using hX 0,
    by simpa only [Fin.val_last, hv'Nw] using hY (Fin.last M₁), ?_⟩
  filter_upwards [hskel, Filter.eventually_all.2 hPt] with n hsk hall
  have hamb : W n (X 0 n, Y (Fin.last M₁) n) ≤
      (W n).internal univ ((Pt n 0).first, (Pt n (Fin.last M₁)).last) := by
    have h := LSCMetric.edist_le_internal (W n) univ
      ((Pt n 0).first, (Pt n (Fin.last M₁)).last)
    rw [← (hall 0).1, ← (hall (Fin.last M₁)).2.1]
    exact h
  have hbud := finiteBridgeBudget_le_fin_sum M₁ (ENNReal.ofReal (η / ((M₁ : ℝ) + 1)))
    (Pt n) budget (fun j => (hall j).2.2)
  refine hamb.trans (hsk.trans (hbud.trans ?_))
  
  set E3 : ℝ≥0∞ := ENNReal.ofReal (Real.exp (3 * ξ * θ)) with hE3
  set eM : ℝ := Real.exp (ξ * (M + θ + θ)) with heM
  have hsplit : ∀ j : Fin (M₁ + 1), budget j =
      E3 * (chainWeightMinus ξ f θ (v' j) * D (v' j, v' (j + 1))) +
        ENNReal.ofReal η' *
          ENNReal.ofReal (Real.exp (ξ * (f (v' j) + θ + θ))) := by
    intro j
    simp only [hbudget, chainWeightMinus]
    rw [mul_add, ofReal_exp_shift3]
    ring
  have hfirst : (∑ j : Fin (M₁ + 1), chainWeightMinus ξ f θ (v' j) * D (v' j, v' (j + 1)))
      ≤ weylScale ξ f D (z, w) + ENNReal.ofReal η := by
    rw [Fin.sum_univ_eq_sum_range (fun j => chainWeightMinus ξ f θ (v' j) *
      D (v' j, v' (j + 1))) (M₁ + 1)]
    exact ((hsum fun x y => chainWeightMinus ξ f θ x * D (x, y)).trans hchain).trans
      hcost.le
  have hsecond : (∑ j : Fin (M₁ + 1), ENNReal.ofReal η' *
      ENNReal.ofReal (Real.exp (ξ * (f (v' j) + θ + θ)))) ≤
        ENNReal.ofReal η * ENNReal.ofReal eM := by
    calc (∑ j : Fin (M₁ + 1), ENNReal.ofReal η' *
          ENNReal.ofReal (Real.exp (ξ * (f (v' j) + θ + θ))))
        ≤ ∑ _j : Fin (M₁ + 1), ENNReal.ofReal η' * ENNReal.ofReal eM := by
          refine Finset.sum_le_sum fun j _ => ?_
          gcongr
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
            (by linarith [(abs_le.1 (hfM (v' j))).2]) hξ)
      _ = (M₁ + 1) • (ENNReal.ofReal η' * ENNReal.ofReal eM) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = ((M₁ + 1) • ENNReal.ofReal η') * ENNReal.ofReal eM := by
          rw [smul_mul_assoc]
      _ ≤ ENNReal.ofReal η * ENNReal.ofReal eM := by
          gcongr
          refine nsmul_ofReal_le (M₁ + 1) ?_
          have h1 : η' ≤ η / ((M₁ : ℝ) + 1) := min_le_right _ _
          rw [le_div_iff₀ hM₁pos] at h1
          push_cast
          linarith
  have hthird : M₁ • ENNReal.ofReal (η / ((M₁ : ℝ) + 1)) ≤ ENNReal.ofReal η := by
    refine nsmul_ofReal_le M₁ ?_
    rw [mul_div_assoc']
    rw [div_le_iff₀ hM₁pos]
    nlinarith
  calc (∑ j : Fin (M₁ + 1), budget j) + M₁ • ENNReal.ofReal (η / ((M₁ : ℝ) + 1))
      = E3 * (∑ j : Fin (M₁ + 1), chainWeightMinus ξ f θ (v' j) * D (v' j, v' (j + 1))) +
          (∑ j : Fin (M₁ + 1), ENNReal.ofReal η' *
            ENNReal.ofReal (Real.exp (ξ * (f (v' j) + θ + θ)))) +
          M₁ • ENNReal.ofReal (η / ((M₁ : ℝ) + 1)) := by
        rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ E3 * (weylScale ξ f D (z, w) + ENNReal.ofReal η) +
          ENNReal.ofReal η * ENNReal.ofReal eM + ENNReal.ofReal η := by
        gcongr
    _ = E3 * (weylScale ξ f D (z, w) + ENNReal.ofReal η) +
          ENNReal.ofReal η * ENNReal.ofReal (eM + 1) := by
        rw [ENNReal.ofReal_add (Real.exp_pos _).le zero_le_one, ENNReal.ofReal_one]
        ring

end SupercriticalLQGUniqueness.B2.PfeWeyl
