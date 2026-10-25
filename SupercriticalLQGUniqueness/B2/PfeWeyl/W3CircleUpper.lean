import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CircleChain
import SupercriticalLQGUniqueness.B2.PfeWeyl.W2ApproxRecovery

 






















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

open PfeAxioms

 
theorem ofReal_exp_shift4 (ξ a θ : ℝ) :
    ENNReal.ofReal (Real.exp (ξ * (a + θ + θ + θ))) =
      ENNReal.ofReal (Real.exp (4 * ξ * θ)) * ENNReal.ofReal (Real.exp (ξ * (a - θ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

 
theorem weyl_rationalCircle_upper
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hGlen : ∀ n, (G n).IsLengthSpace)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (M : ℝ) (hfM : ∀ z, |f z| ≤ M) (hfnM : ∀ n z, |fn n z| ≤ M)
    (hDlen : D.IsLengthSpace) (hDforget : Continuous (euclidForget D))
    (W : ℕ → LSCMetric)
    (hW : ∀ n x y, W n (x, y) = weylScale ξ (fn n) (G n) (x, y))
    (hWforget : ∀ n, Continuous (euclidForget (W n)))
    (hsmall : ∀ k : ℕ,
      SmallAnnulusCosts G D (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (hcirc : ∀ O O' : Set ℂ, B2.Iface.IsRationalCircle O → B2.Iface.IsRationalCircle O' →
      Tendsto (fun n => B2.Iface.setDistance (G n) O O') atTop
        (𝓝 (B2.Iface.setDistance D O O')))
    {O O' : Set ℂ} (hO : B2.Iface.IsRationalCircle O) (hO' : B2.Iface.IsRationalCircle O')
    {θ : ℝ} (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε)
    (hfin : B2.Iface.setDistance (weylScale ξ f D) O O' ≠ ⊤) :
    ∀ᶠ n in atTop, B2.Iface.setDistance (W n) O O' ≤
      ENNReal.ofReal (Real.exp (4 * ξ * θ)) *
          (B2.Iface.setDistance (weylScale ξ f D) O O' + ENNReal.ofReal ε +
            ENNReal.ofReal ε) +
        ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (ξ * (M + θ + θ + θ)) + 1) := by
  set S := B2.Iface.setDistance (weylScale ξ f D) O O' with hSdef
  have hOc : IsClosed O := (isCompact_of_isRationalCircle hO).isClosed
  have hO'c : IsClosed O' := (isCompact_of_isRationalCircle hO').isClosed
  by_cases hmeet : (O ∩ O').Nonempty
  · obtain ⟨p, hpO, hpO'⟩ := hmeet
    refine Eventually.of_forall fun n => ?_
    have h0 : B2.Iface.setDistance (W n) O O' = 0 := by
      refine le_antisymm ?_ bot_le
      calc B2.Iface.setDistance (W n) O O' ≤ W n (p, p) :=
            iInf₂_le_of_le p hpO (iInf₂_le p hpO')
        _ = 0 := (W n).isExtMetric.1 p
    rw [h0]
    exact bot_le
  have hdisj : Disjoint O O' :=
    Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hmeet)
  
  have hSlt : S < S + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hfin (ENNReal.ofReal_pos.2 hε).ne'
  have hSlt' : (⨅ u ∈ O, ⨅ w ∈ O', weylScale ξ f D (u, w)) < S + ENNReal.ofReal ε := hSlt
  simp only [iInf_lt_iff] at hSlt'
  obtain ⟨x, hx, y, hy, hxy⟩ := hSlt'
  have hxyfin : weylScale ξ f D (x, y) ≠ ⊤ :=
    (hxy.trans (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hfin, ENNReal.ofReal_lt_top⟩)).ne
  obtain ⟨P, L, t₀, t₁, hP, hu, ht₀, ht₀₁, ht₁, hP₀, hP₁, hint, hcost⟩ :=
    exists_circle_curve D hDforget ξ f hOc hO'c hdisj hx hy hxyfin hε
  have hPc := continuousOn_of_isCurve_of_forget D hDforget hP
  set K₀ : Set ℂ := P '' Icc 0 L with hK₀def
  have hK₀ : IsCompact K₀ := isCompact_Icc.image_of_continuousOn hPc
  
  obtain ⟨ρ₀, hρ₀, c, hc, hfρ, hcacross⟩ := exists_recovery_scales D f hK₀ hθ
  obtain ⟨δ₃, hδ₃, hDosc⟩ := compact_oscillation D f hK₀ hθ
  obtain ⟨c₁, -, hc₁pos, hc₁⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
  have hc₁' : 0 < c₁ := ENNReal.ofReal_pos.1 hc₁pos
  set δ : ℝ := min δ₃ c₁ with hδdef
  have hδ : 0 < δ := lt_min hδ₃ hc₁'
  have hδδ₃ : δ ≤ δ₃ := min_le_left _ _
  have hδc : ENNReal.ofReal δ < c :=
    (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_lt hc₁
  
  have hosc : ∀ u ∈ K₀, ∀ u' ∈ K₀, D (u, u') ≤ ENNReal.ofReal (δ / 2) →
      |f u - f u'| < θ := fun u hu u' hu' h =>
    hDosc u hu u' hu' (h.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  obtain ⟨N, v, hN2, hv0, hvN, hvint, hvdist, hvK, hvstep, hvsum⟩ :=
    exists_circle_chain_of_curve D hDforget ξ hξ f hdisj hP hu ht₀ ht₀₁ ht₁ hP₀ hP₁ hint
      (half_pos hδ) hosc
  obtain ⟨M₁, rfl⟩ : ∃ M₁, N = M₁ + 1 := ⟨N - 1, by omega⟩
  have hM₁ : 1 ≤ M₁ := by omega
  have hvfin : ∀ j < M₁ + 1, D (v j, v (j + 1)) < ⊤ := fun j hj =>
    (hvstep j hj).trans_lt ENNReal.ofReal_lt_top
  
  have hOne : O.Nonempty := ⟨x, hx⟩
  have hO'ne : O'.Nonempty := ⟨y, hy⟩
  obtain ⟨g₁, hg₁, hg₁le⟩ := exists_pos_le_finset (Finset.range (M₁ + 1))
    (fun j => dist (v j) (v (j + 1)))
    (fun j hj => dist_pos.2 (hvdist j (Finset.mem_range.1 hj)))
  obtain ⟨g₂, hg₂, hg₂le⟩ := exists_pos_le_finset (Finset.Ioo 0 (M₁ + 1))
    (fun j => Metric.infDist (v j) O)
    (fun j hj => (hOc.notMem_iff_infDist_pos hOne).1
      (hvint j (Finset.mem_Ioo.1 hj).1 (Finset.mem_Ioo.1 hj).2).1)
  obtain ⟨g₃, hg₃, hg₃le⟩ := exists_pos_le_finset (Finset.Ioo 0 (M₁ + 1))
    (fun j => Metric.infDist (v j) O')
    (fun j hj => (hO'c.notMem_iff_infDist_pos hO'ne).1
      (hvint j (Finset.mem_Ioo.1 hj).1 (Finset.mem_Ioo.1 hj).2).2)
  set ρs : ℝ := min (ρ₀ / 4) (min g₁ (min g₂ g₃) / 4) with hρsdef
  have hρs : 0 < ρs := lt_min (by linarith) (by
    have := lt_min hg₁ (lt_min hg₂ hg₃)
    linarith)
  have hρsρ₀ : 4 * ρs ≤ ρ₀ := by
    have := min_le_left (ρ₀ / 4) (min g₁ (min g₂ g₃) / 4)
    linarith
  have hρsg₁ : 4 * ρs ≤ g₁ := by
    have h1 := min_le_right (ρ₀ / 4) (min g₁ (min g₂ g₃) / 4)
    have h2 := min_le_left g₁ (min g₂ g₃)
    linarith
  have hρsg₂ : 4 * ρs ≤ g₂ := by
    have h1 := min_le_right (ρ₀ / 4) (min g₁ (min g₂ g₃) / 4)
    have h2 := min_le_right g₁ (min g₂ g₃)
    have h3 := min_le_left g₂ g₃
    linarith
  have hρsg₃ : 4 * ρs ≤ g₃ := by
    have h1 := min_le_right (ρ₀ / 4) (min g₁ (min g₂ g₃) / 4)
    have h2 := min_le_right g₁ (min g₂ g₃)
    have h3 := min_le_right g₂ g₃
    linarith
  have hadj : ∀ j < M₁ + 1, 4 * ρs ≤ dist (v j) (v (j + 1)) := fun j hj =>
    hρsg₁.trans (hg₁le j (Finset.mem_range.2 hj))
  have hfarO : ∀ j, 0 < j → j < M₁ + 1 → ∀ p ∈ O, 4 * ρs ≤ dist (v j) p := fun j h0 h1 p hp =>
    (hρsg₂.trans (hg₂le j (Finset.mem_Ioo.2 ⟨h0, h1⟩))).trans
      (Metric.infDist_le_dist_of_mem hp)
  have hfarO' : ∀ j, 0 < j → j < M₁ + 1 → ∀ p ∈ O', 4 * ρs ≤ dist (v j) p :=
    fun j h0 h1 p hp =>
    (hρsg₃.trans (hg₃le j (Finset.mem_Ioo.2 ⟨h0, h1⟩))).trans
      (Metric.infDist_le_dist_of_mem hp)
  
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
  have hM₁pos : (0 : ℝ) < (M₁ : ℝ) + 1 := Nat.cast_add_one_pos M₁
  set δb : ℝ := ε / ((M₁ : ℝ) + 1) with hδbdef
  have hδb : 0 < δb := div_pos hε hM₁pos
  have hAex : ∀ j : ℕ, 1 ≤ j → j ≤ M₁ → ∃ A : EuclideanAnnulus,
      IsRationalDoubleAnnulus A ∧ dist (v j) A.center < A.innerRadius ∧
      A.outerRadius < ρs ∧ ∀ᶠ n in atTop, aroundDist (W n) A < ENNReal.ofReal δb := by
    intro j hj1 hjM
    obtain ⟨A, h1, h2, h3, -, h5⟩ := hsmallW (v j) (hk (hvK j (by omega)))
      ⟨v (j + 1), (hvdist j (by omega)).symm, hvfin j (by omega)⟩ δb hδb ρs hρs
    exact ⟨A, h1, h2, h3, h5⟩
  have : Nonempty EuclideanAnnulus := ⟨⟨(0, (1, 2)), one_pos, one_lt_two⟩⟩
  choose! A hArat hAin hAout hAev using hAex
  
  set circ : ℕ → Set ℂ := fun j =>
    if j = 0 then O else if j ≤ M₁ then (A j).innerBoundary else O' with hcircdef
  have hcirc0 : circ 0 = O := by simp [hcircdef]
  have hcircN : circ (M₁ + 1) = O' := by simp [hcircdef]
  have hcircj : ∀ j, 1 ≤ j → j ≤ M₁ → circ j = (A j).innerBoundary := by
    intro j h1 h2
    simp [hcircdef, show j ≠ 0 by omega, h2]
  have hrad : ∀ j, 1 ≤ j → j ≤ M₁ → (A j).innerRadius < ρs := fun j h1 h2 =>
    (A j).innerRadius_lt_outerRadius.trans (hAout j h1 h2)
  have hcen : ∀ j, 1 ≤ j → j ≤ M₁ → dist (A j).center (v j) < ρs := fun j h1 h2 => by
    rw [dist_comm]
    exact (hAin j h1 h2).trans (hrad j h1 h2)
  have hcircnear : ∀ j, 1 ≤ j → j ≤ M₁ → ∀ p ∈ circ j, dist p (v j) < 2 * ρs := by
    intro j h1 h2 p hp
    rw [hcircj j h1 h2] at hp
    have hp' : dist p (A j).center = (A j).innerRadius := hp
    have := dist_triangle p (A j).center (v j)
    linarith [hcen j h1 h2, hrad j h1 h2]
  have hballnear : ∀ j, 1 ≤ j → j ≤ M₁ → ∀ p ∈ Metric.ball (A j).center (A j).outerRadius,
      dist p (v j) < 2 * ρs := by
    intro j h1 h2 p hp
    have hp' := Metric.mem_ball.1 hp
    have := dist_triangle p (A j).center (v j)
    linarith [hcen j h1 h2, hAout j h1 h2]
  
  have hfarvert : ∀ j, 1 ≤ j → j ≤ M₁ → ∀ i, (i + 1 = j ∨ i = j + 1) →
      v i ∉ Metric.ball (A j).center (A j).outerRadius := by
    intro j h1 h2 i hi hball
    have hd := hballnear j h1 h2 _ hball
    rcases hi with hi | hi
    · have := hadj i (by omega)
      rw [hi] at this
      linarith
    · have := hadj j (by omega)
      rw [← hi] at this
      rw [dist_comm] at hd
      linarith
  have hfarcirc : ∀ j, 1 ≤ j → j ≤ M₁ → ∀ i, (i + 1 = j ∨ i = j + 1) → i ≤ M₁ + 1 →
      ∀ p ∈ circ i, p ∉ Metric.ball (A j).center (A j).outerRadius := by
    intro j h1 h2 i hi hiM p hp hball
    have hd := hballnear j h1 h2 _ hball
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      rw [hcirc0] at hp
      have := hfarO j (by omega) (by omega) p hp
      rw [dist_comm] at this
      linarith
    rcases Nat.lt_or_eq_of_le hiM with hiM' | hiM'
    · have hpi := hcircnear i hi0 (by omega) p hp
      have hvv : 4 * ρs ≤ dist (v i) (v j) := by
        rcases hi with hi | hi
        · have := hadj i (by omega)
          rwa [hi] at this
        · have := hadj j (by omega)
          rw [← hi, dist_comm] at this
          exact this
      have := dist_triangle (v i) p (v j)
      rw [dist_comm (v i) p] at this
      linarith
    · subst hiM'
      rw [hcircN] at hp
      have := hfarO' j (by omega) (by omega) p hp
      rw [dist_comm] at this
      linarith
  have hratcirc : ∀ j ≤ M₁ + 1, B2.Iface.IsRationalCircle (circ j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [hcirc0]
      exact hO
    rcases Nat.lt_or_eq_of_le hj with hj' | hj'
    · rw [hcircj j h0 (by omega)]
      exact isRationalCircle_innerBoundary (hArat j h0 (by omega))
    · subst hj'
      rw [hcircN]
      exact hO'
  
  set ηs : ℝ := min (δ / 2) (ε / ((M₁ : ℝ) + 1)) with hηsdef
  have hηs : 0 < ηs := lt_min (half_pos hδ) (div_pos hε hM₁pos)
  have hDcirc : ∀ j ≤ M₁, B2.Iface.setDistance D (circ j) (circ (j + 1)) <
      D (v j, v (j + 1)) + ENNReal.ofReal ηs := by
    intro j hj
    obtain ⟨Q, Lq, hQ, hQu, hQ0, hQL, hQlen⟩ :=
      exists_near_min_ordinary_curve D hDlen (v j) (v (j + 1)) (hvfin j (by omega)) hηs
    have hQc := continuousOn_of_isCurve_of_forget D hDforget hQ
    have hLq : 0 ≤ Lq := hQ.1
    obtain ⟨s, hs, hQs⟩ : ∃ s ∈ Icc 0 Lq, Q s ∈ circ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        exact ⟨0, ⟨le_rfl, hLq⟩, by rw [hQ0, hcirc0]; exact hv0⟩
      · have hf : ContinuousOn (fun t => dist (Q t) (A j).center) (Icc 0 Lq) :=
          continuous_dist.comp_continuousOn (hQc.prodMk continuousOn_const)
        have hstart : dist (Q 0) (A j).center ≤ (A j).innerRadius := by
          rw [hQ0]
          exact (hAin j h0 hj).le
        have hend : (A j).innerRadius ≤ dist (Q Lq) (A j).center := by
          rw [hQL]
          have := hfarvert j h0 hj (j + 1) (Or.inr rfl)
          rw [Metric.mem_ball, not_lt] at this
          exact (A j).innerRadius_lt_outerRadius.le.trans this
        obtain ⟨s, hs, hsd⟩ := intermediate_value_Icc hLq hf ⟨hstart, hend⟩
        refine ⟨s, hs, ?_⟩
        rw [hcircj j h0 hj]
        exact hsd
    obtain ⟨t, ht, hQt⟩ : ∃ t ∈ Icc s Lq, Q t ∈ circ (j + 1) := by
      rcases Nat.lt_or_eq_of_le hj with hj' | hj'
      · have h1 : 1 ≤ j + 1 := by omega
        have hf : ContinuousOn (fun t => dist (Q t) (A (j + 1)).center) (Icc s Lq) :=
          continuous_dist.comp_continuousOn
            ((hQc.mono (Icc_subset_Icc hs.1 le_rfl)).prodMk continuousOn_const)
        have hstart : (A (j + 1)).innerRadius ≤ dist (Q s) (A (j + 1)).center := by
          have := hfarcirc (j + 1) h1 hj' j (Or.inl rfl) (by omega) (Q s) hQs
          rw [Metric.mem_ball, not_lt] at this
          exact (A (j + 1)).innerRadius_lt_outerRadius.le.trans this
        have hend : dist (Q Lq) (A (j + 1)).center ≤ (A (j + 1)).innerRadius := by
          rw [hQL]
          exact (hAin (j + 1) h1 hj').le
        obtain ⟨t, ht, htd⟩ := intermediate_value_Icc' hs.2 hf ⟨hend, hstart⟩
        refine ⟨t, ht, ?_⟩
        rw [hcircj (j + 1) h1 hj']
        exact htd
      · subst hj'
        exact ⟨Lq, ⟨hs.2, le_rfl⟩, by rw [hQL, hcircN]; exact hvN⟩
    calc B2.Iface.setDistance D (circ j) (circ (j + 1)) ≤ D (Q s, Q t) :=
          iInf₂_le_of_le (Q s) hQs (iInf₂_le (Q t) hQt)
      _ ≤ D.len Q s t := LSCMetric.apply_le_len D Q ht.1
      _ ≤ D.len Q 0 Lq := len_mono_Icc D Q hs.1 ht.2
      _ < _ := hQlen
  
  set budget : Fin (M₁ + 1) → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (Real.exp (ξ * (f (v j) + θ + θ + θ))) *
      (D (v j, v (j + 1)) + ENNReal.ofReal ηs) with hbudget
  have hBlt : ∀ j < M₁ + 1, ∀ a ∈ K₀, D (v j, v (j + 1)) + ENNReal.ofReal ηs <
      acrossDist D (halfAnnulus a ρ₀ hρ₀) := by
    intro j hj a ha
    calc D (v j, v (j + 1)) + ENNReal.ofReal ηs
        ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          add_le_add (hvstep j hj) (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
          ring_nf
      _ < c := hδc
      _ ≤ _ := hcacross a ha hρ₀
  have hseg : ∀ j : Fin (M₁ + 1), ∀ᶠ n in atTop,
      ∃ T : BufferedMetricTrace (W n) (univ : Set ℂ),
        T.path T.start ∈ circ (j : ℕ) ∧ T.path T.stop ∈ circ ((j : ℕ) + 1) ∧
          T.cost ≤ budget j := by
    intro j
    have hjlt : (j : ℕ) < M₁ + 1 := j.isLt
    have hrat1 := hratcirc j hjlt.le
    have hrat2 := hratcirc (j + 1) (by omega)
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
    · 
      have h1K : v 1 ∈ K₀ := hvK 1 (by omega)
      have hanchor : circ ((j : ℕ) + 1) ⊆ Metric.closedBall (v 1) (ρ₀ / 2) := by
        intro p hp
        rw [h0] at hp
        have := hcircnear 1 le_rfl hM₁ p (by simpa using hp)
        rw [Metric.mem_closedBall]
        linarith
      have hseg0 := weyl_circle_segment hG hGlen hGforget ξ hξ f fn hfn W hW hθ hρ₀
        (f (v 1) + θ) (hfρ (v 1) h1K) (hcirc _ _ hrat1 hrat2)
        (hDcirc j (by omega)) (hBlt j hjlt (v 1) h1K) (Or.inr hanchor)
      filter_upwards [hseg0] with n ⟨T, hT1, hT2, hT3⟩
      refine ⟨T, hT1, hT2, hT3.trans ?_⟩
      simp only [hbudget]
      gcongr ENNReal.ofReal (Real.exp (ξ * ?_)) * _
      have hv01 : D (v 0, v 1) ≤ ENNReal.ofReal (δ / 2) := hvstep 0 (by omega)
      have := hosc (v 0) (hvK 0 (by omega)) (v 1) h1K hv01
      rw [h0]
      linarith [(abs_sub_lt_iff.1 this).2]
    · have hjK : v j ∈ K₀ := hvK j hjlt.le
      have hanchor : circ (j : ℕ) ⊆ Metric.closedBall (v j) (ρ₀ / 2) := by
        intro p hp
        have := hcircnear j h0 (by omega) p hp
        rw [Metric.mem_closedBall]
        linarith
      have hsegj := weyl_circle_segment hG hGlen hGforget ξ hξ f fn hfn W hW hθ hρ₀
        (f (v j) + θ) (hfρ (v j) hjK) (hcirc _ _ hrat1 hrat2)
        (hDcirc j (by omega)) (hBlt j hjlt (v j) hjK) (Or.inl hanchor)
      filter_upwards [hsegj] with n ⟨T, hT1, hT2, hT3⟩
      refine ⟨T, hT1, hT2, hT3.trans ?_⟩
      simp only [hbudget]
      gcongr ENNReal.ofReal (Real.exp (ξ * ?_)) * _
      linarith
  obtain ⟨Pt, hPt⟩ := select_eventual_traces (E := W) (V := (univ : Set ℂ))
    (ι := Fin (M₁ + 1))
    (fun n (j : Fin (M₁ + 1)) T => T.path T.start ∈ circ (j : ℕ) ∧
      T.path T.stop ∈ circ ((j : ℕ) + 1) ∧ T.cost ≤ budget j)
    (fun n _ => constantBufferedTrace (W n) ⟨0, mem_univ _⟩) hseg
  
  have hbridge : ∀ i : Fin M₁, ∀ᶠ n in atTop, ∃ R : BufferedMetricTrace (W n) (univ : Set ℂ),
      ((Pt n (Fin.castSucc i)).trace ∩ R.trace).Nonempty ∧
      (R.trace ∩ (Pt n i.succ).trace).Nonempty ∧ R.cost ≤ ENNReal.ofReal δb := by
    intro i
    have hj1 : 1 ≤ (i : ℕ) + 1 := by omega
    have hjM : (i : ℕ) + 1 ≤ M₁ := i.isLt
    filter_upwards [hPt (Fin.castSucc i), hPt i.succ, hAev ((i : ℕ) + 1) hj1 hjM]
      with n hP1 hP2 hAround
    simp only [Fin.val_castSucc, Fin.val_succ] at hP1 hP2
    have hPb : (Pt n (Fin.castSucc i)).path (Pt n (Fin.castSucc i)).stop ∈
        Metric.closedBall (A ((i : ℕ) + 1)).center (A ((i : ℕ) + 1)).innerRadius := by
      have h := hP1.2.1
      rw [hcircj _ hj1 hjM] at h
      exact Metric.sphere_subset_closedBall h
    have hQc : (Pt n i.succ).path (Pt n i.succ).start ∈
        Metric.closedBall (A ((i : ℕ) + 1)).center (A ((i : ℕ) + 1)).innerRadius := by
      have h := hP2.1
      rw [hcircj _ hj1 hjM] at h
      exact Metric.sphere_subset_closedBall h
    have hPa := hfarcirc ((i : ℕ) + 1) hj1 hjM i (Or.inl rfl) (by omega) _ hP1.1
    have hQd := hfarcirc ((i : ℕ) + 1) hj1 hjM ((i : ℕ) + 1 + 1) (Or.inr rfl) (by omega) _
      hP2.2.1
    obtain ⟨R, hR1, hR2, hR3⟩ := exists_buffered_annular_bridge (W n) (hWforget n)
      (A ((i : ℕ) + 1)) (subset_univ _) (Pt n (Fin.castSucc i)) (Pt n i.succ)
      hPa hPb hQc hQd hAround
    exact ⟨R, hR1, hR2, hR3.le⟩
  
  have hchainW := eventually_finite_buffered_bridge_bound M₁ (ENNReal.ofReal δb) Pt hbridge
  filter_upwards [hchainW, Filter.eventually_all.2 hPt] with n hch hall
  have hfirstO : (Pt n 0).path (Pt n 0).start ∈ O := by
    have := (hall 0).1
    rwa [Fin.val_zero, hcirc0] at this
  have hlastO' : (Pt n (Fin.last M₁)).path (Pt n (Fin.last M₁)).stop ∈ O' := by
    have := (hall (Fin.last M₁)).2.1
    rwa [Fin.val_last, hcircN] at this
  have hsetd : B2.Iface.setDistance (W n) O O' ≤
      W n ((Pt n 0).path (Pt n 0).start,
        (Pt n (Fin.last M₁)).path (Pt n (Fin.last M₁)).stop) :=
    iInf₂_le_of_le _ hfirstO (iInf₂_le _ hlastO')
  have hamb := LSCMetric.edist_le_internal (W n) univ
    ((Pt n 0).first, (Pt n (Fin.last M₁)).last)
  have hbud := finiteBridgeBudget_le_fin_sum M₁ (ENNReal.ofReal δb) (Pt n) budget
    (fun j => (hall j).2.2)
  refine hsetd.trans (hamb.trans (hch.trans (hbud.trans ?_)))
  
  set E4 : ℝ≥0∞ := ENNReal.ofReal (Real.exp (4 * ξ * θ)) with hE4
  set eM : ℝ := Real.exp (ξ * (M + θ + θ + θ)) with heM
  have hsplit : ∀ j : Fin (M₁ + 1), budget j =
      E4 * (chainWeightMinus ξ f θ (v j) * D (v j, v (j + 1))) +
        ENNReal.ofReal ηs * ENNReal.ofReal (Real.exp (ξ * (f (v j) + θ + θ + θ))) := by
    intro j
    simp only [hbudget, chainWeightMinus]
    rw [mul_add, ofReal_exp_shift4]
    ring
  have hfirst : (∑ j : Fin (M₁ + 1), chainWeightMinus ξ f θ (v j) * D (v j, v (j + 1)))
      ≤ S + ENNReal.ofReal ε + ENNReal.ofReal ε := by
    rw [Fin.sum_univ_eq_sum_range (fun j => chainWeightMinus ξ f θ (v j) *
      D (v j, v (j + 1))) (M₁ + 1)]
    refine (hvsum.trans hcost.le).trans ?_
    exact add_le_add hxy.le le_rfl
  have hsecond : (∑ j : Fin (M₁ + 1), ENNReal.ofReal ηs *
      ENNReal.ofReal (Real.exp (ξ * (f (v j) + θ + θ + θ)))) ≤
        ENNReal.ofReal ε * ENNReal.ofReal eM := by
    calc (∑ j : Fin (M₁ + 1), ENNReal.ofReal ηs *
          ENNReal.ofReal (Real.exp (ξ * (f (v j) + θ + θ + θ))))
        ≤ ∑ _j : Fin (M₁ + 1), ENNReal.ofReal ηs * ENNReal.ofReal eM := by
          refine Finset.sum_le_sum fun j _ => ?_
          gcongr
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
            (by linarith [(abs_le.1 (hfM (v j))).2]) hξ)
      _ = (M₁ + 1) • (ENNReal.ofReal ηs * ENNReal.ofReal eM) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = ((M₁ + 1) • ENNReal.ofReal ηs) * ENNReal.ofReal eM := by
          rw [smul_mul_assoc]
      _ ≤ ENNReal.ofReal ε * ENNReal.ofReal eM := by
          gcongr
          refine nsmul_ofReal_le (M₁ + 1) ?_
          have h1 : ηs ≤ ε / ((M₁ : ℝ) + 1) := min_le_right _ _
          rw [le_div_iff₀ hM₁pos] at h1
          push_cast
          linarith
  have hthird : M₁ • ENNReal.ofReal δb ≤ ENNReal.ofReal ε := by
    refine nsmul_ofReal_le M₁ ?_
    rw [hδbdef, mul_div_assoc', div_le_iff₀ hM₁pos]
    nlinarith
  calc (∑ j : Fin (M₁ + 1), budget j) + M₁ • ENNReal.ofReal δb
      = E4 * (∑ j : Fin (M₁ + 1), chainWeightMinus ξ f θ (v j) * D (v j, v (j + 1))) +
          (∑ j : Fin (M₁ + 1), ENNReal.ofReal ηs *
            ENNReal.ofReal (Real.exp (ξ * (f (v j) + θ + θ + θ)))) +
          M₁ • ENNReal.ofReal δb := by
        rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ E4 * (S + ENNReal.ofReal ε + ENNReal.ofReal ε) +
          ENNReal.ofReal ε * ENNReal.ofReal eM + ENNReal.ofReal ε := by
        gcongr
    _ = E4 * (S + ENNReal.ofReal ε + ENNReal.ofReal ε) +
          ENNReal.ofReal ε * ENNReal.ofReal (eM + 1) := by
        rw [ENNReal.ofReal_add (Real.exp_pos _).le zero_le_one, ENNReal.ofReal_one]
        ring

end SupercriticalLQGUniqueness.B2.PfeWeyl
