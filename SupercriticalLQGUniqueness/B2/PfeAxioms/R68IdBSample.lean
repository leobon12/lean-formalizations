import SupercriticalLQGUniqueness.B2.PfeAxioms.R68IdBBarrier

 














set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 




theorem lowerNbhdObs_le_of_barrier
    (ξ : Set.Ioi (0 : ℝ)) (a : ℕ → Set.Ioi (0 : ℝ)) (εn : ℕ → ℝ) (hεn : ∀ n, εn n ≠ 0)
    (Φ : LSCMetric) (hforget : Continuous (PfeWeyl.euclidForget Φ))
    {V : Set ℂ} (hV : IsOpen V) {R : ℝ} (hR : 0 ≤ R)
    (hRV : Metric.ball (0 : ℂ) (R + 2) ⊆ V)
    (φ X : ℕ → C(ℂ, ℝ)) (F F0 : C(ℂ, ℝ)) (M0 : ℝ) (hM0 : ∀ z, |F0 z| ≤ M0)
    (hFF0 : ∀ z : ℂ, ‖z‖ ≤ R → F z = F0 z)
    (hclose : ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ V,
      φ n z ≤ (X n + LQGMetric.LFPP.mollCont (εn n) (hεn n) F0 M0 hM0) z + θ)
    (hW3 : ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M), ∃ E : LSCMetric,
      (∀ p, E p = weylScale (ξ : ℝ) f Φ p) ∧
      Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
        (X n + LQGMetric.LFPP.mollCont (εn n) (hεn n) f M hM)) atTop (𝓝 E))
    {P : ℝ → ℂ} (hP : Φ.IsCurve P 0 1) (hPR : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t‖ ≤ R)
    (x y : V) (hx : P 0 = x) (hy : P 1 = y) {T : ℝ≥0∞}
    (hT : weylWL Φ (ξ : ℝ) F P 0 1 < T) :
    lowerNeighborhoodObservable
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n) (φ n)) V x y ≤ T := by
  have hξ0 : (0 : ℝ) ≤ ξ := ξ.property.le
  by_cases hTtop : T = ⊤
  · rw [hTtop]; exact le_top
  obtain ⟨T₂, hT₂, hT₂T⟩ := exists_between hT
  have hT₂top : T₂ ≠ ⊤ := ne_top_of_lt hT₂T
  
  have hcont : Tendsto (fun θ : ℝ => ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) * T₂) (𝓝 0)
      (𝓝 T₂) := by
    have h1 : Tendsto (fun θ : ℝ => ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ))) (𝓝 0) (𝓝 1) := by
      have hc : Continuous (fun θ : ℝ => ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ))) :=
        ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      simpa using hc.tendsto (0 : ℝ)
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hT₂top)
  obtain ⟨θ, hθT, hθ0⟩ := (((hcont.eventually (gt_mem_nhds hT₂T)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have hθ0' : (0 : ℝ) < θ := hθ0
  
  let A : EuclideanAnnulus := ⟨((0 : ℂ), (R + 1, R + 2)), by linarith, by linarith⟩
  have hAc : A.center = 0 := rfl
  have hAi : A.innerRadius = R + 1 := rfl
  have hAo : A.outerRadius = R + 2 := rfl
  have hα := PfeWeyl.acrossDist_pos Φ A
  obtain ⟨B, hB0, hBT⟩ := exists_barrier_height ξ.property M0 hα hTtop
  let f : C(ℂ, ℝ) := F0 + barrierBump R B
  have hfapp : ∀ z, f z = F0 z + barrierBump R B z := fun z => rfl
  have hfM : ∀ z, |f z| ≤ M0 + B := fun z => by
    rw [hfapp]
    calc |F0 z + barrierBump R B z| ≤ |F0 z| + |barrierBump R B z| := abs_add_le _ _
      _ ≤ M0 + B := add_le_add (hM0 z)
          (by rw [abs_of_nonneg (barrierBump_nonneg hB0 z)]; exact barrierBump_le hB0 z)
  obtain ⟨E, hE, hEconv⟩ := hW3 f (M0 + B) hfM
  set G : ℕ → LSCMetric := fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
    (X n + LQGMetric.LFPP.mollCont (εn n) (hεn n) f (M0 + B) hfM) with hGdef
  
  have hEP : E ((x : ℂ), (y : ℂ)) < T₂ := by
    have h1 : E.len P 0 1 = weylWL Φ (ξ : ℝ) F P 0 1 :=
      len_eq_weylWL_of_eqOn Φ E (ξ : ℝ) F f hforget hE hP (fun t ht => by
        rw [hfapp, barrierBump_eq_zero (by linarith [hPR t ht]), add_zero]
        exact hFF0 _ (hPR t ht))
    have h2 := LSCMetric.apply_le_len E P (zero_le_one : (0 : ℝ) ≤ 1)
    rw [hx, hy] at h2
    exact (h2.trans h1.le).trans_lt hT₂
  
  have hEA : T < acrossDist E A := by
    refine hBT.trans_le ?_
    refine le_acrossDist_weylScale Φ E hforget hξ0 f hE A (B - M0) (fun z hz1 _ => ?_)
    rw [hAi, hAc, dist_zero_right] at hz1
    rw [hfapp, barrierBump_eq hz1]
    linarith [(abs_le.1 (hM0 z)).1]
  
  have hlsc := LSCFun.tendsto_iff_lscTendsto.1
    (LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff.1 hEconv)
  obtain ⟨q, hq, hqv⟩ := hlsc.2 ((x : ℂ), (y : ℂ))
  simp only [Function.comp_apply, LSCMetric.toLSCFun_apply] at hqv
  have hev1 : ∀ᶠ n in atTop, G n (q n) < T₂ := by
    have hlt : ((E ((x : ℂ), (y : ℂ)) : ℝ≥0∞) : EReal) < (T₂ : EReal) :=
      EReal.coe_ennreal_lt_coe_ennreal_iff.2 hEP
    filter_upwards [hqv.eventually (gt_mem_nhds hlt)] with n hn
    exact EReal.coe_ennreal_lt_coe_ennreal_iff.1 hn
  have hev2 : ∀ᶠ n in atTop, T < acrossDist (G n) A := PfeWeyl.eventually_lt_acrossDist hEconv A hEA
  have hq1 : Tendsto (fun n => (q n).1) atTop (𝓝 (x : ℂ)) := (continuous_fst.tendsto _).comp hq
  have hq2 : Tendsto (fun n => (q n).2) atTop (𝓝 (y : ℂ)) := (continuous_snd.tendsto _).comp hq
  have hxR : ‖(x : ℂ)‖ ≤ R := by rw [← hx]; exact hPR 0 ⟨le_rfl, zero_le_one⟩
  have hyR : ‖(y : ℂ)‖ ≤ R := by rw [← hy]; exact hPR 1 ⟨zero_le_one, le_rfl⟩
  have hFf : ∀ z, F0 z ≤ f z := fun z => by
    rw [hfapp]; linarith [barrierBump_nonneg (R := R) hB0 z]
  
  have hnbhd : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop,
      neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n) (φ n)) V x y ρ ≤
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) * T₂ := by
    intro ρ hρ
    have hb1 : ∀ᶠ n in atTop, dist (q n).1 (x : ℂ) < min ρ 1 :=
      hq1.eventually (Metric.ball_mem_nhds _ (lt_min hρ one_pos))
    have hb2 : ∀ᶠ n in atTop, dist (q n).2 (y : ℂ) < min ρ 1 :=
      hq2.eventually (Metric.ball_mem_nhds _ (lt_min hρ one_pos))
    filter_upwards [hev1, hev2, hb1, hb2, hclose θ hθ0'] with n h1 h2 h3 h4 h5
    have hn1 : ‖(q n).1‖ < R + 1 := by
      have := norm_le_norm_add_norm_sub' (q n).1 (x : ℂ)
      rw [← dist_eq_norm] at this
      linarith [min_le_right ρ 1]
    have hn2 : ‖(q n).2‖ < R + 1 := by
      have := norm_le_norm_add_norm_sub' (q n).2 (y : ℂ)
      rw [← dist_eq_norm] at this
      linarith [min_le_right ρ 1]
    have hu : (q n).1 ∈ V := hRV (by rw [Metric.mem_ball, dist_zero_right]; linarith)
    have hv : (q n).2 ∈ V := hRV (by rw [Metric.mem_ball, dist_zero_right]; linarith)
    set u : V := ⟨(q n).1, hu⟩
    set v : V := ⟨(q n).2, hv⟩
    
    have hint : (G n).internal V (u, v) < T₂ := by
      obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 h1
      have hfin : G n ((q n).1, (q n).2) < ⊤ := lt_of_lt_of_le h1 le_top
      obtain ⟨γ, a', b', hγ, hγa, hγb, hγlen⟩ :=
        PfeWeyl.isLengthSpace_normalizedLFPPMetric (ξ : ℝ) (a n) _ (q n).1 (q n).2 hfin
          (r : ℝ) (by exact_mod_cast hr0)
      rw [ENNReal.ofReal_coe_nnreal] at hγlen
      have hlenT : (G n).len γ a' b' < T₂ := hγlen.trans_lt hr
      have hγc : ContinuousOn γ (Icc a' b') :=
        (continuous_euclidForget_normalizedLFPPMetric _ _ _).comp_continuousOn hγ.2
      have ha' : dist (γ a') A.center ≤ A.innerRadius := by
        rw [hγa, hAc, hAi, dist_zero_right]; exact hn1.le
      have hball := PfeWeyl.curve_mem_ball_of_len_lt_acrossDist (G n) A hγc ha'
        (hlenT.trans (hT₂T.trans h2))
      have hY : ∀ t ∈ Icc a' b', γ t ∈ V := fun t ht => hRV (by
        have := hball t ht
        rwa [hAc, hAo] at this)
      have hle := B2.PfeLocal.internal_le_len (G n) V γ a' b' hγ hY
      have hua : (⟨γ a', hY a' ⟨le_rfl, hγ.1⟩⟩ : V) = u := Subtype.ext hγa
      have hvb : (⟨γ b', hY b' ⟨hγ.1, le_rfl⟩⟩ : V) = v := Subtype.ext hγb
      rw [hua, hvb] at hle
      exact hle.trans_lt hlenT
    have hθ' : ∀ z ∈ V, φ n z ≤
        (X n + LQGMetric.LFPP.mollCont (εn n) (hεn n) f (M0 + B) hfM) z + θ := by
      intro z hz
      have hm := PfeWeyl.mollCont_mono (hεn n) hM0 hfM hFf z
      have := h5 z hz
      simp only [ContinuousMap.add_apply] at this ⊢
      linarith
    calc neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n) (φ n)) V x y ρ
        ≤ (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n) (φ n)).internal V (u, v) :=
          iInf_le_of_le u (iInf_le_of_le (h3.trans_le (min_le_left _ _))
            (iInf_le_of_le v (iInf_le_of_le (h4.trans_le (min_le_left _ _)) le_rfl)))
      _ ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) * (G n).internal V (u, v) :=
          internal_le_of_weight_le ξ (a n) (φ n) _ hV hθ' u v
      _ ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) * T₂ := by gcongr
  refine le_trans ?_ hθT.le
  unfold lowerNeighborhoodObservable
  refine iSup_le fun i => ?_
  exact Filter.liminf_le_of_frequently_le' (hnbhd _ (by positivity)).frequently

 

theorem tendsto_patchApprox_of_fixedFieldWeyl
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (Φ : LSCMetric) (hlen : Φ.IsLengthSpace)
    (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (hacross : PfeWeyl.AcrossUnbounded Φ) (hSSA : SelfSmallAnnuli Φ univ)
    (g : DistC) (F : C(ℂ, ℝ))
    (Fk : ℕ → C(ℂ, ℝ)) (Mk : ℕ → ℝ) (hFkM : ∀ k z, |Fk k z| ≤ Mk k)
    (hFk : ∀ k, EqOn F (Fk k) (Metric.closedBall 0 ((k : ℝ) + 3)))
    (X : ℕ → C(ℂ, ℝ))
    (hW3 : ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M), ∃ E : LSCMetric,
      (∀ p, E p = weylScale (ξ : ℝ) f Φ p) ∧
      Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n))
        (X n + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' f M hM)) atTop (𝓝 E))
    (hclose : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
      |locMollifyC (ε n : ℝ) (ε n).property g z -
        (X n + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k) (hFkM k)) z|
        ≤ θ) :
    ∃ W : LSCMetric, (∀ p, W p = weylScale (ξ : ℝ) F Φ p) ∧
      Tendsto (fun k => patchApprox ξ m ε k g) atTop (𝓝 W.toLSCFun) := by
  have hξ0 : (0 : ℝ) ≤ ξ := ξ.property.le
  obtain ⟨W, hW⟩ := exists_weylScale_lscMetric Φ hlen hforget hacross hSSA (ξ : ℝ) hξ0 F
  refine ⟨W, hW, ?_⟩
  choose E hE hEconv using fun k => hW3 (Fk k) (Mk k) (hFkM k)
  set ψ : ℕ → ℕ → C(ℂ, ℝ) := fun k n =>
    X n + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k) (hFkM k) with hψ
  
  have hval : ∀ (k : ℕ) {x y : ℂ} (hx : x ∈ patchBall k) (hy : y ∈ patchBall k),
      (patchApprox ξ m ε k g).1 (x, y) =
        ((lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (patchBall k)
          ⟨x, hx⟩ ⟨y, hy⟩ : ℝ≥0∞) : EReal) := by
    intro k x y hx hy
    rw [patchApprox_apply_of_mem ξ m ε k g hx hy]
    have heq := lowerNbhdObs_eq_of_weight_close ξ (fun n => m (ε n))
      (fun n => locMollifyC (ε n : ℝ) (ε n).property g) (ψ k) (isOpen_patchBall k)
      (hclose k) ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg (fun t : ℝ≥0∞ => (t : EReal)) heq
  apply tendsto_lscFun_of_sandwich _ W (fun k => (k : ℝ)) tendsto_natCast_atTop_atTop
  · 
    rintro k ⟨x, y⟩ hp1 hp2
    have hx : x ∈ patchBall k := by
      change x ∈ Metric.ball (0 : ℂ) ((k : ℝ) + 1)
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hy : y ∈ patchBall k := by
      change y ∈ Metric.ball (0 : ℂ) ((k : ℝ) + 1)
      rw [Metric.mem_ball, dist_zero_right]; linarith
    rw [hval k hx hy]
    apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    have hlow := compact_buffer_le_lowerNeighborhoodObservable (hEconv k)
      (V := patchBall k) (K := Metric.closedBall 0 ((k : ℝ) + 1))
      (U := Metric.ball 0 ((k : ℝ) + 2)) Metric.ball_subset_closedBall
      (isCompact_closedBall _ _) (Metric.closedBall_subset_ball (by linarith))
      ⟨x, hx⟩ ⟨y, hy⟩
    refine le_trans ?_ hlow
    rw [hW (x, y)]
    have hUR : EqOn F (Fk k) (Metric.ball 0 ((k : ℝ) + 2)) := fun z hz =>
      hFk k (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
        (by linarith)) hz)
    have hxU : x ∈ Metric.ball (0 : ℂ) ((k : ℝ) + 2) := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hyU : y ∈ Metric.ball (0 : ℂ) ((k : ℝ) + 2) := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    exact weylScale_le_internal_of_eqOn Φ (E k) (ξ : ℝ) hξ0 F (Fk k) hforget (hE k)
      (-Mk k) (fun z => (abs_le.1 (hFkM k z)).1) hUR ⟨x, hxU⟩ ⟨y, hyU⟩
  · 
    rintro ⟨x₀, y₀⟩
    set p : ℂ × ℂ := (x₀, y₀) with hpdef
    by_cases htop : W p = ⊤
    · rw [htop]; simp
    apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    have hc0 : (0 : EReal) ≤ c := le_trans (EReal.coe_ennreal_nonneg _) hc.le
    by_cases hctop : c = ⊤
    · rw [hctop]; exact le_top
    have hcc : (W p : ℝ≥0∞) < c.toENNReal := by
      have := EReal.toENNReal_lt_toENNReal (EReal.coe_ennreal_nonneg _) hc
      rwa [EReal.toENNReal_coe] at this
    have hlt : weylScale (ξ : ℝ) F Φ p < c.toENNReal := by rw [← hW p]; exact hcc
    obtain ⟨P, hP, hP0, hP1, hPlen⟩ := exists_curve_of_weylScale_lt Φ (ξ : ℝ) F hforget hlt
    have hPc := continuousOn_of_isCurve_forget Φ hforget hP
    obtain ⟨R0, hR0⟩ :=
      ((isCompact_Icc.image_of_continuousOn hPc).isBounded).subset_closedBall 0
    set R : ℝ := max R0 0 with hRdef
    have hR : 0 ≤ R := le_max_right _ _
    have hPR : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t‖ ≤ R := fun t ht => by
      have := hR0 ⟨t, ht, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt (R + 2)
    have hev : ∀ᶠ k in atTop, (patchApprox ξ m ε k g).1 p ≤ (c : EReal) := by
      filter_upwards [eventually_ge_atTop K₀] with k hk
      have hRk : R + 2 < (k : ℝ) := lt_of_lt_of_le hK₀ (by exact_mod_cast hk)
      have hRV : Metric.ball (0 : ℂ) (R + 2) ⊆ patchBall k :=
        Metric.ball_subset_ball (by linarith)
      have hx0 : ‖x₀‖ ≤ R := by
        have := hPR 0 ⟨le_rfl, zero_le_one⟩
        rwa [hP0] at this
      have hy0 : ‖y₀‖ ≤ R := by
        have := hPR 1 ⟨zero_le_one, le_rfl⟩
        rwa [hP1] at this
      have hx : p.1 ∈ patchBall k := hRV (by
        rw [Metric.mem_ball, dist_zero_right]
        show ‖x₀‖ < R + 2
        linarith)
      have hy : p.2 ∈ patchBall k := hRV (by
        rw [Metric.mem_ball, dist_zero_right]
        show ‖y₀‖ < R + 2
        linarith)
      rw [patchApprox_apply_of_mem ξ m ε k g hx hy]
      have hFF0 : ∀ z : ℂ, ‖z‖ ≤ R → F z = Fk k z := fun z hz =>
        hFk k (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
      have hclose' : ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
          locMollifyC (ε n : ℝ) (ε n).property g z ≤
            (X n + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k)
              (hFkM k)) z + θ := fun θ hθ => by
        filter_upwards [hclose k θ hθ] with n hn z hz
        have := (abs_le.1 (hn z hz)).2
        linarith
      have hbar := lowerNbhdObs_le_of_barrier ξ (fun n => m (ε n)) (fun n => (ε n : ℝ))
        (fun n => (ε n).property.ne') Φ hforget (isOpen_patchBall k) hR hRV
        (fun n => locMollifyC (ε n : ℝ) (ε n).property g) X F (Fk k) (Mk k) (hFkM k) hFF0
        hclose' hW3 hP hPR ⟨p.1, hx⟩ ⟨p.2, hy⟩ hP0 hP1 hPlen
      calc ((lowerNeighborhoodObservable (fun n => locLFPP ξ m ε n g) (patchBall k)
            ⟨p.1, hx⟩ ⟨p.2, hy⟩ : ℝ≥0∞) : EReal)
          ≤ ((c.toENNReal : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 hbar
        _ = c := EReal.coe_toENNReal hc0
    exact limsup_le_of_le (by isBoundedDefault) hev

end SupercriticalLQGUniqueness.B2.PfeAxioms
