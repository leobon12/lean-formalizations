import SupercriticalLQGUniqueness.B2.PfeLocal.L6Obs
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaAutoRadius

 


















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum Uniqueness.Toolkit.PathInfimum PfeWeyl

 
theorem l6_smallAnnulusCosts_localize {G : ℕ → LSCMetric} {D : LSCMetric}
    {K₁ V₁ K V : Set ℂ} (h : SmallAnnulusCosts G D K₁ V₁) (hK : K ⊆ K₁) {η : ℝ} (hη : 0 < η)
    (hV : ∀ z ∈ K, ball z η ⊆ V) : SmallAnnulusCosts G D K V := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨A, hA1, hA2, hA3, -, hA5⟩ := h z (hK hz) hns δ hδ (min ρ (η / 2))
    (lt_min hρ (half_pos hη))
  refine ⟨A, hA1, hA2, hA3.trans_le (min_le_left _ _), ?_, hA5⟩
  intro w hw
  have hw1 : w ∈ ball A.center A.outerRadius := hw.1
  apply hV z hz
  rw [mem_ball] at hw1 ⊢
  have h1 : A.outerRadius < η / 2 := hA3.trans_le (min_le_right _ _)
  have h2 : A.innerRadius < A.outerRadius := by
    by_contra hc
    push Not at hc
    have : w ∈ closure (ball A.center A.innerRadius) := by
      apply subset_closure
      rw [mem_ball]; linarith
    exact hw.2 this
  calc dist w z ≤ dist w A.center + dist A.center z := dist_triangle _ _ _
    _ < A.outerRadius + A.innerRadius := by rw [dist_comm A.center z]; exact add_lt_add hw1 hA2
    _ < η := by linarith

 
theorem l6_limsup_le {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, PfeAxioms.FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    (hsmall : ∀ k : ℕ, SmallAnnulusCosts G D (closedBall 0 k) (ball 0 ((k : ℝ) + 1)))
    {Q E F Q' E' F' : Set ℂ} (hQ : IsCompact Q) {η : ℝ} (hη : 0 < η)
    (hQQ' : thickening η Q ⊆ Q') (hEE' : thickening η E ⊆ E') (hFF' : thickening η F ⊆ F') :
    limsup (fun n => compactPathInf (G n) Q' E' F') atTop ≤ compactPathInf D Q E F := by
  by_contra hnot
  push Not at hnot
  obtain ⟨y, hy1, hy2⟩ := exists_between hnot
  have hyt : y ≠ ∞ := ne_top_of_lt hy2
  set C : ℝ := y.toReal
  have hyC : y = ENNReal.ofReal C := (ENNReal.ofReal_toReal hyt).symm
  have hC : 0 < C := by
    rw [hyC] at hy1
    exact ENNReal.ofReal_pos.1 (lt_of_le_of_lt bot_le hy1)
  
  rw [hyC] at hy1
  have hlt := hy1
  unfold compactPathInf at hlt
  obtain ⟨P, s, t, hP, htr, hEs, hFt, hcost⟩ := (by simpa only [iInf_lt_iff] using hlt)
  set W : Set ℂ := thickening (η / 4) Q
  set K : Set ℂ := cthickening (η / 2) Q
  set V : Set ℂ := thickening (3 * η / 4) Q
  have hQW : Q ⊆ W := self_subset_thickening (by positivity) Q
  have hes : P s ∈ W := hQW (htr s ⟨le_rfl, hP.1⟩)
  have hft : P t ∈ W := hQW (htr t ⟨hP.1, le_rfl⟩)
  have hint : D.internal W (⟨P s, hes⟩, ⟨P t, hft⟩) < ENNReal.ofReal C := by
    refine lt_of_le_of_lt ?_ hcost
    unfold LSCMetric.internal
    exact iInf_le_of_le P <| iInf_le_of_le s <| iInf_le_of_le t <| iInf_le_of_le hP <|
      iInf_le_of_le (fun u hu => hQW (htr u hu)) <| iInf_le_of_le rfl <| iInf_le_of_le rfl le_rfl
  have hWV : W ⊆ V := thickening_mono (by linarith) Q
  have hWK : W ⊆ interior K :=
    (thickening_mono (by linarith : η / 4 ≤ η / 2) Q).trans
      (thickening_subset_interior_cthickening (η / 2) Q)
  have hVo : IsOpen V := isOpen_thickening
  have hKc : IsCompact K := hQ.cthickening
  have hVb : Bornology.IsBounded V := hQ.isBounded.thickening
  have hfront : IsCompact (frontier V) :=
    hVb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hVne : V.Nonempty := ⟨P s, hWV hes⟩
  have hVc : Vᶜ.Nonempty := by
    obtain ⟨R, hR⟩ := hVb.subset_closedBall 0
    refine ⟨(R + 1 : ℝ), fun h => ?_⟩
    have := hR h
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at this
    have hR0 : 0 ≤ R := le_trans dist_nonneg (hR (hWV hes))
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have hneFront : (frontier V).Nonempty :=
    nonempty_frontier_iff.2 ⟨hVne, fun h => by rw [h] at hVc; simp at hVc⟩
  have hdisj : Disjoint K (frontier V) := by
    refine Set.disjoint_left.2 fun z hzK hzF => ?_
    have h1 : infEDist z Q ≤ ENNReal.ofReal (η / 2) := mem_cthickening_iff.1 hzK
    have h2 : infEDist z Q = ENNReal.ofReal (3 * η / 4) := frontier_thickening_subset Q hzF
    rw [h2, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    linarith
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall 0
  obtain ⟨k, hk⟩ := exists_nat_ge R
  have hsmallK : SmallAnnulusCosts G D K V := by
    refine l6_smallAnnulusCosts_localize (hsmall k) (fun z hz => ?_) (by positivity : (0 : ℝ) < η / 4)
      fun z hz => ?_
    · exact closedBall_subset_closedBall hk (hR hz)
    · intro w hw
      have h1 : infEDist z Q ≤ ENNReal.ofReal (η / 2) := mem_cthickening_iff.1 hz
      have h2 : edist w z < ENNReal.ofReal (η / 4) := by
        rw [edist_dist]; exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨mem_ball.1 hw, by positivity⟩
      show infEDist w Q < ENNReal.ofReal (3 * η / 4)
      calc infEDist w Q ≤ infEDist z Q + edist w z := infEDist_le_infEDist_add_edist
        _ < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 4) :=
            ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) h1 h2
        _ = ENNReal.ofReal (3 * η / 4) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  obtain ⟨x', y', hx', hy', hev⟩ := PfeAxioms.buffered_inner_internal_upper_of_compact_collar hG
    hLen hPath hforget hWV hWK hVo hKc hfront hneFront hdisj hsmallK ⟨P s, hes⟩ ⟨P t, hft⟩ hC hint
  have hx'' : Tendsto (fun n => (x' n : ℂ)) atTop (𝓝 (P s)) :=
    (continuous_subtype_val.tendsto _).comp hx'
  have hy'' : Tendsto (fun n => (y' n : ℂ)) atTop (𝓝 (P t)) :=
    (continuous_subtype_val.tendsto _).comp hy'
  have hxE : ∀ᶠ n in atTop, (x' n : ℂ) ∈ E' := by
    filter_upwards [hx''.eventually (ball_mem_nhds (P s) hη)] with n hn
    exact hEE' (mem_thickening_iff.2 ⟨P s, hEs, by rw [← mem_ball]; exact hn⟩)
  have hyF : ∀ᶠ n in atTop, (y' n : ℂ) ∈ F' := by
    filter_upwards [hy''.eventually (ball_mem_nhds (P t) hη)] with n hn
    exact hFF' (mem_thickening_iff.2 ⟨P t, hFt, by rw [← mem_ball]; exact hn⟩)
  have hVQ : V ⊆ Q' := (thickening_mono (by linarith) Q).trans hQQ'
  have hfin : ∀ᶠ n in atTop, compactPathInf (G n) Q' E' F' ≤ ENNReal.ofReal C := by
    filter_upwards [hev, hxE, hyF] with n hn hxn hyn
    refine le_trans ?_ hn.le
    unfold LSCMetric.internal compactPathInf
    refine le_iInf fun Pn => le_iInf fun a => le_iInf fun b => le_iInf fun hPn =>
      le_iInf fun htrn => le_iInf fun ha => le_iInf fun hb => ?_
    exact iInf_le_of_le Pn <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hPn <|
      iInf_le_of_le (fun u hu => hVQ (htrn u hu)) <| iInf_le_of_le (ha ▸ hxn) <|
        iInf_le_of_le (hb ▸ hyn) le_rfl
  have := limsup_le_of_le (by isBoundedDefault) hfin
  rw [← hyC] at this
  exact (not_lt_of_ge this) hy2

 
theorem l6_compactPathInf_le_liminf_shrink (D : LSCMetric) (K E F : ℕ → Set ℂ)
    (hK0 : IsCompact (K 0)) (hK : Antitone K) (hE : Antitone E) (hF : Antitone F)
    (hKc : ∀ m, IsClosed (K m)) (hEc : ∀ m, IsClosed (E m)) (hFc : ∀ m, IsClosed (F m)) :
    compactPathInf D (⋂ m, K m) (⋂ m, E m) (⋂ m, F m) ≤
      liminf (fun m => compactPathInf D (K m) (E m) (F m)) atTop := by
  refine le_of_forall_lt fun v hv => ?_
  obtain ⟨w, hvw, hw⟩ := exists_between hv
  have hwfin : w ≠ ∞ := ne_top_of_lt hw
  have htail : ∀ᶠ m in atTop, w ≤ compactPathInf D (K m) (E m) (F m) := by
    by_contra hn
    rw [not_eventually] at hn
    obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hn
    have hbad' : ∀ n, compactPathInf D (K (φ n)) (E (φ n)) (F (φ n)) < w :=
      fun n => lt_of_not_ge (hbad n)
    have hpaths : ∀ n, ∃ (P : ℝ → ℂ) (a b : ℝ),
        D.IsCurve P a b ∧ (∀ t ∈ Icc a b, P t ∈ K (φ n)) ∧ P a ∈ E (φ n) ∧ P b ∈ F (φ n) ∧
        D.len P a b < w := by
      intro n
      unfold compactPathInf at hbad'
      obtain ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩ :=
        (by simpa only [iInf_lt_iff] using hbad' n)
      exact ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩
    choose P a b hP htrace hEa hFb hlen using hpaths
    have hfin : ∀ n, D.len (P n) (a n) (b n) ≠ ∞ := fun n => ne_top_of_lt (hlen n)
    have htrace' : ∀ n, P n '' Icc (a n) (b n) ⊆ K (φ n) := by
      intro n z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact htrace n t ht
    choose γ hγlen hγtrace hγlip using fun n =>
      exists_lipschitz_reparam D (P n) (hP n) (hfin n) (htrace' n)
    let Q : ℕ → unitInterval → ℂ := fun n t => γ n t
    have hQK : ∀ n t, Q n t ∈ K (φ n) := fun n t => hγtrace n t
    have hQtrace : ∀ n t, Q n t ∈ K 0 := fun n t => hK (Nat.zero_le _) (hQK n t)
    have hQ0 : ∀ n, Q n 0 = P n (a n) := fun n => by
      change (γ n 0 : ℂ) = _
      rw [(γ n).source]
      rfl
    have hQ1 : ∀ n, Q n 1 = P n (b n) := fun n => by
      change (γ n 1 : ℂ) = _
      rw [(γ n).target]
      rfl
    have hQlip : ∀ n, LipschitzWith w.toNNReal (D.pt ∘ Q n) := by
      intro n
      have hmono : (D.len (P n) (a n) (b n)).toNNReal ≤ w.toNNReal :=
        ENNReal.toNNReal_mono hwfin (hlen n).le
      exact (hγlip n).weaken hmono
    have hQbound : ∀ n, D.len (fun t => Q n (projIcc 0 1 zero_le_one t)) 0 1 ≤ w := by
      intro n
      change LQGMetric.MetricGeometry.pathLength (γ n) ≤ w
      exact (hγlen n).le.trans (hlen n).le
    have hconst : Tendsto (fun _ : ℕ => D) atTop (𝓝 D) := tendsto_const_nhds
    obtain ⟨ψ, P₀, hψ, hlim, -⟩ := compact_trace_path_subseq hconst hK0 hQtrace hQlip
    have hDlip : LipschitzWith w.toNNReal (D.pt ∘ P₀) :=
      lipschitz_limit_of_epi hconst hlim (fun n => hQlip (ψ n))
    have hcurve : D.IsCurve (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 :=
      ⟨zero_le_one, (hDlip.continuous.comp continuous_projIcc).continuousOn⟩
    have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
        Tendsto (fun n => Q (ψ n) (projIcc 0 1 zero_le_one t)) atTop
          (𝓝 (P₀ (projIcc 0 1 zero_le_one t))) :=
      fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t)
    have hlen₀ := joint_len_le_liminf hconst hpoint
    have hlen₁ : D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ w :=
      hlen₀.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => hQbound (ψ n)))
    have hφψ : Tendsto (fun n => φ (ψ n)) atTop atTop := (hφ.comp hψ).tendsto_atTop
    have hmemI : ∀ (S : ℕ → Set ℂ), Antitone S → (∀ m, IsClosed (S m)) →
        ∀ s : unitInterval, (∀ n, Q (ψ n) s ∈ S (φ (ψ n))) → P₀ s ∈ ⋂ m, S m := by
      intro S hS hSc s hmem
      refine mem_iInter.2 fun j => (hSc j).mem_of_tendsto (hlim.tendsto_at s) ?_
      filter_upwards [hφψ.eventually_ge_atTop j] with n hn
      exact hS hn (hmem n)
    have hInf : compactPathInf D (⋂ m, K m) (⋂ m, E m) (⋂ m, F m) ≤
        D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
      apply l5_compactPathInf_le D _ 0 1 hcurve
      · intro t _
        exact hmemI K hK hKc _ fun n => hQK (ψ n) _
      · simp only [projIcc_left]
        exact hmemI E hE hEc 0 fun n => by rw [hQ0]; exact hEa (ψ n)
      · simp only [projIcc_right]
        exact hmemI F hF hFc 1 fun n => by rw [hQ1]; exact hFb (ψ n)
    exact (not_le_of_gt hw) (hInf.trans hlen₁)
  exact hvw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) htail)

 

 
def l6δ (m : ℕ) : ℚ := 1 / ((m : ℚ) + 1)

theorem l6δ_pos (m : ℕ) : 0 < l6δ m := by unfold l6δ; positivity

theorem l6δ_anti {m m' : ℕ} (h : m < m') : l6δ m' < l6δ m := by
  unfold l6δ
  apply one_div_lt_one_div_of_lt (by positivity)
  exact_mod_cast Nat.add_lt_add_right h 1

 
def l6Enlarge (c : L5Code) (m : ℕ) : L5Code :=
  ((c.1.1 - l6δ m, c.1.2.1 + l6δ m, c.1.2.2.1 - l6δ m, c.1.2.2.2 + l6δ m),
    (c.2.1.1, c.2.1.2.1, c.2.1.2.2 + l6δ m), (c.2.2.1, c.2.2.2.1, c.2.2.2.2 + l6δ m))

 
theorem l6_rect_thickening {q q' : ℚ × ℚ × ℚ × ℚ} {η : ℝ}
    (h1 : (q'.1 : ℝ) ≤ q.1 - η) (h2 : (q.2.1 : ℝ) + η ≤ q'.2.1)
    (h3 : (q'.2.2.1 : ℝ) ≤ q.2.2.1 - η) (h4 : (q.2.2.2 : ℝ) + η ≤ q'.2.2.2) :
    thickening η (l5Rect q) ⊆ l5Rect q' := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := mem_thickening_iff.1 hz
  have hzp' : ‖z - p‖ < η := by rw [← Complex.dist_eq]; exact hzp
  have hre : |z.re - p.re| < η := by
    rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans_lt hzp'
  have him : |z.im - p.im| < η := by
    rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans_lt hzp'
  obtain ⟨p1, p2, p3, p4⟩ := hp
  rw [abs_lt] at hre him
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

 
theorem l6_ball_thickening {q q' : ℚ × ℚ × ℚ} (hc1 : q'.1 = q.1) (hc2 : q'.2.1 = q.2.1)
    {η : ℝ} (hr : (q.2.2 : ℝ) + η ≤ q'.2.2) : thickening η (l5Ball q) ⊆ l5Ball q' := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := mem_thickening_iff.1 hz
  rw [l5Ball, mem_closedBall] at hp ⊢
  rw [hc1, hc2]
  calc dist z _ ≤ dist z p + dist p _ := dist_triangle _ _ _
    _ ≤ η + q.2.2 := add_le_add hzp.le hp
    _ ≤ q'.2.2 := by linarith

 
theorem l6_enlarge_margin (c : L5Code) {m m' : ℕ} (h : m < m') :
    let η : ℝ := (l6δ m : ℝ) - l6δ m'
    thickening η (l5Rect (l6Enlarge c m').1) ⊆ l5Rect (l6Enlarge c m).1 ∧
      thickening η (l5Ball (l6Enlarge c m').2.1) ⊆ l5Ball (l6Enlarge c m).2.1 ∧
      thickening η (l5Ball (l6Enlarge c m').2.2) ⊆ l5Ball (l6Enlarge c m).2.2 := by
  intro η
  refine ⟨l6_rect_thickening ?_ ?_ ?_ ?_,
    l6_ball_thickening (q := (l6Enlarge c m').2.1) (q' := (l6Enlarge c m).2.1) rfl rfl ?_,
    l6_ball_thickening (q := (l6Enlarge c m').2.2) (q' := (l6Enlarge c m).2.2) rfl rfl ?_⟩ <;>
    simp only [l6Enlarge, η] <;> push_cast <;> linarith

 
theorem l6_enlarge_margin0 (c : L5Code) (m : ℕ) :
    thickening (l6δ m : ℝ) (l5Rect c.1) ⊆ l5Rect (l6Enlarge c m).1 ∧
      thickening (l6δ m : ℝ) (l5Ball c.2.1) ⊆ l5Ball (l6Enlarge c m).2.1 ∧
      thickening (l6δ m : ℝ) (l5Ball c.2.2) ⊆ l5Ball (l6Enlarge c m).2.2 := by
  refine ⟨l6_rect_thickening ?_ ?_ ?_ ?_,
    l6_ball_thickening (q := c.2.1) (q' := (l6Enlarge c m).2.1) rfl rfl ?_,
    l6_ball_thickening (q := c.2.2) (q' := (l6Enlarge c m).2.2) rfl rfl ?_⟩ <;>
    simp only [l6Enlarge] <;> push_cast <;> linarith

theorem l6_iInter_rect (c : L5Code) : ⋂ m, l5Rect (l6Enlarge c m).1 = l5Rect c.1 := by
  have hδ : Tendsto (fun m : ℕ => ((l6δ m : ℚ) : ℝ)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine this.congr fun m => ?_
    simp [l6δ]
  ext z
  simp only [mem_iInter, l5Rect, l6Enlarge, mem_setOf_eq]
  constructor
  · intro h
    have key : ∀ (x y : ℝ), (∀ m : ℕ, x ≤ y + ((l6δ m : ℚ) : ℝ)) → x ≤ y := fun x y hxy =>
      le_of_tendsto_of_tendsto' tendsto_const_nhds (by simpa using hδ.const_add y) hxy
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact key _ _ fun m => by have := (h m).1; push_cast at this; linarith
    · exact key _ _ fun m => by have := (h m).2.1; push_cast at this; linarith
    · exact key _ _ fun m => by have := (h m).2.2.1; push_cast at this; linarith
    · exact key _ _ fun m => by have := (h m).2.2.2; push_cast at this; linarith
  · rintro ⟨h1, h2, h3, h4⟩ m
    have := l6δ_pos m
    have h0 : (0 : ℝ) < l6δ m := by exact_mod_cast this
    push_cast
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem l6_iInter_ball (q : ℚ × ℚ × ℚ) :
    ⋂ m, l5Ball (q.1, q.2.1, q.2.2 + l6δ m) = l5Ball q := by
  have hδ : Tendsto (fun m : ℕ => ((l6δ m : ℚ) : ℝ)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine this.congr fun m => ?_
    simp [l6δ]
  ext z
  simp only [mem_iInter, l5Ball, mem_closedBall]
  constructor
  · intro h
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds (by simpa using hδ.const_add _)
      fun m => ?_
    have := h m
    push_cast at this
    exact this
  · intro h m
    have h0 : (0 : ℝ) < l6δ m := by exact_mod_cast l6δ_pos m
    push_cast
    linarith

 
theorem l6_obs_enlarge_tendsto (D : LSCMetric) (c : L5Code) :
    Tendsto (fun m => l5Obs D (l6Enlarge c m)) atTop (𝓝 (l5Obs D c)) := by
  have hmono : Monotone fun m => l5Obs D (l6Enlarge c m) := by
    intro m m' hmm
    rcases eq_or_lt_of_le hmm with h | h
    · rw [h]
    obtain ⟨h1, h2, h3⟩ := l6_enlarge_margin c h
    have hpos : (0 : ℝ) < (l6δ m : ℝ) - l6δ m' := by
      have := l6δ_anti h; rw [sub_pos]; exact_mod_cast this
    unfold l5Obs compactPathInf
    refine iInf_mono fun P => iInf_mono fun a => iInf_mono fun b => iInf_mono fun _ =>
      iInf_mono' fun htr => ⟨fun t ht => h1 (self_subset_thickening hpos _ (htr t ht)),
        iInf_mono' fun hE => ⟨h2 (self_subset_thickening hpos _ hE),
          iInf_mono' fun hF => ⟨h3 (self_subset_thickening hpos _ hF), le_rfl⟩⟩⟩
  have hle : ∀ m, l5Obs D (l6Enlarge c m) ≤ l5Obs D c := by
    intro m
    obtain ⟨h1, h2, h3⟩ := l6_enlarge_margin0 c m
    have hpos : (0 : ℝ) < l6δ m := by exact_mod_cast l6δ_pos m
    unfold l5Obs compactPathInf
    exact iInf_mono fun P => iInf_mono fun a => iInf_mono fun b => iInf_mono fun _ =>
      iInf_mono' fun htr => ⟨fun t ht => h1 (self_subset_thickening hpos _ (htr t ht)),
        iInf_mono' fun hE => ⟨h2 (self_subset_thickening hpos _ hE),
          iInf_mono' fun hF => ⟨h3 (self_subset_thickening hpos _ hF), le_rfl⟩⟩⟩
  have hanti : ∀ (S : ℕ → Set ℂ), (∀ m m', m < m' → S m' ⊆ S m) → Antitone S := by
    intro S hS m m' hmm
    rcases eq_or_lt_of_le hmm with h | h
    · rw [h]
    · exact hS m m' h
  have hsub : ∀ m m', m < m' →
      l5Rect (l6Enlarge c m').1 ⊆ l5Rect (l6Enlarge c m).1 ∧
        l5Ball (l6Enlarge c m').2.1 ⊆ l5Ball (l6Enlarge c m).2.1 ∧
        l5Ball (l6Enlarge c m').2.2 ⊆ l5Ball (l6Enlarge c m).2.2 := by
    intro m m' h
    obtain ⟨h1, h2, h3⟩ := l6_enlarge_margin c h
    have hpos : (0 : ℝ) < (l6δ m : ℝ) - l6δ m' := by
      have := l6δ_anti h; rw [sub_pos]; exact_mod_cast this
    exact ⟨(self_subset_thickening hpos _).trans h1, (self_subset_thickening hpos _).trans h2,
      (self_subset_thickening hpos _).trans h3⟩
  have hsh := l6_compactPathInf_le_liminf_shrink D (fun m => l5Rect (l6Enlarge c m).1)
    (fun m => l5Ball (l6Enlarge c m).2.1) (fun m => l5Ball (l6Enlarge c m).2.2)
    (l5Rect_isCompact _) (hanti _ fun m m' h => (hsub m m' h).1)
    (hanti _ fun m m' h => (hsub m m' h).2.1) (hanti _ fun m m' h => (hsub m m' h).2.2)
    (fun m => (l5Rect_isCompact _).isClosed)
    (fun m => isClosed_closedBall) (fun m => isClosed_closedBall)
  rw [l6_iInter_rect] at hsh
  have e1 : ⋂ m, l5Ball (l6Enlarge c m).2.1 = l5Ball c.2.1 := l6_iInter_ball c.2.1
  have e2 : ⋂ m, l5Ball (l6Enlarge c m).2.2 = l5Ball c.2.2 := l6_iInter_ball c.2.2
  rw [e1, e2] at hsh
  have hT : Tendsto (fun m => l5Obs D (l6Enlarge c m)) atTop
      (𝓝 (⨆ m, l5Obs D (l6Enlarge c m))) := tendsto_atTop_iSup hmono
  have hsup : ⨆ m, l5Obs D (l6Enlarge c m) = l5Obs D c :=
    le_antisymm (iSup_le hle) (hsh.trans hT.liminf_eq.le)
  rw [hsup] at hT
  exact hT

end SupercriticalLQGUniqueness.B2.PfeLocal
