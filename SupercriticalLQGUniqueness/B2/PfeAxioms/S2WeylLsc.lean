import SupercriticalLQGUniqueness.B2.PfeAxioms.S2WeylCurves
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2AroundLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaLower
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaJoin
import SupercriticalLQGUniqueness.B2.PfeAxioms.ContinuousCutoff
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3WeylMetric
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylLocalTopology
import SupercriticalLQGUniqueness.B2.PfeLocal.Length

 




















set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem continuousOn_of_isCurve_forget (D : LSCMetric)
    (hforget : Continuous (PfeWeyl.euclidForget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) : ContinuousOn P (Icc a b) :=
  hforget.continuousOn.comp hP.2 (mapsTo_univ _ _)

theorem isCurve_sub {D : LSCMetric} {P : ℝ → ℂ} {a b u v : ℝ} (hP : D.IsCurve P a b)
    (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) : D.IsCurve P u v :=
  ⟨huv, hP.2.mono (Icc_subset_Icc hu hv)⟩

 
theorem eventually_lt_add_of_le_liminf {e : ℕ → ℝ≥0∞} {I : ℝ≥0∞}
    (hI : I ≤ liminf e atTop) (hItop : I ≠ ⊤) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, I < e n + ENNReal.ofReal η := by
  rcases lt_or_ge I (ENNReal.ofReal η) with h | h
  · exact Eventually.of_forall fun n => lt_of_lt_of_le h le_add_self
  · have hne : I ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hη) h).ne'
    have hsub : I - ENNReal.ofReal η < I :=
      ENNReal.sub_lt_self hItop hne (ENNReal.ofReal_pos.2 hη).ne'
    filter_upwards [eventually_lt_of_lt_liminf (lt_of_lt_of_le hsub hI)] with n hn
    exact (ENNReal.sub_lt_iff_lt_right ENNReal.ofReal_ne_top h).1 hn

 


theorem weylScale_one_end_join
    (D : LSCMetric) (hlen : D.IsLengthSpace)
    (hforget : Continuous (PfeWeyl.euclidForget D))
    (hacross : PfeWeyl.AcrossUnbounded D) (hSSA : SelfSmallAnnuli D univ)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    {x : ℂ} {xs ys : ℕ → ℂ} (hx : Tendsto xs atTop (𝓝 x)) {r : ℝ} (hr : 0 < r)
    (hxs : ∀ n, xs n ∈ Metric.ball x (r / 2)) (hys : ∀ n, 2 * r ≤ dist (ys n) x)
    {T : ℝ≥0∞} (hTtop : T ≠ ⊤) (hT : ∀ n, weylScale ξ f D (xs n, ys n) < T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ᶠ n in atTop, weylScale ξ f D (x, ys n) < T + ENNReal.ofReal δ := by
  have hδ4 : 0 < δ / 4 := by positivity
  
  set R : ℝ := ‖x‖ + 3 * r + 1 with hRdef
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    f.continuous.continuousOn
  set M : ℝ := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  set fb : C(ℂ, ℝ) := clampContinuous M f
  have hfbM : ∀ z, |fb z| ≤ M := clampContinuous_bound hM f
  have hfb2 : ∀ z, -M ≤ fb z ∧ fb z ≤ M := fun z => abs_le.1 (hfbM z)
  have hfb : EqOn f fb (Metric.closedBall 0 R) := by
    intro z hz
    have h1 : |f z| ≤ M := by
      have := hM0 z hz
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    exact (clampContinuous_eq_of_bound f h1).symm
  obtain ⟨E, hE⟩ := PfeWeyl.exists_weyl_lscMetric hlen hforget hacross ξ hξ fb M hfbM
  have hEforget : Continuous (PfeWeyl.euclidForget E) :=
    Uniqueness.Toolkit.WeylShift.continuous_forget_of_weyl D E ξ hξ fb hforget hE
  have hEcurve : ∀ {P : ℝ → ℂ} {u v : ℝ}, D.IsCurve P u v → E.IsCurve P u v :=
    fun hP => isCurve_weyl_of_bounded D E ξ hξ fb hforget hE (-M) M hfb2 hlen hP
  have hWtri := (Uniqueness.Toolkit.WeylLength.weylScale_isExtMetric D ξ f hforget).2.2.2
  
  choose γ hγ hγ0 hγ1 hγT using fun n =>
    exists_curve_of_weylScale_lt D ξ f hforget (hT n)
  have hexit : ∀ n, ∃ s ∈ Icc (0 : ℝ) 1, γ n s ∈ Metric.sphere x r ∧
      ∀ t ∈ Ico 0 s, γ n t ∈ Metric.ball x r := by
    intro n
    refine exists_first_exit zero_le_one (continuousOn_of_isCurve_forget D hforget (hγ n))
      ?_ ?_
    · rw [hγ0 n]; exact Metric.ball_subset_ball (by linarith) (hxs n)
    · rw [hγ1 n, Metric.mem_ball, not_lt]; linarith [hys n]
  choose s hs hsS hsBall using hexit
  set as : ℕ → ℂ := fun n => γ n (s n)
  obtain ⟨a, -, φ, hφ, haφ⟩ := (isCompact_closedBall x r).tendsto_subseq
    (fun n => Metric.sphere_subset_closedBall (hsS n))
  have ha : a ∈ Metric.sphere x r :=
    Metric.isClosed_sphere.mem_of_tendsto haφ (Eventually.of_forall fun n => hsS (φ n))
  
  set V : Set ℂ := Metric.closedBall x r
  set U : Set ℂ := Metric.ball x (2 * r)
  have hVU : V ⊆ U := Metric.closedBall_subset_ball (by linarith)
  have hR1 : ∀ z, dist z x ≤ 2 * r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z x
    rw [← dist_eq_norm] at this
    linarith
  have hUR : U ⊆ Metric.closedBall 0 R := fun z hz =>
    hR1 z (Metric.mem_ball.1 hz).le
  have htrV : ∀ n, ∀ t ∈ Icc 0 (s n), γ n t ∈ V := by
    intro n t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; exact Metric.sphere_subset_closedBall (hsS n)
    · exact Metric.ball_subset_closedBall (hsBall n t ⟨ht.1, h⟩)
  have hxV : ∀ n, xs n ∈ V := fun n =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) (hxs n))
  have haV : ∀ n, as n ∈ V := fun n => Metric.sphere_subset_closedBall (hsS n)
  
  have hinit : ∀ n, E.internal V (⟨xs n, hxV n⟩, ⟨as n, haV n⟩) ≤
      weylWL D ξ f (γ n) 0 (s n) := by
    intro n
    have hD : D.IsCurve (γ n) 0 (s n) := isCurve_sub (hγ n) le_rfl (hs n).1 (hs n).2
    have h1 := internal_trace_pair_le_len E (hEcurve hD) (htrV n)
      (⟨le_rfl, (hs n).1⟩ : (0 : ℝ) ∈ Icc 0 (s n)) (⟨(hs n).1, le_rfl⟩ : s n ∈ Icc 0 (s n))
    have heq : (⟨γ n 0, htrV n 0 ⟨le_rfl, (hs n).1⟩⟩ : V) = ⟨xs n, hxV n⟩ :=
      Subtype.ext (hγ0 n)
    rw [heq] at h1
    refine h1.trans (le_of_eq ?_)
    exact len_eq_weylWL_of_eqOn D E ξ f fb hforget hE hD
      (fun t ht => hfb (hUR (hVU (htrV n t ht))))
  
  have hxlim : Tendsto (fun k => ((⟨xs (φ k), hxV (φ k)⟩ : V) : ℂ)) atTop
      (𝓝 ((⟨x, Metric.mem_closedBall_self hr.le⟩ : V) : ℂ)) := hx.comp hφ.tendsto_atTop
  have halim : Tendsto (fun k => ((⟨as (φ k), haV (φ k)⟩ : V) : ℂ)) atTop
      (𝓝 ((⟨a, Metric.sphere_subset_closedBall ha⟩ : V) : ℂ)) := haφ
  have hlim := buffered_internal_liminf (G := fun _ => E) tendsto_const_nhds
    (V := V) (K := V) (U := U) subset_rfl (isCompact_closedBall x r) hVU
    (fun k => ⟨xs (φ k), hxV (φ k)⟩) (fun k => ⟨as (φ k), haV (φ k)⟩)
    ⟨x, Metric.mem_closedBall_self hr.le⟩ ⟨a, Metric.sphere_subset_closedBall ha⟩
    hxlim halim
  set I : ℝ≥0∞ := E.internal U (⟨x, hVU (Metric.mem_closedBall_self hr.le)⟩,
    ⟨a, hVU (Metric.sphere_subset_closedBall ha)⟩)
  have hlim' : I ≤ liminf (fun k => E.internal V (⟨xs (φ k), hxV (φ k)⟩,
      ⟨as (φ k), haV (φ k)⟩)) atTop := hlim
  have hIT : I ≤ T := by
    refine hlim'.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_))
    refine (hinit (φ k)).trans (le_trans ?_ (hγT (φ k)).le)
    unfold weylWL
    exact HigherDimLQGMetric.weightedLength_mono_interval le_rfl (hs (φ k)).1 (hs (φ k)).2
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top hTtop hIT
  
  obtain ⟨α, aα, bα, hα, hαU, hα0, hα1, hαlen⟩ :=
    Uniqueness.Objects.Producer.exists_curve_of_internal_lt E
      (hVU (Metric.mem_closedBall_self hr.le)) (hVU (Metric.sphere_subset_closedBall ha))
      (ENNReal.lt_add_right hItop (ENNReal.ofReal_pos.2 hδ4).ne')
  
  have hDxa : D (x, a) < ⊤ := by
    have h1 : E (x, a) ≤ I := by
      have := B2.PfeLocal.edist_le_internal E U
        (⟨x, hVU (Metric.mem_closedBall_self hr.le)⟩,
          ⟨a, hVU (Metric.sphere_subset_closedBall ha)⟩)
      exact this
    have h2 := Uniqueness.Toolkit.WeylShift.distance_lower D E ξ fb (-M) hforget hE
      (fun z => (hfb2 z).1) hξ x a
    have hpos : ENNReal.ofReal (Real.exp (ξ * -M)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have h3 : ENNReal.ofReal (Real.exp (ξ * -M)) * D (x, a) < ⊤ :=
      lt_of_le_of_lt (h2.trans h1) (lt_top_iff_ne_top.2 hItop)
    rcases ENNReal.mul_lt_top_iff.1 h3 with h | h | h
    · exact h.2
    · exact absurd h hpos
    · rw [h]; exact ENNReal.zero_lt_top
  have hxa : x ≠ a := by
    intro h; rw [← h, Metric.mem_sphere, dist_self] at ha; linarith
  have hnsa : PfeWeyl.IsNonsingular D a :=
    ⟨x, hxa, by rw [D.isExtMetric.2.2.1]; exact hDxa⟩
  
  set δ'' : ℝ := δ / 4 / Real.exp (ξ * M)
  have hδ'' : 0 < δ'' := div_pos hδ4 (Real.exp_pos _)
  obtain ⟨A, hzA, hAρ, hAδ⟩ := hSSA a (mem_univ _) hnsa δ'' hδ'' (r / 4) (by positivity)
  obtain ⟨π, sπ, tπ, hπ, hπA, hπsep, hπlen⟩ := PfeWeyl.aroundDist_exists_curve_lt D A hAδ
  have hAE : aroundDist E A < ENNReal.ofReal (δ / 4) := by
    have hlenE := (Uniqueness.Toolkit.WeylShift.length_bounds D E ξ hξ fb (-M) M hforget hE
      hfb2 hπ).2
    have hEle : aroundDist E A ≤ E.len π sπ tπ := by
      unfold aroundDist
      exact iInf_le_of_le π <| iInf_le_of_le sπ <| iInf_le_of_le tπ <|
        iInf_le_of_le (hEcurve hπ) <| iInf_le_of_le hπA <| iInf_le_of_le hπsep le_rfl
    refine lt_of_le_of_lt (hEle.trans hlenE) ?_
    calc ENNReal.ofReal (Real.exp (ξ * M)) * D.len π sπ tπ
        < ENNReal.ofReal (Real.exp (ξ * M)) * ENNReal.ofReal δ'' :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
            ENNReal.ofReal_ne_top hπlen
      _ = ENNReal.ofReal (δ / 4) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          simp only [δ'']
          field_simp
  
  have hball_sub : Metric.ball A.center A.outerRadius ⊆ Metric.ball a (r / 2) := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have := dist_triangle z A.center a
    rw [dist_comm A.center a] at this
    linarith [A.innerRadius_lt_outerRadius]
  have hxout : x ∉ Metric.ball A.center A.outerRadius := by
    intro hxin
    have h1 := hball_sub hxin
    rw [Metric.mem_ball, dist_comm] at h1
    rw [Metric.mem_sphere] at ha
    linarith
  have haIn : a ∈ Metric.ball A.center A.innerRadius := by
    rw [Metric.mem_ball]; exact hzA
  
  set V' : Set ℂ := Metric.ball 0 R
  have hV'R : V' ⊆ Metric.closedBall 0 R := Metric.ball_subset_closedBall
  have hR2 : ∀ z, dist z x < 2 * r → z ∈ V' := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z x
    rw [← dist_eq_norm] at this
    linarith
  have hAV' : A.toSet ⊆ V' := fun z hz => by
    apply hR2
    have h1 := hball_sub hz.1
    rw [Metric.mem_ball] at h1
    rw [Metric.mem_sphere] at ha
    have := dist_triangle z a x
    linarith
  
  have hev : ∀ᶠ k in atTop, weylScale ξ f D (x, ys (φ k)) < T + ENNReal.ofReal δ := by
    have hinner : ∀ᶠ k in atTop, as (φ k) ∈ Metric.ball A.center A.innerRadius :=
      haφ (Metric.isOpen_ball.mem_nhds haIn)
    have hI_ev := eventually_lt_add_of_le_liminf hlim' hItop hδ4
    filter_upwards [hinner, hI_ev] with k hk hIk
    set n := φ k
    
    have hsn1 : s n ≤ 1 := (hs n).2
    have hstart : γ n (s n) ∈ Metric.ball a (r / 2) :=
      hball_sub (Metric.ball_subset_ball A.innerRadius_lt_outerRadius.le hk)
    have hend : γ n 1 ∉ Metric.ball a (r / 2) := by
      rw [hγ1 n, Metric.mem_ball, not_lt]
      have h1 := hys n
      rw [Metric.mem_sphere] at ha
      have := dist_triangle (ys n) a x
      linarith
    obtain ⟨u, hu, huS, huBall⟩ := exists_first_exit hsn1
      ((continuousOn_of_isCurve_forget D hforget (hγ n)).mono
        (Icc_subset_Icc (hs n).1 le_rfl)) hstart hend
    have hQD : D.IsCurve (γ n) (s n) u := isCurve_sub (hγ n) (hs n).1 hu.1 hu.2
    have hQtr : ∀ t ∈ Icc (s n) u, γ n t ∈ Metric.closedBall a (r / 2) := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; exact Metric.sphere_subset_closedBall huS
      · exact Metric.ball_subset_closedBall (huBall t ⟨ht.1, h⟩)
    have hQV' : ∀ t ∈ Icc (s n) u, γ n t ∈ V' := by
      intro t ht
      apply hR2
      have h1 := Metric.mem_closedBall.1 (hQtr t ht)
      rw [Metric.mem_sphere] at ha
      have := dist_triangle (γ n t) a x
      linarith
    have hαV' : ∀ t ∈ Icc aα bα, α t ∈ V' := fun t ht => hR2 _ (Metric.mem_ball.1 (hαU t ht))
    have hjoin := buffered_annular_join_of_around_lt E hEforget A hAV' hα (hEcurve hQD)
      hαV' hQV' (by rw [hα0]; exact hxout)
      (by rw [hα1]; exact Metric.ball_subset_closedBall haIn)
      (Metric.ball_subset_closedBall hk)
      (fun hin => by
        have h1 := hball_sub hin
        rw [Metric.mem_ball, Metric.mem_sphere.1 huS] at h1
        exact lt_irrefl _ h1)
      hAE
    
    have hW1 : weylScale ξ f D (x, γ n u) ≤ E.len α aα bα + ENNReal.ofReal (δ / 4) +
        E.len (γ n) (s n) u := by
      have h := weylScale_le_internal_of_eqOn D E ξ hξ f fb hforget hE (-M)
        (fun z => (hfb2 z).1) (V := V') (hfb.mono hV'R)
        ⟨α aα, hαV' aα ⟨le_rfl, hα.1⟩⟩ ⟨γ n u, hQV' u ⟨hu.1, le_rfl⟩⟩
      calc weylScale ξ f D (x, γ n u) = weylScale ξ f D (α aα, γ n u) := by rw [hα0]
        _ ≤ _ := h.trans hjoin
    have hQlen : E.len (γ n) (s n) u = weylWL D ξ f (γ n) (s n) u :=
      len_eq_weylWL_of_eqOn D E ξ f fb hforget hE hQD (fun t ht => hfb (hV'R (hQV' t ht)))
    have hW2 : weylScale ξ f D (γ n u, ys n) ≤ weylWL D ξ f (γ n) u 1 := by
      have h := weylScale_le_weylWL D ξ f hforget
        (isCurve_sub (hγ n) ((hs n).1.trans hu.1) hu.2 le_rfl)
      rw [hγ1 n] at h
      exact h
    have hsplit : weylWL D ξ f (γ n) 0 (s n) + weylWL D ξ f (γ n) (s n) u +
        weylWL D ξ f (γ n) u 1 = weylWL D ξ f (γ n) 0 1 := by
      unfold weylWL
      rw [HigherDimLQGMetric.weightedLength_add (hs n).1 hu.1,
        HigherDimLQGMetric.weightedLength_add ((hs n).1.trans hu.1) hu.2]
    have hαI : E.len α aα bα ≤ I + ENNReal.ofReal (δ / 4) := hαlen.le
    have hIe : I ≤ weylWL D ξ f (γ n) 0 (s n) + ENNReal.ofReal (δ / 4) :=
      hIk.le.trans (add_le_add (hinit n) le_rfl)
    have hδsum : ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) ≤
        ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add hδ4.le hδ4.le, ← ENNReal.ofReal_add (by positivity) hδ4.le]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc weylScale ξ f D (x, ys n)
        ≤ weylScale ξ f D (x, γ n u) + weylScale ξ f D (γ n u, ys n) := hWtri _ _ _
      _ ≤ (E.len α aα bα + ENNReal.ofReal (δ / 4) + E.len (γ n) (s n) u) +
          weylWL D ξ f (γ n) u 1 := add_le_add hW1 hW2
      _ ≤ ((weylWL D ξ f (γ n) 0 (s n) + ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4)) +
          ENNReal.ofReal (δ / 4) + weylWL D ξ f (γ n) (s n) u) + weylWL D ξ f (γ n) u 1 := by
          rw [hQlen]
          gcongr
          exact hαI.trans (add_le_add hIe le_rfl)
      _ = weylWL D ξ f (γ n) 0 1 + (ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) +
          ENNReal.ofReal (δ / 4)) := by
          rw [← hsplit]; ring
      _ < T + ENNReal.ofReal δ :=
          ENNReal.add_lt_add_of_lt_of_le (ENNReal.add_ne_top.2
            ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
              ENNReal.ofReal_ne_top⟩) (hγT n) hδsum
  exact hφ.tendsto_atTop.frequently hev.frequently

end SupercriticalLQGUniqueness.B2.PfeAxioms
