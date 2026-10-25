import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Bridge.OptimalBridge
import LQGMetric.Papers.LM.T1_7G2
import LQGMetric.Metric.InternalOps




 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Transfer

 
theorem isCurve_of_allPairs_le (D E : LSCMetric) (c : NNReal)
    (h : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    E.IsCurve P a b := by
  have hLip :
      @LipschitzWith D.Space E.Space D.instEMetricSpace.toPseudoEMetricSpace
        E.instEMetricSpace.toPseudoEMetricSpace c (fun x => x) := by
    intro x y
    change E (x, y) ≤ (c : ℝ≥0∞) * D (x, y)
    exact h x y
  refine ⟨hP.1, ?_⟩
  convert hLip.continuous.comp_continuousOn hP.2 using 1
  rfl

 
theorem len_le_mul_of_allPairs_le (D E : LSCMetric) (c : NNReal)
    (h : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) :
    E.len P a b ≤ (c : ℝ≥0∞) * D.len P a b := by
  exact LQGMetric.LM.t17_eVariationOn_le_mul
    (g := D.pt ∘ P) (g' := E.pt ∘ P) (s := Icc a b) (c := (c : ℝ≥0∞))
    (fun x _ y _ => h (P x) (P y))

 
theorem aroundDist_le_mul_of_allPairs_le (D E : LSCMetric) (c : NNReal)
    (hc : 0 < c)
    (h : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (A : EuclideanAnnulus) :
    aroundDist E A ≤ (c : ℝ≥0∞) * aroundDist D A := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hcTop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hbound (P : ℝ → ℂ) (a b : ℝ)
      (hP : D.IsCurve P a b)
      (hA : ∀ t ∈ Icc a b, P t ∈ A.toSet)
      (hsep : Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary) :
      aroundDist E A ≤ (c : ℝ≥0∞) * D.len P a b := by
    have hcost : aroundDist E A ≤ E.len P a b := by
      unfold aroundDist
      refine iInf_le_of_le (i := P) ?_
      refine iInf_le_of_le (i := a) ?_
      refine iInf_le_of_le (i := b) ?_
      refine iInf_le_of_le (i := isCurve_of_allPairs_le D E c h hP) ?_
      refine iInf_le_of_le (i := hA) ?_
      exact iInf_le _ hsep
    exact hcost.trans (len_le_mul_of_allPairs_le D E c h P a b)
  conv_rhs => rw [aroundDist]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun hA => le_iInf fun hsep => ?_
  exact hbound P a b hP hA hsep

 
theorem endpoint_outer_balls_disjoint
    (r : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (δ : ℝ) (hδB : δ ≤ (1 - (a : ℝ)) ^ 4)
    {u v : ℂ}
    (hu : u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r))
    (hv : v ∈ Metric.sphere (0 : ℂ) r) :
    Disjoint (Metric.ball u (Real.sqrt δ * r))
      (Metric.ball v (Real.sqrt δ * r)) := by
  have ht0 : 0 < 1 - (a : ℝ) := by linarith only [a.property.2]
  have ht4 : 1 - (a : ℝ) < 1 / 4 := by linarith only [a.property.1]
  have hsqrt : Real.sqrt δ ≤ (1 - (a : ℝ)) ^ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨sq_nonneg _, by nlinarith only [hδB]⟩
  have hsmall : 2 * Real.sqrt δ < 1 - (a : ℝ) := by
    nlinarith only [hsqrt, ht0, ht4, sq_nonneg (1 - (a : ℝ))]
  have hu' : dist u (0 : ℂ) = (a : ℝ) * r := by
    simpa only [Metric.mem_sphere, dist_comm] using hu
  have hv' : dist v (0 : ℂ) = r := by
    simpa only [Metric.mem_sphere, dist_comm] using hv
  have hgap : (1 - (a : ℝ)) * r ≤ dist u v := by
    have h := (le_abs_self (dist v (0 : ℂ) - dist u (0 : ℂ))).trans
      (abs_dist_sub_le v u 0)
    rw [hv', hu', dist_comm] at h
    nlinarith only [h]
  apply Metric.ball_disjoint_ball
  have hmul := mul_lt_mul_of_pos_right hsmall r.property
  nlinarith only [hgap, hmul]

 

theorem two_endpoint_separator_contacts
    {P : ℝ → ℂ} {s t : ℝ} {u v : ℂ} {rU RU rV RV : ℝ}
    {KU KV : Set ℂ}
    (hst : s ≤ t) (hP : ContinuousOn P (Icc s t))
    (hu : P s ∈ Metric.closedBall u rU)
    (hv : P t ∈ Metric.closedBall v rV)
    (huSub : Metric.closedBall u rU ⊆ Metric.ball u RU)
    (hvSub : Metric.closedBall v rV ⊆ Metric.ball v RV)
    (hdisj : Disjoint (Metric.ball u RU) (Metric.ball v RV))
    (hrU : rU ≤ RU) (hrV : rV ≤ RV)
    (hsepU : LQGMetric.Disconnects KU (Metric.sphere u rU) (Metric.sphere u RU))
    (hsepV : LQGMetric.Disconnects KV (Metric.sphere v rV) (Metric.sphere v RV)) :
    ∃ p q : ℝ, s ≤ p ∧ p ≤ q ∧ q ≤ t ∧ P p ∈ KU ∧ P q ∈ KV := by
  have hmid : ∃ τ ∈ Icc s t,
      P τ ∉ Metric.ball u RU ∪ Metric.ball v RV := by
    by_contra hn
    have hsub : P '' Icc s t ⊆ Metric.ball u RU ∪ Metric.ball v RV := by
      rintro x ⟨τ, hτ, rfl⟩
      by_contra hbad
      exact hn ⟨τ, hτ, hbad⟩
    have hconn : IsPreconnected (P '' Icc s t) :=
      isPreconnected_Icc.image P hP
    have hleft : ((P '' Icc s t) ∩ Metric.ball u RU).Nonempty :=
      ⟨P s, ⟨s, ⟨le_rfl, hst⟩, rfl⟩, huSub hu⟩
    have hAllU := hconn.subset_left_of_subset_union Metric.isOpen_ball
      Metric.isOpen_ball hdisj hsub hleft
    have hPtU : P t ∈ Metric.ball u RU :=
      hAllU ⟨t, ⟨hst, le_rfl⟩, rfl⟩
    exact (Set.disjoint_left.mp hdisj hPtU) (hvSub hv)
  obtain ⟨τ, hτ, hτout⟩ := hmid
  have hτu : P τ ∉ Metric.ball u RU := fun h => hτout (Or.inl h)
  have hτv : P τ ∉ Metric.ball v RV := fun h => hτout (Or.inr h)
  have hpcU : IsPathConnected (P '' Icc s τ) :=
    ((convex_Icc s τ).isPathConnected ⟨s, ⟨le_rfl, hτ.1⟩⟩).image'
      (hP.mono (Icc_subset_Icc le_rfl hτ.2))
  have hjoinedU : JoinedIn (P '' Icc s τ) (P s) (P τ) :=
    hpcU.joinedIn (P s) ⟨s, ⟨le_rfl, hτ.1⟩, rfl⟩
      (P τ) ⟨τ, ⟨hτ.1, le_rfl⟩, rfl⟩
  have hsepU' := LQGMetric.Disconnects.closedBall_compl_ball hrU hsepU
  obtain ⟨wu, ⟨pu, rfl⟩, hwuK⟩ := hsepU' (P s) (P τ)
    hjoinedU.somePath hu hτu
  obtain ⟨p, hp, hPp⟩ := hjoinedU.somePath_mem pu
  have hpK : P p ∈ KU := hPp ▸ hwuK
  have hpcV : IsPathConnected (P '' Icc τ t) :=
    ((convex_Icc τ t).isPathConnected ⟨τ, ⟨le_rfl, hτ.2⟩⟩).image'
      (hP.mono (Icc_subset_Icc hτ.1 le_rfl))
  have hjoined : JoinedIn (P '' Icc τ t) (P τ) (P t) :=
    hpcV.joinedIn (P τ) ⟨τ, ⟨le_rfl, hτ.2⟩, rfl⟩
      (P t) ⟨t, ⟨hτ.2, le_rfl⟩, rfl⟩
  have hsepV' := (LQGMetric.Disconnects.closedBall_compl_ball hrV hsepV).symm
  obtain ⟨w, ⟨q, rfl⟩, hwK⟩ := hsepV' (P τ) (P t)
    hjoined.somePath hτv hv
  obtain ⟨q', hq', hPq'⟩ := hjoined.somePath_mem q
  refine ⟨p, q', hp.1, hp.2.trans hq'.1, hq'.2, hpK, ?_⟩
  exact hPq' ▸ hwK

 
theorem trace_pair_le_len (E : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    {x y : ℂ} (hx : x ∈ P '' Icc a b) (hy : y ∈ P '' Icc a b) :
    E (x, y) ≤ E.len P a b := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rcases le_total s t with hst | hts
  · change edist (E.pt (P s)) (E.pt (P t)) ≤
      LQGMetric.MetricGeometry.curveLength (E.pt ∘ P) a b
    exact (LQGMetric.MetricGeometry.edist_le_curveLength (E.pt ∘ P) hst).trans
      (LQGMetric.MetricGeometry.curveLength_mono (E.pt ∘ P) hs.1 ht.2)
  · change edist (E.pt (P s)) (E.pt (P t)) ≤
      LQGMetric.MetricGeometry.curveLength (E.pt ∘ P) a b
    rw [edist_comm]
    exact (LQGMetric.MetricGeometry.edist_le_curveLength (E.pt ∘ P) hts).trans
      (LQGMetric.MetricGeometry.curveLength_mono (E.pt ∘ P) ht.1 hs.2)

 

theorem connector_hits_separator
    {Q : ℝ → ℂ} {a b : ℝ} {z : ℂ} {r R : ℝ} {K : Set ℂ}
    (hab : a ≤ b) (hQ : ContinuousOn Q (Icc a b))
    (hrR : r ≤ R)
    (hsep : LQGMetric.Disconnects K (Metric.sphere z r) (Metric.sphere z R))
    (ha : Q a ∈ Metric.closedBall z r)
    (hb : Q b ∈ Metric.sphere z R) :
    ∃ q ∈ Icc a b, Q q ∈ K := by
  have hout : Q b ∉ Metric.ball z R := by
    rw [Metric.mem_sphere] at hb
    simpa only [Metric.mem_ball, not_lt] using hb.symm.le
  have hpc : IsPathConnected (Q '' Icc a b) :=
    ((convex_Icc a b).isPathConnected ⟨a, ⟨le_rfl, hab⟩⟩).image' hQ
  have hj : JoinedIn (Q '' Icc a b) (Q a) (Q b) :=
    hpc.joinedIn (Q a) ⟨a, ⟨le_rfl, hab⟩, rfl⟩
      (Q b) ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  obtain ⟨w, ⟨q, rfl⟩, hwK⟩ :=
    (LQGMetric.Disconnects.closedBall_compl_ball hrR hsep)
      (Q a) (Q b) hj.somePath ha hout
  obtain ⟨q', hq', hQq'⟩ := hj.somePath_mem q
  exact ⟨q', hq', hQq' ▸ hwK⟩

 

theorem two_endpoint_paid_paths (E : LSCMetric)
    {u v : ℂ} {rU RU rV RV : ℝ}
    {P Qu Qv πu πv : ℝ → ℂ}
    {s t au bu av bv αu βu αv βv : ℝ}
    (hst : s ≤ t) (hP : ContinuousOn P (Icc s t))
    (hPs : P s ∈ Metric.closedBall u rU)
    (hPt : P t ∈ Metric.closedBall v rV)
    (hrU0 : 0 ≤ rU) (hrV0 : 0 ≤ rV)
    (hrU : rU ≤ RU) (hrV : rV ≤ RV)
    (huSub : Metric.closedBall u rU ⊆ Metric.ball u RU)
    (hvSub : Metric.closedBall v rV ⊆ Metric.ball v RV)
    (hdisj : Disjoint (Metric.ball u RU) (Metric.ball v RV))
    (hQu : au ≤ bu) (hQv : av ≤ bv)
    (hQucont : ContinuousOn Qu (Icc au bu))
    (hQvcont : ContinuousOn Qv (Icc av bv))
    (hQua : Qu au = u) (hQva : Qv av = v)
    (hQub : Qu bu ∈ Metric.sphere u RU)
    (hQvb : Qv bv ∈ Metric.sphere v RV)
    (hsepU : LQGMetric.Disconnects (πu '' Icc αu βu)
      (Metric.sphere u rU) (Metric.sphere u RU))
    (hsepV : LQGMetric.Disconnects (πv '' Icc αv βv)
      (Metric.sphere v rV) (Metric.sphere v RV)) :
    E (u, v) ≤ E.len Qu au bu + E.len πu αu βu + E.len P s t +
      E.len πv αv βv + E.len Qv av bv := by
  obtain ⟨p, q, hp0, hpq, hqt, hpU, hqV⟩ :=
    two_endpoint_separator_contacts hst hP hPs hPt huSub hvSub hdisj
      hrU hrV hsepU hsepV
  obtain ⟨cu, hcu, hcuK⟩ := connector_hits_separator hQu hQucont
    hrU hsepU (hQua ▸ Metric.mem_closedBall_self hrU0) hQub
  obtain ⟨cv, hcv, hcvK⟩ := connector_hits_separator hQv hQvcont
    hrV hsepV (hQva ▸ Metric.mem_closedBall_self hrV0) hQvb
  have huc : E (u, Qu cu) ≤ E.len Qu au bu :=
    trace_pair_le_len E Qu ⟨au, ⟨le_rfl, hQu⟩, hQua⟩ ⟨cu, hcu, rfl⟩
  have hloopU : E (Qu cu, P p) ≤ E.len πu αu βu :=
    trace_pair_le_len E πu hcuK hpU
  have hmiddle : E (P p, P q) ≤ E.len P s t :=
    trace_pair_le_len E P ⟨p, ⟨hp0, hpq.trans hqt⟩, rfl⟩
      ⟨q, ⟨hp0.trans hpq, hqt⟩, rfl⟩
  have hloopV : E (P q, Qv cv) ≤ E.len πv αv βv :=
    trace_pair_le_len E πv hqV hcvK
  have hvc : E (Qv cv, v) ≤ E.len Qv av bv :=
    trace_pair_le_len E Qv ⟨cv, hcv, rfl⟩
      ⟨av, ⟨le_rfl, hQv⟩, hQva⟩
  calc
    E (u, v) ≤ E (u, Qu cu) + E (Qu cu, P p) + E (P p, P q) +
        E (P q, Qv cv) + E (Qv cv, v) := by
          have h1 := E.isExtMetric.2.2.2 u (Qu cu) v
          have h2 := E.isExtMetric.2.2.2 (Qu cu) (P p) v
          have h3 := E.isExtMetric.2.2.2 (P p) (P q) v
          have h4 := E.isExtMetric.2.2.2 (P q) (Qv cv) v
          simp only [hQua, hQva] at *
          exact le_trans h1 (by
            calc E (u, Qu cu) + E (Qu cu, v)
                ≤ E (u, Qu cu) + (E (Qu cu, P p) + E (P p, v)) :=
                  by gcongr
              _ ≤ E (u, Qu cu) + (E (Qu cu, P p) +
                    (E (P p, P q) + E (P q, v))) :=
                  by gcongr
              _ ≤ E (u, Qu cu) + (E (Qu cu, P p) +
                    (E (P p, P q) + (E (P q, Qv cv) + E (Qv cv, v)))) :=
                  by gcongr
              _ = _ := by ac_rfl)
    _ ≤ E.len Qu au bu + E.len πu αu βu + E.len P s t +
        E.len πv αv βv + E.len Qv av bv := by
          exact add_le_add (add_le_add (add_le_add (add_le_add huc hloopU) hmiddle)
            hloopV) hvc


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Transfer
