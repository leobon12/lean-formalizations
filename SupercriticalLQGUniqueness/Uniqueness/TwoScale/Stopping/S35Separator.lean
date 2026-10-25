import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PaidTraces
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.S35Deterministic




 






set_option autoImplicit false
noncomputable section
open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping

 



theorem outer_passage_le_around (D : LSCMetric) {P : ℝ → ℂ}
    {T a s' t' b r : ℝ} {c : ℂ}
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hr : 0 < r) (ha : 0 ≤ a) (has : a < s') (hst : s' ≤ t')
    (htb : t' < b) (hb : b ≤ T)
    (hPa : 2 * r ≤ dist (P a) c)
    (hPs : dist (P s') c ≤ 3 * r / 2)
    (hPt : dist (P t') c ≤ 3 * r / 2)
    (hPb : 2 * r ≤ dist (P b) c) :
    ENNReal.ofReal (t' - s') ≤
      aroundDist D ⟨(c, (3 * r / 2, 2 * r)), by constructor <;> nlinarith⟩ := by
  let A : EuclideanAnnulus :=
    ⟨(c, (3 * r / 2, 2 * r)), by constructor <;> nlinarith⟩
  change ENNReal.ofReal (t' - s') ≤ aroundDist D A
  exact Toolkit.PlanarSeparation.separator_twoSidedShortcut_around
    D A ha has hst htb hb hP hgeo hunit hPa hPs hPt hPb

 


theorem tiny_across_le_outer_passage (D : LSCMetric) {P : ℝ → ℂ}
    {T s' t t' r ρ σ : ℝ} {c : ℂ}
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hs't : s' ≤ t) (htt' : t < t') (ht'T : t' ≤ T)
    (hs'0 : 0 ≤ s')
    (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ < r / 2)
    (hPt : dist (P t) c = r)
    (hPt' : dist (P t') c = 3 * r / 2) :
    acrossDist D ⟨(P t, (ρ, σ)), ⟨hρ, hρσ⟩⟩ ≤
      ENNReal.ofReal (t' - s') := by
  have hfar : σ < dist (P t') (P t) := by
    have htri := dist_triangle (P t') (P t) c
    rw [hPt, hPt'] at htri
    linarith
  obtain ⟨u, v, htu, huv, hvt', hu, hv, _⟩ :=
    Toolkit.PlanarSeparation.crossing_extract htt'.le
      (hP.mono (Icc_subset_Icc (hs'0.trans hs't) ht'T)) hρσ
      (by rw [dist_self]; exact hρ) hfar
  let A : EuclideanAnnulus := ⟨(P t, (ρ, σ)), ⟨hρ, hρσ⟩⟩
  have hcross : acrossDist D A ≤ D (P u, P v) := by
    unfold acrossDist
    exact iInf_le_of_le (P u) (iInf_le_of_le
      (by simpa only [A, EuclideanAnnulus.innerBoundary, EuclideanAnnulus.center,
          EuclideanAnnulus.innerRadius, mem_sphere] using hu)
      (iInf_le_of_le (P v) (iInf_le_of_le
        (by simpa only [A, EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center,
            EuclideanAnnulus.outerRadius, mem_sphere] using hv) le_rfl)))
  have huT : u ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have hvT : v ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have htime : D (P u, P v) = ENNReal.ofReal (v - u) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit huT hvT huv.le
  calc
    acrossDist D A ≤ D (P u, P v) := hcross
    _ = ENNReal.ofReal (v - u) := htime
    _ ≤ ENNReal.ofReal (t' - s') := ENNReal.ofReal_le_ofReal (by linarith)

 

theorem covered_step_outer_times {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : CoveredStep P Good ε b α z w)
    (hP : ContinuousOn P (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hr : 0 < st.radius) (ha0 : 0 ≤ st.a) (htT : st.t < T) :
    ∃ s' t' : ℝ, 0 < s' ∧ s' < st.a ∧ st.t < t' ∧ t' < T ∧
      dist (P s') st.center = 3 * st.radius / 2 ∧
      dist (P t') st.center = 3 * st.radius / 2 := by
  have hcont₁ : ContinuousOn P (Icc 0 st.a) :=
    hP.mono (Icc_subset_Icc le_rfl (by linarith [st.a_lt_s, st.s_lt_t]))
  have hcont₂ : ContinuousOn P (Icc st.t T) :=
    hP.mono (Icc_subset_Icc (by linarith [ha0, st.a_lt_s, st.s_lt_t]) le_rfl)
  have h0far : 2 * st.radius < dist (P 0) st.center := by
    rw [hP0, dist_comm]
    exact st.z_far
  have hTfar : 2 * st.radius < dist (P T) st.center := by
    rw [hPT, dist_comm]
    exact st.w_far
  have hastart : dist (P st.a) st.center < 3 * st.radius / 2 := by
    have h := mem_ball.mp st.start_half
    nlinarith
  obtain ⟨σ, s', hσ0, hσs, hs'a, _, hsphere, _⟩ :=
    Toolkit.PlanarSeparation.crossing_extract_reverse ha0 hcont₁
      (by linarith : 3 * st.radius / 2 < 2 * st.radius)
      h0far hastart
  have hs'a' : s' < st.a := by
    rcases eq_or_lt_of_le hs'a with heq | hlt
    · rw [heq] at hsphere
      linarith
    · exact hlt
  have hs'0 : 0 < s' := lt_of_le_of_lt hσ0 hσs
  have htinside : dist (P st.t) st.center < 3 * st.radius / 2 := by
    have h := mem_sphere.mp st.outer_hit
    linarith
  obtain ⟨t', τ, ht_t', ht'τ, hτT, ht'sphere, _, _⟩ :=
    Toolkit.PlanarSeparation.crossing_extract htT.le hcont₂
      (by linarith : 3 * st.radius / 2 < 2 * st.radius)
      htinside hTfar
  have ht_t'' : st.t < t' := by
    rcases eq_or_lt_of_le ht_t' with heq | hlt
    · rw [← heq] at ht'sphere
      linarith [mem_sphere.mp st.outer_hit]
    · exact hlt
  exact ⟨s', t', hs'0, hs'a', ht_t'', ht'τ.trans_le hτT,
    hsphere, ht'sphere⟩

 

theorem covered_step_loop_bounds (D : LSCMetric) {P : ℝ → ℂ}
    {Good : ℂ → ℝ → Prop} {ε b α T ρ σ : ℝ} {z w : ℂ}
    (st : CoveredStep P Good ε b α z w)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hr : 0 < st.radius) (ha0 : 0 ≤ st.a) (htT : st.t < T)
    (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ < st.radius / 2) :
    ∃ s' t' : ℝ, s' < st.a ∧ st.t < t' ∧
      st.t - st.s ≤ t' - s' ∧
      ENNReal.ofReal (t' - s') ≤ aroundDist D
        ⟨(st.center, (3 * st.radius / 2, 2 * st.radius)), by constructor <;> nlinarith⟩ ∧
      acrossDist D ⟨(P st.t, (ρ, σ)), ⟨hρ, hρσ⟩⟩ ≤
        ENNReal.ofReal (t' - s') := by
  obtain ⟨s', t', hs'0, hs'a, ht_t', ht'T, hsphere, ht'sphere⟩ :=
    covered_step_outer_times st hP hP0 hPT hr ha0 htT
  refine ⟨s', t', hs'a, ht_t', by linarith [st.a_lt_s], ?_, ?_⟩
  · exact outer_passage_le_around D hP hgeo hunit hr le_rfl hs'0
      (by linarith [st.a_lt_s, st.s_lt_t, ht_t']) ht'T le_rfl
      (by rw [hP0, dist_comm]; linarith [st.z_far]) hsphere.le
      ht'sphere.le (by rw [hPT, dist_comm]; linarith [st.w_far])
  · exact tiny_across_le_outer_passage D hP hgeo hunit
      (by linarith [hs'a, st.a_lt_s, st.s_lt_t]) ht_t' ht'T.le
      hs'0.le hρ hρσ hσ (mem_sphere.mp st.outer_hit) ht'sphere

 


theorem ordinary_increment_le_K_crossing (D : LSCMetric) {P : ℝ → ℂ}
    {T a s t r α K : ℝ} {c z w : ℂ}
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hr : 0 < r) (hα : 1 / 2 < α) (hα1 : α < 1) (hK : 0 ≤ K)
    (ha : 0 < a) (has : a < s) (hst : s < t) (htT : t < T)
    (hPa : P a ∈ ball c (r / 2))
    (hPs : P s ∈ sphere c (α * r))
    (hPt : P t ∈ sphere c r)
    (hz : 2 * r < dist c z) (hw : 2 * r < dist c w)
    (hEratio : aroundDist D
        ⟨(c, (α * r, r)), by constructor <;> nlinarith⟩ ≤
      ENNReal.ofReal K * acrossDist D
        ⟨(c, (α * r, r)), by constructor <;> nlinarith⟩) :
    s - a ≤ K * (t - s) := by
  let A : EuclideanAnnulus := ⟨(c, (α * r, r)), by constructor <;> nlinarith⟩
  have houter : ENNReal.ofReal (s - a) ≤ aroundDist D A := by
    apply Toolkit.PlanarSeparation.separator_twoSidedShortcut_around
      D A (a := 0) (c := a) (e := s) (b := T)
        le_rfl ha has.le (hst.trans htT) (le_refl T) hP hgeo hunit
    · change r ≤ dist (P 0) c
      rw [hP0, dist_comm]
      linarith
    · change dist (P a) c ≤ α * r
      have h := mem_ball.mp hPa
      nlinarith
    · change dist (P s) c ≤ α * r
      exact (mem_sphere.mp hPs).le
    · change r ≤ dist (P T) c
      rw [hPT, dist_comm]
      linarith
  have hcross : acrossDist D A ≤ D (P s, P t) := by
    unfold acrossDist
    exact iInf_le_of_le (P s) (iInf_le_of_le (by simpa only [A, EuclideanAnnulus.innerBoundary, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius] using hPs)
      (iInf_le_of_le (P t) (iInf_le_of_le
        (by simpa only [A, EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center, EuclideanAnnulus.outerRadius] using hPt) le_rfl)))
  have hst0 : 0 ≤ t - s := by linarith
  have hs0 : s ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have ht0 : t ∈ Icc (0 : ℝ) T := ⟨by linarith, htT.le⟩
  have htime : D (P s, P t) = ENNReal.ofReal (t - s) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit hs0 ht0 hst.le
  have hbound : ENNReal.ofReal (s - a) ≤ ENNReal.ofReal (K * (t - s)) := by
    calc
      ENNReal.ofReal (s - a) ≤ aroundDist D A := houter
      _ ≤ ENNReal.ofReal K * acrossDist D A := hEratio
      _ ≤ ENNReal.ofReal K * D (P s, P t) := by gcongr
      _ = ENNReal.ofReal (K * (t - s)) := by rw [htime, ENNReal.ofReal_mul hK]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK hst0)).mp hbound

 


theorem increment_bounds (D D' : LSCMetric) {P : ℝ → ℂ}
    {T a s t C Cplus : ℝ}
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (ha0 : 0 ≤ a) (has : a ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (hCplus : 0 ≤ Cplus)
    (hbilip : ∀ x y : ℂ, D' (x, y) ≤ ENNReal.ofReal Cplus * D (x, y))
    (hEgeo : D' (P s, P t) ≤ ENNReal.ofReal (C * (t - s))) :
    D' (P a, P s) ≤ ENNReal.ofReal (Cplus * (s - a)) ∧
      D' (P s, P t) ≤ ENNReal.ofReal (C * (t - s)) := by
  constructor
  · have ha : a ∈ Icc (0 : ℝ) T := ⟨ha0, by linarith⟩
    have hs : s ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
    have hdist : D (P a, P s) = ENNReal.ofReal (s - a) :=
      hgeo.edist_eq_of_hasUnitSpeedOn hunit ha hs has
    calc
      D' (P a, P s) ≤ ENNReal.ofReal Cplus * D (P a, P s) := hbilip _ _
      _ = ENNReal.ofReal (Cplus * (s - a)) := by
        rw [hdist, ENNReal.ofReal_mul hCplus]
  · exact hEgeo

 

theorem covered_step_metric_bound (D D' : LSCMetric) {P : ℝ → ℂ}
    {Good : ℂ → ℝ → Prop} {ε b α T C Cplus K : ℝ} {z w : ℂ}
    (st : CoveredStep P Good ε b α z w)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hε : 0 < ε) (hb : 0 < b) (hα : 1 / 2 < α) (hα1 : α < 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hCC : C ≤ Cplus)
    (hapos : 0 < st.a) (htT : st.t < T)
    (hbilip : ∀ x y : ℂ, D' (x, y) ≤ ENNReal.ofReal Cplus * D (x, y))
    (hEratio : aroundDist D
      ⟨(st.center, (α * st.radius, st.radius)), by
        have hr : 0 < st.radius := lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b) st.radius_min
        constructor <;> nlinarith⟩ ≤
        ENNReal.ofReal K * acrossDist D
      ⟨(st.center, (α * st.radius, st.radius)), by
        have hr : 0 < st.radius := lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b) st.radius_min
        constructor <;> nlinarith⟩)
    (hEgeo : D' (P st.s, P st.t) ≤ ENNReal.ofReal (C * (st.t - st.s))) :
    D' (P st.a, P st.t) ≤ ENNReal.ofReal
      ((C + K / (K + 1) * (Cplus - C)) * (st.t - st.a)) := by
  have hr : 0 < st.radius := by
    have hεb : 0 < ε ^ 2 * b := by positivity
    exact hεb.trans_le st.radius_min
  have hshort := ordinary_increment_le_K_crossing D hP hgeo hunit hP0 hPT
    hr hα hα1 hK hapos st.a_lt_s st.s_lt_t htT st.start_half st.inner_hit
    st.outer_hit st.z_far st.w_far hEratio
  have hfrac := fraction_of_shortcut hK hshort
  have hinc := increment_bounds D D' hgeo hunit hapos.le st.a_lt_s.le
    st.s_lt_t.le htT.le (hC.trans hCC) hbilip hEgeo
  have htri := D'.isExtMetric.2.2.2 (P st.a) (P st.s) (P st.t)
  have hleft : 0 ≤ Cplus * (st.s - st.a) :=
    mul_nonneg (hC.trans hCC) (sub_nonneg.mpr st.a_lt_s.le)
  have hright : 0 ≤ C * (st.t - st.s) :=
    mul_nonneg hC (sub_nonneg.mpr st.s_lt_t.le)
  have hdiff : 0 ≤ Cplus - C := by linarith
  have hreal : Cplus * (st.s - st.a) + C * (st.t - st.s) ≤
      (C + K / (K + 1) * (Cplus - C)) * (st.t - st.a) := by
    have hmul := mul_le_mul_of_nonneg_left hfrac hdiff
    nlinarith
  calc
    D' (P st.a, P st.t) ≤ D' (P st.a, P st.s) + D' (P st.s, P st.t) := htri
    _ ≤ ENNReal.ofReal (Cplus * (st.s - st.a)) +
        ENNReal.ofReal (C * (st.t - st.s)) := add_le_add hinc.1 hinc.2
    _ = ENNReal.ofReal (Cplus * (st.s - st.a) + C * (st.t - st.s)) := by
      rw [ENNReal.ofReal_add hleft hright]
    _ ≤ ENNReal.ofReal ((C + K / (K + 1) * (Cplus - C)) * (st.t - st.a)) :=
      ENNReal.ofReal_le_ofReal hreal

 
theorem stepsEnd_ge_start {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α : ℝ} {z w : ℂ} {a : ℝ}
    (steps : List (CoveredStep P Good ε b α z w))
    (hfrom : StepsFrom a steps) : a ≤ StepsEnd a steps := by
  induction steps generalizing a with
  | nil => simp only [StepsEnd, le_refl]
  | cons st rest ih =>
      obtain ⟨ha, hrest⟩ := hfrom
      change a ≤ StepsEnd st.t rest
      calc
        a = st.a := ha.symm
        _ ≤ st.t := (st.a_lt_s.trans st.s_lt_t).le
        _ ≤ StepsEnd st.t rest := ih hrest

 

theorem metric_steps_telescope (D' : LSCMetric) {P : ℝ → ℂ}
    {Good : ℂ → ℝ → Prop} {ε b α A : ℝ} {z w : ℂ} {a : ℝ}
    (steps : List (CoveredStep P Good ε b α z w))
    (hA : 0 ≤ A) (hfrom : StepsFrom a steps)
    (hstep : ∀ st ∈ steps,
      D' (P st.a, P st.t) ≤ ENNReal.ofReal (A * (st.t - st.a))) :
    D' (P a, P (StepsEnd a steps)) ≤
      ENNReal.ofReal (A * (StepsEnd a steps - a)) := by
  induction steps generalizing a with
  | nil =>
      simpa only [StepsEnd, sub_self, mul_zero, ENNReal.ofReal_zero] using
        (le_of_eq (D'.isExtMetric.1 (P a)))
  | cons st rest ih =>
      obtain ⟨ha, hrest⟩ := hfrom
      have hstp := hstep st (List.mem_cons_self)
      have hreststep : ∀ q ∈ rest,
          D' (P q.a, P q.t) ≤ ENNReal.ofReal (A * (q.t - q.a)) := by
        intro q hq
        exact hstep q (List.mem_cons_of_mem st hq)
      have hih := ih hrest hreststep
      have hstnonneg : 0 ≤ A * (st.t - st.a) :=
        mul_nonneg hA (sub_nonneg.mpr (st.a_lt_s.trans st.s_lt_t).le)
      have hendnonneg : 0 ≤ A * (StepsEnd st.t rest - st.t) :=
        mul_nonneg hA (sub_nonneg.mpr (stepsEnd_ge_start rest hrest))
      change D' (P a, P (StepsEnd st.t rest)) ≤
        ENNReal.ofReal (A * (StepsEnd st.t rest - a))
      calc
        D' (P a, P (StepsEnd st.t rest)) ≤
            D' (P a, P st.t) + D' (P st.t, P (StepsEnd st.t rest)) :=
          D'.isExtMetric.2.2.2 _ _ _
        _ ≤ ENNReal.ofReal (A * (st.t - st.a)) +
            ENNReal.ofReal (A * (StepsEnd st.t rest - st.t)) := by
          rw [← ha]
          exact add_le_add hstp hih
        _ = ENNReal.ofReal (A * (StepsEnd st.t rest - a)) := by
          rw [← ENNReal.ofReal_add hstnonneg hendnonneg, ha]
          congr 1
          ring

 

theorem metric_steps_strict (D' : LSCMetric) {P : ℝ → ℂ}
    {Good : ℂ → ℝ → Prop} {ε b α A C' T a : ℝ} {z w : ℂ}
    (steps : List (CoveredStep P Good ε b α z w))
    (hA : 0 ≤ A) (hgap : A < C') (hT : 0 < T)
    (ha : 0 ≤ a) (hend : StepsEnd a steps ≤ T)
    (hfrom : StepsFrom a steps)
    (hstep : ∀ st ∈ steps,
      D' (P st.a, P st.t) ≤ ENNReal.ofReal (A * (st.t - st.a))) :
    D' (P a, P (StepsEnd a steps)) < ENNReal.ofReal (C' * T) := by
  have hbound := metric_steps_telescope D' steps hA hfrom hstep
  have hreal : A * (StepsEnd a steps - a) < C' * T := by
    calc
      A * (StepsEnd a steps - a) ≤ A * T :=
        mul_le_mul_of_nonneg_left (by linarith) hA
      _ < C' * T := mul_lt_mul_of_pos_right hgap hT
  have hCpos : 0 < C' * T :=
    mul_pos (lt_of_le_of_lt hA hgap) hT
  exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hCpos).mpr hreal)

 
theorem steps_start_pos {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α : ℝ} {z w : ℂ} {a : ℝ}
    (steps : List (CoveredStep P Good ε b α z w))
    (ha : 0 < a) (hfrom : StepsFrom a steps) :
    ∀ st ∈ steps, 0 < st.a := by
  induction steps generalizing a with
  | nil => simp
  | cons st rest ih =>
      obtain ⟨hsta, hrest⟩ := hfrom
      intro q hq
      rcases List.mem_cons.mp hq with heq | hmem
      · rw [heq, hsta]; exact ha
      · exact ih (ha.trans (hsta ▸ (st.a_lt_s.trans st.s_lt_t))) hrest q hmem

 
theorem stepsEnd_lt_T {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T a : ℝ} {z w : ℂ}
    (steps : List (CoveredStep P Good ε b α z w))
    (hne : steps ≠ []) (hlast : ∀ st ∈ steps, st.t < T) :
    StepsEnd a steps < T := by
  induction steps generalizing a with
  | nil => exact False.elim (hne rfl)
  | cons st rest ih =>
      change StepsEnd st.t rest < T
      cases rest with
      | nil => simpa only [StepsEnd] using hlast st (List.mem_cons_self)
      | cons q qs =>
          apply ih (by simp)
          intro k hk
          exact hlast k (List.mem_cons_of_mem st hk)

 

theorem strict_metric_telescope_from_E (D D' : LSCMetric) {P : ℝ → ℂ}
    {Good : ℂ → ℝ → Prop} {ε b α T C Cplus K C' a : ℝ} {z w : ℂ}
    (steps : List (CoveredStep P Good ε b α z w))
    (hε : 0 < ε) (hb : 0 < b) (hα : 1 / 2 < α) (hα1 : α < 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hCC : C ≤ Cplus)
    (hgap : C + K / (K + 1) * (Cplus - C) < C')
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hT : 0 < T) (ha : 0 < a)
    (hne : steps ≠ []) (hfrom : StepsFrom a steps)
    (hlast : ∀ st ∈ steps, st.t < T)
    (hbilip : ∀ x y : ℂ, D' (x, y) ≤ ENNReal.ofReal Cplus * D (x, y))
    (hEratio : ∀ st ∈ steps, aroundDist D
      ⟨(st.center, (α * st.radius, st.radius)), by
        have hr : 0 < st.radius := lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b) st.radius_min
        constructor <;> nlinarith⟩ ≤
      ENNReal.ofReal K * acrossDist D
      ⟨(st.center, (α * st.radius, st.radius)), by
        have hr : 0 < st.radius := lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b) st.radius_min
        constructor <;> nlinarith⟩)
    (hEgeo : ∀ st ∈ steps,
      D' (P st.s, P st.t) ≤ ENNReal.ofReal (C * (st.t - st.s))) :
    D' (P a, P (StepsEnd a steps)) < ENNReal.ofReal (C' * T) := by
  let A := C + K / (K + 1) * (Cplus - C)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg hC (mul_nonneg (div_nonneg hK (by linarith)) (by linarith))
  have hstarts := steps_start_pos steps ha hfrom
  have hstep : ∀ st ∈ steps,
      D' (P st.a, P st.t) ≤ ENNReal.ofReal (A * (st.t - st.a)) := by
    intro st hmem
    exact covered_step_metric_bound D D' st hP hgeo hunit hP0 hPT
      hε hb hα hα1 hK hC hCC (hstarts st hmem) (hlast st hmem)
      hbilip (hEratio st hmem) (hEgeo st hmem)
  exact metric_steps_strict D' steps hA hgap hT ha.le
    (stepsEnd_lt_T steps hne hlast).le hfrom hstep

 

theorem endpoint_ball_strict (D' : LSCMetric) {P : ℝ → ℂ}
    {ε b κ C' T a t : ℝ} {z w : ℂ}
    (hε : 0 < ε) (hb : 0 < b) (hεκ : ε ≤ κ / 32)
    (hstart : P a ∈ ball z (7 * ε * b))
    (hend : P t ∈ ball w (7 * ε * b))
    (hstrict : D' (P a, P t) < ENNReal.ofReal (C' * T)) :
    (⨅ x ∈ ball z (κ * b), ⨅ y ∈ ball w (κ * b), D' (x, y)) <
      ENNReal.ofReal (C' * T) := by
  have hrad : 7 * ε * b < κ * b := by
    have hκ : 32 * ε ≤ κ := by linarith
    nlinarith
  have ha : P a ∈ ball z (κ * b) :=
    ball_subset_ball hrad.le hstart
  have ht : P t ∈ ball w (κ * b) :=
    ball_subset_ball hrad.le hend
  exact (iInf_le_of_le (P a) (iInf_le_of_le ha
    (iInf_le_of_le (P t) (iInf_le_of_le ht le_rfl)))).trans_lt hstrict

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping

