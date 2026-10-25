import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Transfer.Transfer




 






set_option autoImplicit false
noncomputable section

open scoped ENNReal
open Set Filter Topology

namespace SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit

open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios

 

theorem le_five_infima
    {I J K L M : Type*}
    (a : I → ℝ≥0∞) (b : J → ℝ≥0∞) (c : K → ℝ≥0∞)
    (d : L → ℝ≥0∞) (e : M → ℝ≥0∞) (T : ℝ≥0∞)
    (h : ∀ i j k l m, T ≤ a i + b j + c k + d l + e m) :
    T ≤ (⨅ i, a i) + (⨅ j, b j) + (⨅ k, c k) +
      (⨅ l, d l) + (⨅ m, e m) := by
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  exact le_iInf fun m => le_iInf fun l => le_iInf fun k =>
    le_iInf fun j => le_iInf fun i => h i j k l m

 

theorem setDist_eq_curveLenInf
    (D : LSCMetric) (hD : D.IsLengthSpace) (A B : Set ℂ) :
    setDist D A B =
      ⨅ x ∈ A, ⨅ y ∈ B,
        ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ)
          (_ : D.IsCurve P a b) (_ : P a = x) (_ : P b = y),
          D.len P a b := by
  unfold setDist
  simp_rw [(D.isLengthSpace_iff_eq_iInf.mp hD)]

 

theorem closedBall_comparison_of_no_G
    (D E : LSCMetric) (C : Set.Ioi (0 : ℝ))
    (hNo : ∀ κ : Set.Ioi (0 : ℝ),
      ¬ G D E ⟨1, by norm_num⟩ κ C) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
        E (z, w) ≤ ENNReal.ofReal (C : ℝ) * D (z, w) := by
  intro z hz w hw
  by_cases hzero : D (z, w) = 0
  · have hzw : z = w := D.isExtMetric.2.1 z w hzero
    subst w
    simp only [E.isExtMetric.1, D.isExtMetric.1, mul_zero, le_refl]
  by_cases htop : D (z, w) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr C.property).ne']
    exact le_top
  have hp : RatioPair D z w := by
    apply (ratioPair_iff_finite_positive D z w).2
    refine ⟨?_, pos_iff_ne_zero.mpr hzero, lt_top_iff_ne_top.mpr htop⟩
    intro hzw
    apply hzero
    rw [hzw]
    exact D.isExtMetric.1 w
  by_contra hn
  obtain ⟨κ, hG⟩ :=
    OptimalConstants.Bridge.exists_G_one_of_strict_local_pair D E C hz hw hp (lt_of_not_ge hn)
  exact hNo κ hG

 
structure BetweenCurve (D : LSCMetric) (A B : Set ℂ) where
  path : ℝ → ℂ
  startTime : ℝ
  endTime : ℝ
  isCurve : D.IsCurve path startTime endTime
  start_mem : path startTime ∈ A
  end_mem : path endTime ∈ B

 
structure AroundCurve (D : LSCMetric) (A : EuclideanAnnulus) where
  path : ℝ → ℂ
  startTime : ℝ
  endTime : ℝ
  isCurve : D.IsCurve path startTime endTime
  trace_mem : ∀ t ∈ Set.Icc startTime endTime, path t ∈ A.toSet
  separates : Disconnects (path '' Set.Icc startTime endTime)
    A.innerBoundary A.outerBoundary

 

theorem setDist_eq_iInf_betweenCurve (D : LSCMetric) (hD : D.IsLengthSpace)
    (A B : Set ℂ) :
    setDist D A B =
      ⨅ q : BetweenCurve D A B, D.len q.path q.startTime q.endTime := by
  apply le_antisymm
  · apply le_iInf
    intro q
    have hpoint : setDist D A B ≤ D (q.path q.startTime, q.path q.endTime) :=
      iInf₂_le_of_le _ q.start_mem (iInf₂_le _ q.end_mem)
    exact hpoint.trans (D.apply_le_len q.path q.isCurve.1)
  · rw [setDist_eq_curveLenInf D hD A B]
    refine le_iInf fun x => le_iInf fun hx => le_iInf fun y =>
      le_iInf fun hy => le_iInf fun P => le_iInf fun a =>
      le_iInf fun b => le_iInf fun hP => le_iInf fun ha =>
      le_iInf fun hb => ?_
    exact iInf_le
      (fun q : BetweenCurve D A B => D.len q.path q.startTime q.endTime)
      ⟨P, a, b, hP, ha ▸ hx, hb ▸ hy⟩

 
theorem aroundDist_eq_iInf_aroundCurve (D : LSCMetric) (A : EuclideanAnnulus) :
    aroundDist D A =
      ⨅ q : AroundCurve D A, D.len q.path q.startTime q.endTime := by
  unfold aroundDist
  apply le_antisymm
  · refine le_iInf fun q => ?_
    exact iInf_le_of_le q.path <| iInf_le_of_le q.startTime <|
      iInf_le_of_le q.endTime <| iInf_le_of_le q.isCurve <|
      iInf_le_of_le q.trace_mem <| iInf_le _ q.separates
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun htr => le_iInf fun hsep => ?_
    exact iInf_le
      (fun q : AroundCurve D A => D.len q.path q.startTime q.endTime)
      ⟨P, a, b, hP, htr, hsep⟩

 


theorem two_endpoint_infimum_splice
    (D E : LSCMetric) (c : NNReal) (hc : 0 < c)
    (hDlen : D.IsLengthSpace) (hElen : E.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → ContinuousOn P (Set.Icc a b))
    (hEreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      E.IsCurve P a b → ContinuousOn P (Set.Icc a b))
    (hcomp : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (u v : ℂ) (rU RU rV RV : ℝ)
    (AU AV : EuclideanAnnulus)
    (hrU0 : 0 ≤ rU) (hrV0 : 0 ≤ rV)
    (hrU : rU ≤ RU) (hrV : rV ≤ RV)
    (huSub : Metric.closedBall u rU ⊆ Metric.ball u RU)
    (hvSub : Metric.closedBall v rV ⊆ Metric.ball v RV)
    (hdisj : Disjoint (Metric.ball u RU) (Metric.ball v RV))
    (hAUc : AU.center = u) (hAUr : AU.innerRadius = rU)
    (hAUR : AU.outerRadius = RU)
    (hAVc : AV.center = v) (hAVr : AV.innerRadius = rV)
    (hAVR : AV.outerRadius = RV) :
    E (u, v) ≤
      (c : ℝ≥0∞) * setDist D {u} (Metric.sphere u RU) +
      (c : ℝ≥0∞) * aroundDist D AU +
      setDist E (Metric.ball u rU) (Metric.ball v rV) +
      (c : ℝ≥0∞) * aroundDist D AV +
      (c : ℝ≥0∞) * setDist D {v} (Metric.sphere v RV) := by
  let Cu := BetweenCurve D {u} (Metric.sphere u RU)
  let Cv := BetweenCurve D {v} (Metric.sphere v RV)
  let Cp := BetweenCurve E (Metric.ball u rU) (Metric.ball v rV)
  let Lu := AroundCurve D AU
  let Lv := AroundCurve D AV
  have hcost (qu : Cu) (lu : Lu) (p : Cp) (lv : Lv) (qv : Cv) :
      E (u, v) ≤
        (c : ℝ≥0∞) * D.len qu.path qu.startTime qu.endTime +
        (c : ℝ≥0∞) * D.len lu.path lu.startTime lu.endTime +
        E.len p.path p.startTime p.endTime +
        (c : ℝ≥0∞) * D.len lv.path lv.startTime lv.endTime +
        (c : ℝ≥0∞) * D.len qv.path qv.startTime qv.endTime := by
    have hsepU : LQGMetric.Disconnects
        (lu.path '' Set.Icc lu.startTime lu.endTime)
        (Metric.sphere u rU) (Metric.sphere u RU) := by
      have hs := (disconnects_iff_lqgMetric_disconnects
        lu.isCurve.isClosed_image).1 lu.separates
      simpa only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary,
        hAUc, hAUr, hAUR] using hs
    have hsepV : LQGMetric.Disconnects
        (lv.path '' Set.Icc lv.startTime lv.endTime)
        (Metric.sphere v rV) (Metric.sphere v RV) := by
      have hs := (disconnects_iff_lqgMetric_disconnects
        lv.isCurve.isClosed_image).1 lv.separates
      simpa only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary,
        hAVc, hAVr, hAVR] using hs
    have hqua : qu.path qu.startTime = u := Set.mem_singleton_iff.mp qu.start_mem
    have hqva : qv.path qv.startTime = v := Set.mem_singleton_iff.mp qv.start_mem
    have hpaid := TwoScale.Transfer.two_endpoint_paid_paths E
      p.isCurve.1 (hEreg p.path p.startTime p.endTime p.isCurve)
      (Metric.ball_subset_closedBall p.start_mem)
      (Metric.ball_subset_closedBall p.end_mem)
      hrU0 hrV0 hrU hrV huSub hvSub hdisj
      qu.isCurve.1 qv.isCurve.1
      (hDreg qu.path qu.startTime qu.endTime qu.isCurve)
      (hDreg qv.path qv.startTime qv.endTime qv.isCurve)
      hqua hqva qu.end_mem qv.end_mem hsepU hsepV
    have hqu := TwoScale.Transfer.len_le_mul_of_allPairs_le D E c hcomp
      qu.path qu.startTime qu.endTime
    have hlu := TwoScale.Transfer.len_le_mul_of_allPairs_le D E c hcomp
      lu.path lu.startTime lu.endTime
    have hlv := TwoScale.Transfer.len_le_mul_of_allPairs_le D E c hcomp
      lv.path lv.startTime lv.endTime
    have hqv := TwoScale.Transfer.len_le_mul_of_allPairs_le D E c hcomp
      qv.path qv.startTime qv.endTime
    exact hpaid.trans (add_le_add
      (add_le_add (add_le_add (add_le_add hqu hlu) le_rfl) hlv) hqv)
  have hInf := le_five_infima
    (fun qu : Cu => (c : ℝ≥0∞) * D.len qu.path qu.startTime qu.endTime)
    (fun lu : Lu => (c : ℝ≥0∞) * D.len lu.path lu.startTime lu.endTime)
    (fun p : Cp => E.len p.path p.startTime p.endTime)
    (fun lv : Lv => (c : ℝ≥0∞) * D.len lv.path lv.startTime lv.endTime)
    (fun qv : Cv => (c : ℝ≥0∞) * D.len qv.path qv.startTime qv.endTime)
    (E (u, v)) hcost
  have hcTop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  dsimp only [Cu, Lu, Cp, Lv, Cv] at hInf
  simp only [← ENNReal.mul_iInf_of_ne hc0 hcTop,
    ← setDist_eq_iInf_betweenCurve D hDlen,
    ← setDist_eq_iInf_betweenCurve E hElen,
    ← aroundDist_eq_iInf_aroundCurve] at hInf
  exact hInf

 

theorem endpointLoop_splice_bound
    (D E : LSCMetric) (c : NNReal) (hc : 0 < c)
    (hDlen : D.IsLengthSpace) (hElen : E.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → ContinuousOn P (Set.Icc a b))
    (hEreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      E.IsCurve P a b → ContinuousOn P (Set.Icc a b))
    (hcomp : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (r : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (θ : Set.Ioi (0 : ℝ)) (δ : ℝ)
    (hδ : 0 < δ) (hδB : δ ≤ (1 - (a : ℝ)) ^ 4)
    (u v : ℂ)
    (hu : u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r))
    (hv : v ∈ Metric.sphere (0 : ℂ) r)
    (hlu : EndpointLoop D r a θ u v u)
    (hlv : EndpointLoop D r a θ u v v) :
    E (u, v) ≤
      setDist E (Metric.ball u (δ * r)) (Metric.ball v (δ * r)) +
      ENNReal.ofReal (2 * (c : ℝ) *
        (δ ^ ((θ : ℝ) / 2) + δ ^ (θ : ℝ))) * D (u, v) := by
  have ht0 : 0 < 1 - (a : ℝ) := sub_pos.mpr a.property.2
  have ht1 : 1 - (a : ℝ) < 1 := by linarith only [a.property.1]
  have ht2 : (1 - (a : ℝ)) ^ 2 < 1 := by
    nlinarith only [ht0, ht1]
  have ht4 : (1 - (a : ℝ)) ^ 4 ≤ (1 - (a : ℝ)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right ht2.le (sq_nonneg (1 - (a : ℝ)))
    nlinarith only [hmul]
  have hδ2 : δ ≤ (1 - (a : ℝ)) ^ 2 := by
    exact hδB.trans ht4
  have hsqrtB : Real.sqrt δ ≤ (1 - (a : ℝ)) ^ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨sq_nonneg _, by nlinarith only [hδB]⟩
  have hsqrt0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hδ1 : δ < 1 := lt_of_le_of_lt hδ2 ht2
  have hδsqrt : δ < Real.sqrt δ := by
    nlinarith only [Real.sq_sqrt hδ.le, hsqrt0, hδ1]
  obtain ⟨AU, hAUc, hAUr, hAUR, hAUcost⟩ := hlu δ hδ hδ2
  obtain ⟨AV, hAVc, hAVr, hAVR, hAVcost⟩ := hlv δ hδ hδ2
  obtain ⟨_BU, _hBUc, _hBUr, _hBUR, hBUcost⟩ := hlu (Real.sqrt δ) hsqrt0 hsqrtB
  obtain ⟨_BV, _hBVc, _hBVr, _hBVR, hBVcost⟩ := hlv (Real.sqrt δ) hsqrt0 hsqrtB
  have hrad : δ * (r : ℝ) < Real.sqrt δ * r :=
    mul_lt_mul_of_pos_right hδsqrt r.property
  have hsep : Disjoint
      (Metric.ball u (Real.sqrt δ * r))
      (Metric.ball v (Real.sqrt δ * r)) :=
    TwoScale.Transfer.endpoint_outer_balls_disjoint r a δ hδB hu hv
  have hbase := two_endpoint_infimum_splice D E c hc hDlen hElen
    hDreg hEreg hcomp u v (δ * r) (Real.sqrt δ * r)
    (δ * r) (Real.sqrt δ * r) AU AV
    (mul_nonneg hδ.le r.property.le)
    (mul_nonneg hδ.le r.property.le)
    hrad.le hrad.le
    (Metric.closedBall_subset_ball hrad)
    (Metric.closedBall_subset_ball hrad)
    hsep hAUc hAUr hAUR hAVc hAVr hAVR
  have hpointU :
      setDist D {u} (Metric.sphere u (Real.sqrt δ * r)) ≤
        ENNReal.ofReal ((Real.sqrt δ) ^ (θ : ℝ)) * D (u, v) :=
    (le_max_left _ _).trans hBUcost
  have hpointV :
      setDist D {v} (Metric.sphere v (Real.sqrt δ * r)) ≤
        ENNReal.ofReal ((Real.sqrt δ) ^ (θ : ℝ)) * D (u, v) :=
    (le_max_left _ _).trans hBVcost
  have haroundU :
      aroundDist D AU ≤ ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v) :=
    (le_max_right _ _).trans hAUcost
  have haroundV :
      aroundDist D AV ≤ ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v) :=
    (le_max_right _ _).trans hAVcost
  have hcost : E (u, v) ≤
      (c : ℝ≥0∞) * (ENNReal.ofReal ((Real.sqrt δ) ^ (θ : ℝ)) * D (u, v)) +
      (c : ℝ≥0∞) * (ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v)) +
      setDist E (Metric.ball u (δ * r)) (Metric.ball v (δ * r)) +
      (c : ℝ≥0∞) * (ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v)) +
      (c : ℝ≥0∞) * (ENNReal.ofReal ((Real.sqrt δ) ^ (θ : ℝ)) * D (u, v)) := by
    refine hbase.trans ?_
    gcongr
  have hsqrtPow : (Real.sqrt δ) ^ (θ : ℝ) = δ ^ ((θ : ℝ) / 2) := by
    exact (Real.rpow_div_two_eq_sqrt (θ : ℝ) hδ.le).symm
  rw [hsqrtPow] at hcost
  have hA0 : 0 ≤ δ ^ ((θ : ℝ) / 2) := Real.rpow_nonneg hδ.le _
  have hB0 : 0 ≤ δ ^ (θ : ℝ) := Real.rpow_nonneg hδ.le _
  have hfactor :
      (c : ℝ≥0∞) * (ENNReal.ofReal (δ ^ ((θ : ℝ) / 2)) * D (u, v)) +
      (c : ℝ≥0∞) * (ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v)) +
      setDist E (Metric.ball u (δ * r)) (Metric.ball v (δ * r)) +
      (c : ℝ≥0∞) * (ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v)) +
      (c : ℝ≥0∞) * (ENNReal.ofReal (δ ^ ((θ : ℝ) / 2)) * D (u, v)) =
      setDist E (Metric.ball u (δ * r)) (Metric.ball v (δ * r)) +
      ENNReal.ofReal (2 * (c : ℝ) *
        (δ ^ ((θ : ℝ) / 2) + δ ^ (θ : ℝ))) * D (u, v) := by
    have hcReal : 0 ≤ (c : ℝ) := by exact_mod_cast hc.le
    have hcoef : ENNReal.ofReal (2 * (c : ℝ) *
        (δ ^ ((θ : ℝ) / 2) + δ ^ (θ : ℝ))) =
        (c : ℝ≥0∞) * ENNReal.ofReal (δ ^ ((θ : ℝ) / 2)) +
        (c : ℝ≥0∞) * ENNReal.ofReal (δ ^ (θ : ℝ)) +
        (c : ℝ≥0∞) * ENNReal.ofReal (δ ^ (θ : ℝ)) +
        (c : ℝ≥0∞) * ENNReal.ofReal (δ ^ ((θ : ℝ) / 2)) := by
      have hreal : 2 * (c : ℝ) *
          (δ ^ ((θ : ℝ) / 2) + δ ^ (θ : ℝ)) =
          (c : ℝ) * δ ^ ((θ : ℝ) / 2) +
          (c : ℝ) * δ ^ (θ : ℝ) +
          (c : ℝ) * δ ^ (θ : ℝ) +
          (c : ℝ) * δ ^ ((θ : ℝ) / 2) := by ring
      rw [hreal]
      rw [ENNReal.ofReal_add
        (by positivity : 0 ≤ (c : ℝ) * δ ^ ((θ : ℝ) / 2) +
          (c : ℝ) * δ ^ (θ : ℝ) + (c : ℝ) * δ ^ (θ : ℝ))
        (mul_nonneg hcReal hA0)]
      rw [ENNReal.ofReal_add
        (by positivity : 0 ≤ (c : ℝ) * δ ^ ((θ : ℝ) / 2) +
          (c : ℝ) * δ ^ (θ : ℝ))
        (mul_nonneg hcReal hB0)]
      rw [ENNReal.ofReal_add (mul_nonneg hcReal hA0) (mul_nonneg hcReal hB0)]
      simp only [ENNReal.ofReal_mul hcReal, ENNReal.ofReal_coe_nnreal]
    rw [hcoef]
    ring
  exact hcost.trans_eq hfactor

 
theorem exists_endpoint_error_radius (M θ ζ B : ℝ)
    (hθ : 0 < θ) (hζ : 0 < ζ) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ B ∧
      2 * M * (δ ^ (θ / 2) + δ ^ θ) < ζ := by
  have hθ2 : 0 < θ / 2 := by positivity
  have hlim1 : Tendsto (fun δ : ℝ => δ ^ (θ / 2)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun δ : ℝ => δ ^ (θ / 2)) 0 :=
      continuousAt_id.rpow_const (Or.inr hθ2.le)
    simpa only [Real.zero_rpow hθ2.ne'] using hc.tendsto
  have hlim2 : Tendsto (fun δ : ℝ => δ ^ θ) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun δ : ℝ => δ ^ θ) 0 :=
      continuousAt_id.rpow_const (Or.inr hθ.le)
    simpa only [Real.zero_rpow hθ.ne'] using hc.tendsto
  have hlim : Tendsto (fun δ : ℝ => 2 * M * (δ ^ (θ / 2) + δ ^ θ))
      (𝓝 0) (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      (hlim1.add hlim2).const_mul (2 * M)
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      δ ∈ Ioo 0 B ∧ 2 * M * (δ ^ (θ / 2) + δ ^ θ) < ζ := by
    have hB' : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < B :=
      (show ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < B from Iio_mem_nhds hB).filter_mono nhdsWithin_le_nhds
    filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0),
      hB', (hlim.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hζ)]
      with δ hδ hδB hcost
    exact ⟨⟨hδ, hδB⟩, hcost⟩
  obtain ⟨δ, hδ⟩ := hevent.exists
  exact ⟨δ, hδ.1.1, hδ.1.2.le, hδ.2⟩

 
theorem ratio_gap_of_endpoint_splice (d middle endDist : ℝ≥0∞)
    (C ζ e : ℝ)
    (hd0 : 0 < d) (hdtop : d < ⊤)
    (hζ : 0 < ζ) (hζC : ζ < C) (heζ : e < ζ)
    (hH : ENNReal.ofReal C * d ≤ endDist)
    (hsplice : endDist ≤ middle + ENNReal.ofReal e * d) :
    ENNReal.ofReal (C - ζ) * d ≤ middle := by
  by_contra hn
  have hmiddle : middle < ENNReal.ofReal (C - ζ) * d := lt_of_not_ge hn
  have hζpos : 0 < C - ζ := sub_pos.mpr hζC
  have herror : ENNReal.ofReal e * d < ENNReal.ofReal ζ * d := by
    rw [mul_comm (ENNReal.ofReal e) d, mul_comm (ENNReal.ofReal ζ) d,
      ENNReal.mul_lt_mul_iff_right hd0.ne' hdtop.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff hζ).2 heζ
  have hmiddleFin : middle ≠ ⊤ :=
    (hmiddle.trans (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdtop)).ne
  have hsum : middle + ENNReal.ofReal e * d <
      ENNReal.ofReal (C - ζ) * d + ENNReal.ofReal ζ * d :=
    ENNReal.add_lt_add_of_le_of_lt hmiddleFin hmiddle.le herror
  have hCeq : ENNReal.ofReal (C - ζ) * d + ENNReal.ofReal ζ * d =
      ENNReal.ofReal C * d := by
    rw [← add_mul, ← ENNReal.ofReal_add hζpos.le hζ.le]
    congr 1
    ring_nf
  exact (not_lt_of_ge hH) (hsplice.trans_lt (hsum.trans_eq hCeq))

 

theorem H_to_G_on_regular_at_radius
    (D E : LSCMetric) (c : NNReal) (hc : 0 < c)
    (hDlen : D.IsLengthSpace) (hElen : E.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → ContinuousOn P (Icc a b))
    (hEreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      E.IsCurve P a b → ContinuousOn P (Icc a b))
    (hcomp : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (ξ Q : ℝ) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (θ : Set.Ioi (0 : ℝ)) (ζ : ℝ) (hζ : 0 < ζ)
    (δ : ℝ) (hδpos : 0 < δ) (hδB : δ ≤ (1 - (a : ℝ)) ^ 4)
    (herr : 2 * (c : ℝ) * (δ ^ ((θ : ℝ) / 2) + δ ^ (θ : ℝ)) < ζ) :
    ∀ (r : Set.Ioi (0 : ℝ)) (C : Set.Ioi (0 : ℝ))
      (hCircle : ℝ) (hζC : ζ < (C : ℝ)),
      H D E ξ Q r a C θ hCircle →
      G D E r ⟨δ, hδpos⟩ ⟨(C : ℝ) - ζ, sub_pos.mpr hζC⟩ := by
  intro r C hCircle hζC hH
  obtain ⟨u, v, hu, hv, _hnu, _hnv, hRatio,
    P, s, t, hgeo, _htrace, _hdiam, _hcircle, hloopU, hloopV⟩ := hH
  have huClosed : u ∈ Metric.closedBall (0 : ℂ) r := by
    have hrad : (a : ℝ) * r ≤ r := by
      exact (mul_le_mul_of_nonneg_right a.property.2.le r.property.le).trans_eq (one_mul _)
    rw [Metric.mem_closedBall]
    rw [Metric.mem_sphere] at hu
    exact hu.le.trans hrad
  have hvClosed : v ∈ Metric.closedBall (0 : ℂ) r :=
    Metric.sphere_subset_closedBall hv
  have hp : RatioPair D u v :=
    OptimalConstants.Bridge.ratioPair_of_H_witness D r a hu hv hgeo.2.2.2.2
  have hsp := endpointLoop_splice_bound D E c hc hDlen hElen
    hDreg hEreg hcomp r a θ δ hδpos hδB u v hu hv hloopU hloopV
  have hgap := ratio_gap_of_endpoint_splice (D (u, v))
    (setDist E (Metric.ball u (δ * r)) (Metric.ball v (δ * r)))
    (E (u, v)) C ζ
    (2 * (c : ℝ) * (δ ^ ((θ : ℝ) / 2) + δ ^ (θ : ℝ)))
    hp.2.2.2.1 hp.2.2.2.2 hζ hζC herr hRatio hsp
  exact ⟨u, v, huClosed, hvClosed, hp, hgap⟩

 
theorem H_to_G_on_regular
    (D E : LSCMetric) (c : NNReal) (hc : 0 < c)
    (hDlen : D.IsLengthSpace) (hElen : E.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → ContinuousOn P (Icc a b))
    (hEreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      E.IsCurve P a b → ContinuousOn P (Icc a b))
    (hcomp : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (ξ Q : ℝ) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (θ : Set.Ioi (0 : ℝ)) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ κ : Set.Ioi (0 : ℝ),
      ∀ (r : Set.Ioi (0 : ℝ)) (C : Set.Ioi (0 : ℝ))
        (hCircle : ℝ) (hζC : ζ < (C : ℝ)),
        H D E ξ Q r a C θ hCircle →
        G D E r κ ⟨(C : ℝ) - ζ, sub_pos.mpr hζC⟩ := by
  have hB : 0 < (1 - (a : ℝ)) ^ 4 :=
    pow_pos (sub_pos.mpr a.property.2) _
  obtain ⟨δ, hδpos, hδB, herr⟩ :=
    exists_endpoint_error_radius (c : ℝ) θ ζ ((1 - (a : ℝ)) ^ 4)
      θ.property hζ hB
  exact ⟨⟨δ, hδpos⟩,
    H_to_G_on_regular_at_radius D E c hc hDlen hElen hDreg hEreg
      hcomp ξ Q a θ ζ hζ δ hδpos hδB herr⟩


end SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit
