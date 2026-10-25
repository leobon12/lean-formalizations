import SLUMetricAPI2
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3
import SLUFieldSupport
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import LQGMetric.Metric.InternalOps




 
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.MetricGeometry
namespace SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FirstExit

def boundaryDist (D : LSCMetric) (z : ℂ) (r : ℝ) (u : ℂ) : ℝ≥0∞ :=
  ⨅ y ∈ Metric.sphere z r, D (u, y)

theorem curve_stays_ball_of_len_lt_boundary (D : LSCMetric)
    (hC : ∀ (P : ℝ → ℂ) (s t : ℝ), D.IsCurve P s t → D.len P s t < ∞ →
      ContinuousOn P (Icc s t))
    {z u : ℂ} {r : ℝ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (ha : P a = u) (hu : u ∈ Metric.ball z r)
    (hlen : D.len P a b < boundaryDist D z r u) :
    ∀ t ∈ Icc a b, P t ∈ Metric.ball z r := by
  intro t ht
  by_contra hout
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hPt : D.IsCurve P a t := ⟨ht.1, hP.2.mono hsub⟩
  have hlt : D.len P a t ≤ D.len P a b :=
    LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) le_rfl ht.2
  have hfin : D.len P a t < ∞ := (hlt.trans_lt hlen).trans_le le_top
  obtain ⟨γ, -, hγrange⟩ := exists_path_of_curve ht.1 (hC P a t hPt hfin)
  obtain ⟨s, hs⟩ := exists_mem_frontier_of_path Metric.isOpen_ball γ (by simpa [ha] using hu) hout
  have hsSphere : (γ s : ℂ) ∈ Metric.sphere z r :=
    Metric.frontier_ball_subset_sphere hs
  obtain ⟨q, hq, hqeq⟩ := hγrange ⟨s, rfl⟩
  have hDq : D (u, (γ s : ℂ)) ≤ D.len P a b := by
    rw [← ha, ← hqeq]
    exact (D.apply_le_len P hq.1).trans
      (LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) le_rfl (hq.2.trans ht.2))
  have hBd : boundaryDist D z r u ≤ D (u, (γ s : ℂ)) :=
    iInf₂_le _ hsSphere
  exact (not_le_of_gt hlen) (hBd.trans hDq)

 

theorem ambient_eq_internal_of_escape (D : LSCMetric)
    (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (s t : ℝ), D.IsCurve P s t → D.len P s t < ∞ →
      ContinuousOn P (Icc s t))
    {z u v : ℂ} {r : ℝ} (hu : u ∈ Metric.ball z r) (hv : v ∈ Metric.ball z r)
    (hxy : D (u, v) < boundaryDist D z r u) :
    D (u, v) = D.internal (Metric.ball z r) (⟨u, hu⟩, ⟨v, hv⟩) := by
  refine le_antisymm ?_ ?_
  · rw [D.internal_eq_internalEDist]
    exact edist_le_internalEDist (D.pt '' Metric.ball z r) (D.pt u) (D.pt v)
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨δ, hδ, hδr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hxy
    obtain ⟨P, a, b, hP, ha, hb, hlen⟩ :=
      hL u v (hxy.trans_le le_top) (min ε δ : ℝ)
        (by exact_mod_cast lt_min hε hδ)
    simp only [← NNReal.coe_min, ENNReal.ofReal_coe_nnreal] at hlen
    have hlenB : D.len P a b < boundaryDist D z r u :=
      hlen.trans_lt (lt_of_le_of_lt
        (add_le_add le_rfl (by exact_mod_cast min_le_right ε δ)) hδr)
    have hY := curve_stays_ball_of_len_lt_boundary D hC hP ha hu hlenB
    have hInt : D.internal (Metric.ball z r) (⟨u, hu⟩, ⟨v, hv⟩) ≤
        D.len P a b := by
      rw [D.internal_eq_internalEDist]
      have h := internalEDist_le_curveLength hP.1 hP.2
        (fun t ht => Set.mem_image_of_mem D.pt (hY t ht))
      simpa only [Function.comp_apply, ha, hb, D.len_eq_curveLength] using h
    exact hInt.trans (hlen.trans (add_le_add le_rfl
      (by exact_mod_cast min_le_left ε δ)))

 
theorem first_exit_closedBall (D : LSCMetric)
    {z : ℂ} {r : ℝ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hE : ContinuousOn P (Icc a b))
    (ha : P a ∈ Metric.ball z r) (hb : P b ∉ Metric.ball z r) :
    ∃ t ∈ Icc a b, P t ∈ Metric.sphere z r ∧
      ∀ s ∈ Icc a t, P s ∈ Metric.closedBall z r := by
  obtain ⟨t, ht, htout, hbefore⟩ := exists_first_hit hE
    (Metric.isOpen_ball.isClosed_compl)
    ⟨b, right_mem_Icc.2 hP.1, hb⟩
  have hat : a < t := by
    rcases ht.1.eq_or_lt with h | h
    · exfalso
      exact htout (h ▸ ha)
    · exact h
  have htin : P t ∈ closure (Metric.ball z r) := by
    have hcont : ContinuousWithinAt P (Ico a t) t :=
      (hE t ht).mono (fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩)
    have hmem : ∀ᶠ s in 𝓝[Ico a t] t, P s ∈ Metric.ball z r :=
      eventually_nhdsWithin_of_forall fun s hs => not_not.1 (hbefore s hs)
    have hne : (𝓝[Ico a t] t).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hat.ne]
      exact ⟨hat.le, le_rfl⟩
    exact mem_closure_of_tendsto hcont hmem
  have htfr : P t ∈ frontier (Metric.ball z r) := by
    exact ⟨htin, by change P t ∉ Metric.ball z r at htout; simpa only [Metric.isOpen_ball.interior_eq] using htout⟩
  refine ⟨t, ht, Metric.frontier_ball_subset_sphere htfr, ?_⟩
  intro s hs
  rcases hs.2.lt_or_eq with hst | hst
  · exact Metric.ball_subset_closedBall (not_not.1 (hbefore s ⟨hs.1, hst⟩))
  · exact Metric.sphere_subset_closedBall (Metric.frontier_ball_subset_sphere (hst ▸ htfr))

def boundaryInternal (D : LSCMetric) (z : ℂ) (r : ℝ) (u : ℂ)
    (hu : u ∈ Metric.closedBall z r) : ℝ≥0∞ :=
  ⨅ y ∈ Metric.sphere z r,
    D.internal (Metric.closedBall z r)
      (⟨u, hu⟩, ⟨y, Metric.sphere_subset_closedBall ‹y ∈ Metric.sphere z r›⟩)

 

theorem boundaryDist_eq_internalClosedBall (D : LSCMetric)
    (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (s t : ℝ), D.IsCurve P s t → D.len P s t < ∞ →
      ContinuousOn P (Icc s t))
    {z u : ℂ} {r : ℝ} (hu : u ∈ Metric.ball z r) :
    boundaryDist D z r u =
      boundaryInternal D z r u (Metric.ball_subset_closedBall hu) := by
  let huK : u ∈ Metric.closedBall z r := Metric.ball_subset_closedBall hu
  change boundaryDist D z r u = boundaryInternal D z r u huK
  refine le_antisymm ?_ ?_
  · unfold boundaryInternal
    refine le_iInf fun y => le_iInf fun hy => ?_
    exact (iInf₂_le y hy).trans (by
      rw [D.internal_eq_internalEDist]
      exact edist_le_internalEDist (D.pt '' Metric.closedBall z r) (D.pt u) (D.pt y))
  · unfold boundaryDist
    refine le_iInf fun y => le_iInf fun hy => ?_
    by_cases hfin : D (u, y) = ∞
    · rw [hfin]; exact le_top
    have hlt : D (u, y) < ∞ := lt_top_iff_ne_top.mpr hfin
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨P, a, b, hP, ha, hb, hlen⟩ :=
      hL u y hlt (ε : ℝ) (by exact_mod_cast hε)
    rw [ENNReal.ofReal_coe_nnreal] at hlen
    have hPfin : D.len P a b < ∞ :=
      hlen.trans_lt (ENNReal.add_lt_top.2 ⟨hlt, ENNReal.coe_lt_top⟩)
    have hbout : P b ∉ Metric.ball z r := by
      rw [hb]
      exact fun h => (Metric.mem_sphere.1 hy).not_lt (Metric.mem_ball.1 h)
    obtain ⟨t, ht, htsphere, hK⟩ :=
      first_exit_closedBall D hP (hC P a b hP hPfin) (ha.symm ▸ hu) hbout
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hPt : D.IsCurve P a t := ⟨ht.1, hP.2.mono hsub⟩
    have hInt : D.internal (Metric.closedBall z r)
        (⟨u, huK⟩, ⟨P t, Metric.sphere_subset_closedBall htsphere⟩) ≤
        D.len P a t := by
      rw [D.internal_eq_internalEDist]
      have h := internalEDist_le_curveLength hPt.1 hPt.2
        (fun s hs => Set.mem_image_of_mem D.pt (hK s hs))
      simpa only [Function.comp_apply, ha, D.len_eq_curveLength] using h
    have hbd : boundaryInternal D z r u huK ≤
        D.internal (Metric.closedBall z r)
          (⟨u, huK⟩, ⟨P t, Metric.sphere_subset_closedBall htsphere⟩) := by
      exact iInf₂_le (P t) htsphere
    exact (hbd.trans (hInt.trans
      (LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) le_rfl ht.2))).trans hlen

 

theorem ambient_eq_internal_of_below_boundary (D : LSCMetric)
    (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (s t : ℝ), D.IsCurve P s t → D.len P s t < ∞ →
      ContinuousOn P (Icc s t))
    {z u v : ℂ} {r : ℝ} (hu : u ∈ Metric.ball z r) (hv : v ∈ Metric.ball z r)
    (hlt : D.internal (Metric.ball z r) (⟨u, hu⟩, ⟨v, hv⟩) <
      boundaryInternal D z r u (Metric.ball_subset_closedBall hu)) :
    D (u, v) = D.internal (Metric.ball z r) (⟨u, hu⟩, ⟨v, hv⟩) := by
  have hbound : D (u, v) ≤
      D.internal (Metric.ball z r) (⟨u, hu⟩, ⟨v, hv⟩) := by
    rw [D.internal_eq_internalEDist]
    exact edist_le_internalEDist (D.pt '' Metric.ball z r) (D.pt u) (D.pt v)
  have hxy : D (u, v) < boundaryDist D z r u := by
    rw [boundaryDist_eq_internalClosedBall D hL hC hu]
    exact hbound.trans_lt hlt
  exact ambient_eq_internal_of_escape D hL hC hu hv hxy

def LocalWitness (D E : LSCMetric) (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r) : Prop :=
  ∃ u v : ℂ, ∃ hu : u ∈ Metric.ball z (r / 2),
    ∃ hv : v ∈ Metric.ball z (r / 2),
      u ≠ v ∧
      0 < D.internal (Metric.ball z r)
        (⟨u, Metric.ball_subset_ball (by linarith [hr]) hu⟩,
         ⟨v, Metric.ball_subset_ball (by linarith [hr]) hv⟩) ∧
      D.internal (Metric.ball z r)
        (⟨u, Metric.ball_subset_ball (by linarith [hr]) hu⟩,
         ⟨v, Metric.ball_subset_ball (by linarith [hr]) hv⟩) <
        boundaryInternal D z r u
          (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith [hr]) hu)) ∧
      0 < E.internal (Metric.ball z r)
        (⟨u, Metric.ball_subset_ball (by linarith [hr]) hu⟩,
         ⟨v, Metric.ball_subset_ball (by linarith [hr]) hv⟩) ∧
      E.internal (Metric.ball z r)
        (⟨u, Metric.ball_subset_ball (by linarith [hr]) hu⟩,
         ⟨v, Metric.ball_subset_ball (by linarith [hr]) hv⟩) <
        boundaryInternal E z r u
          (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith [hr]) hu)) ∧
      a * D.internal (Metric.ball z r)
        (⟨u, Metric.ball_subset_ball (by linarith [hr]) hu⟩,
         ⟨v, Metric.ball_subset_ball (by linarith [hr]) hv⟩) <
        E.internal (Metric.ball z r)
        (⟨u, Metric.ball_subset_ball (by linarith [hr]) hu⟩,
         ⟨v, Metric.ball_subset_ball (by linarith [hr]) hv⟩)

 

theorem localWitness_lt_upperOptimal (D E : LSCMetric)
    (hLD : D.IsLengthSpace) (hLE : E.IsLengthSpace)
    (hCD : ∀ (P : ℝ → ℂ) (s t : ℝ), D.IsCurve P s t → D.len P s t < ∞ →
      ContinuousOn P (Icc s t))
    (hCE : ∀ (P : ℝ → ℂ) (s t : ℝ), E.IsCurve P s t → E.len P s t < ∞ →
      ContinuousOn P (Icc s t))
    {a : ℝ≥0∞} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (h : LocalWitness D E a z r hr) :
    a < OptimalConstants.Ratios.upperOptimal D E := by
  rcases h with ⟨u, v, hu, hv, huv, hDpos, hDbound, hEpos, hEbound, hRatio⟩
  have huW : u ∈ Metric.ball z r := Metric.ball_subset_ball (by linarith [hr]) hu
  have hvW : v ∈ Metric.ball z r := Metric.ball_subset_ball (by linarith [hr]) hv
  have hD := ambient_eq_internal_of_below_boundary D hLD hCD huW hvW hDbound
  have hE := ambient_eq_internal_of_below_boundary E hLE hCE huW hvW hEbound
  have hDpos' : 0 < D (u, v) := by simpa only [hD] using hDpos
  have hDfin : D (u, v) < ∞ := by
    rw [hD]
    exact hDbound.trans_le le_top
  have hRatio' : a * D (u, v) < E (u, v) := by
    simpa only [hD, hE] using hRatio
  have hpair : OptimalConstants.Ratios.RatioPair D u v := by
    refine ⟨huv, ?_, ?_, hDpos', hDfin⟩
    · intro hs
      exact (ne_top_of_lt hDfin) (hs v huv.symm)
    · intro hs
      exact (ne_top_of_lt hDfin)
        ((D.isExtMetric.2.2.1 u v).trans (hs u huv))
  have hrat : a < E (u, v) / D (u, v) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hDpos'.ne') (Or.inl hDfin.ne)).2 hRatio'
  exact hrat.trans_le (OptimalConstants.Ratios.ratio_le_upperOptimal D E hpair)

 

theorem internal_of_scale {D E : LSCMetric} {scale : ℝ≥0∞}
    (hscale0 : scale ≠ 0) (hscalet : scale ≠ ∞)
    (h : ∀ x y : ℂ, E (x, y) = scale * D (x, y))
    (Y : Set ℂ) (x y : Y) :
    E.internal Y (x, y) = scale * D.internal Y (x, y) := by
  let e : D.Space ≃ E.Space := Equiv.refl ℂ
  have he : ∀ a b : D.Space,
      edist (e a) (e b) = scale * edist a b := by
    intro a b
    change E (a, b) = scale * D (a, b)
    exact h a b
  have hi := internalEDist_image_of_edist_eq
    (X := D.Space) (Z := E.Space) e hscale0 hscalet he
    (D.pt '' Y) (D.pt x) (D.pt y)
  rw [D.internal_eq_internalEDist, E.internal_eq_internalEDist]
  have hset : e '' (D.pt '' Y) = E.pt '' Y := by
    ext w
    constructor
    · rintro ⟨v, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨D.pt q, ⟨q, hq, rfl⟩, rfl⟩
  have hx : e (D.pt x) = E.pt x := rfl
  have hy : e (D.pt y) = E.pt y := rfl
  rw [hset, hx, hy] at hi
  exact hi

theorem boundaryInternal_of_scale {D E : LSCMetric} {scale : ℝ≥0∞}
    (hscale0 : scale ≠ 0) (hscalet : scale ≠ ∞)
    (h : ∀ x y : ℂ, E (x, y) = scale * D (x, y))
    (z : ℂ) (r : ℝ) (u : ℂ) (hu : u ∈ Metric.closedBall z r) :
    boundaryInternal E z r u hu = scale * boundaryInternal D z r u hu := by
  unfold boundaryInternal
  simp_rw [internal_of_scale hscale0 hscalet h]
  rw [ENNReal.mul_iInf_of_ne hscale0 hscalet]
  simp_rw [ENNReal.mul_iInf_of_ne hscale0 hscalet]

 

theorem localWitness_iff_of_scale {D₁ D₂ E₁ E₂ : LSCMetric}
    {scale : ℝ≥0∞} (hscale0 : scale ≠ 0) (hscalet : scale ≠ ∞)
    (hD : ∀ x y : ℂ, D₂ (x, y) = scale * D₁ (x, y))
    (hE : ∀ x y : ℂ, E₂ (x, y) = scale * E₁ (x, y))
    (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r) :
    LocalWitness D₂ E₂ a z r hr ↔ LocalWitness D₁ E₁ a z r hr := by
  have hscalePos : 0 < scale := pos_iff_ne_zero.mpr hscale0
  have hlast (x y : ℝ≥0∞) :
      a * (scale * x) < scale * y ↔ a * x < y := by
    rw [mul_left_comm a scale x,
      ENNReal.mul_lt_mul_iff_right hscale0 hscalet]
  unfold LocalWitness
  simp only [internal_of_scale hscale0 hscalet hD,
    internal_of_scale hscale0 hscalet hE,
    boundaryInternal_of_scale hscale0 hscalet hD,
    boundaryInternal_of_scale hscale0 hscalet hE,
    ENNReal.mul_pos_iff, hscalePos, true_and,
    ENNReal.mul_lt_mul_iff_right hscale0 hscalet, hlast]

 

theorem internal_translate_scale {D E : LSCMetric} {scale : ℝ≥0∞}
    (hscale0 : scale ≠ 0) (hscalet : scale ≠ ∞)
    (z : ℂ)
    (h : ∀ x y : ℂ, E (x - z, y - z) = scale * D (x, y))
    (W : Set ℂ) (x y : W) :
    E.internal ((fun w : ℂ => w - z) '' W)
      (⟨x.1 - z, ⟨x.1, x.2, rfl⟩⟩,
       ⟨y.1 - z, ⟨y.1, y.2, rfl⟩⟩) =
    scale * D.internal W (x, y) := by
  let e : D.Space ≃ E.Space :=
    { toFun := fun w => (show ℂ from w) - z
      invFun := fun w => (show ℂ from w) + z
      left_inv := by intro w; change ((show ℂ from w) - z) + z = w; exact sub_add_cancel _ _
      right_inv := by intro w; change ((show ℂ from w) + z) - z = w; exact add_sub_cancel_right _ _ }
  have he : ∀ a b : D.Space, edist (e a) (e b) = scale * edist a b := by
    intro a b
    change E ((show ℂ from a) - z, (show ℂ from b) - z) = scale * D (a, b)
    exact h a b
  have hi := internalEDist_image_of_edist_eq
    (X := D.Space) (Z := E.Space) e hscale0 hscalet he
    (D.pt '' W) (D.pt x) (D.pt y)
  rw [D.internal_eq_internalEDist, E.internal_eq_internalEDist]
  have hset : e '' (D.pt '' W) =
      E.pt '' ((fun w : ℂ => w - z) '' W) := by
    ext w
    constructor
    · rintro ⟨v, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q - z, ⟨q, hq, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨D.pt q, ⟨q, hq, rfl⟩, rfl⟩
  have hx : e (D.pt x) = E.pt (x.1 - z) := rfl
  have hy : e (D.pt y) = E.pt (y.1 - z) := rfl
  rw [hset, hx, hy] at hi
  exact hi

 

theorem ae_localWitness_addConst_iff
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D E : LQGMetric.DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    (c : Ω → ℝ) (a : ℝ≥0∞) (z : ℂ) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂P,
      LocalWitness (D (LQGMetric.addConst (h ω) (c ω)))
        (E (LQGMetric.addConst (h ω) (c ω))) a z r hr ↔
      LocalWitness (D (h ω)) (E (h ω)) a z r hr := by
  filter_upwards [hD.length P h hh, hE.length P h hh,
    hD.weyl P h hh, hE.weyl P h hh] with ω hLD hLE hwD hwE
  let scale : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω))
  have hs0 : scale ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hst : scale ≠ ∞ := ENNReal.ofReal_ne_top
  have hd (x y : ℂ) :
      D (LQGMetric.addConst (h ω) (c ω)) (x, y) =
        scale * D (h ω) (x, y) := by
    have hw := hwD (ContinuousMap.const ℂ (c ω))
    have hc := weylScale_const (ξ : ℝ) (c ω) (D (h ω)) hLD (x, y)
    simpa only [LQGMetric.addConst, scale] using (hw ▸ hc)
  have he (x y : ℂ) :
      E (LQGMetric.addConst (h ω) (c ω)) (x, y) =
        scale * E (h ω) (x, y) := by
    have hw := hwE (ContinuousMap.const ℂ (c ω))
    have hc := weylScale_const (ξ : ℝ) (c ω) (E (h ω)) hLE (x, y)
    simpa only [LQGMetric.addConst, scale] using (hw ▸ hc)
  exact localWitness_iff_of_scale hs0 hst hd he a z r hr

 

theorem boundaryDist_eq_internalClosedBall_of_barrier (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {z u : ℂ} {r : ℝ} (hu : u ∈ Metric.ball z r) :
    boundaryDist D z r u =
      boundaryInternal D z r u (Metric.ball_subset_closedBall hu) :=
  boundaryDist_eq_internalClosedBall D hL
    (fun _P _s _t hP _ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length D hB hL hP) hu

theorem ambient_eq_internal_of_below_boundary_of_barrier (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {z u v : ℂ} {r : ℝ} (hu : u ∈ Metric.ball z r) (hv : v ∈ Metric.ball z r)
    (hlt : D.internal (Metric.ball z r) (⟨u, hu⟩, ⟨v, hv⟩) <
      boundaryInternal D z r u (Metric.ball_subset_closedBall hu)) :
    D (u, v) = D.internal (Metric.ball z r) (⟨u, hu⟩, ⟨v, hv⟩) :=
  ambient_eq_internal_of_below_boundary D hL
    (fun _P _s _t hP _ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length D hB hL hP) hu hv hlt

theorem ambient_eq_internal_of_escape_of_barrier (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {z u v : ℂ} {r : ℝ} (hu : u ∈ Metric.ball z r) (hv : v ∈ Metric.ball z r)
    (hxy : D (u, v) < boundaryDist D z r u) :
    D (u, v) = D.internal (Metric.ball z r) (⟨u, hu⟩, ⟨v, hv⟩) :=
  ambient_eq_internal_of_escape D hL
    (fun _P _s _t hP _ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length D hB hL hP) hu hv hxy


end SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FirstExit
