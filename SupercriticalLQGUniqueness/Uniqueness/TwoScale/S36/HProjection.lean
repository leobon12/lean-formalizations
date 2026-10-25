import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.LoopBorel
import BR1Bridges
import LQGMetric.Meas.UM
import LQGMetric.Field.StandardBorelRange
import LQGMetric.Field.CameronMartin




 













set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

def HBody (m n : LSCMetric) (cmp : ℝ≥0∞ → ℝ≥0∞ → Prop) (ξ Q : ℝ) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) (hCircle : ℝ) : Prop :=
  ∃ u v : ℂ, u ∈ Metric.sphere (0 : ℂ) (a * r) ∧
    v ∈ Metric.sphere (0 : ℂ) r ∧
    ¬ OptimalConstants.Ratios.Singular m u ∧ ¬ OptimalConstants.Ratios.Singular m v ∧
    cmp (m (u, v)) (n (u, v)) ∧
    ∃ (P : ℝ → ℂ) (s t : ℝ),
      OptimalConstants.Ratios.Geodesic m P s t u v ∧
      (∀ q ∈ Icc s t, q ∈ P ⁻¹' (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (a * r))) ∧
      Metric.diam (P '' Icc s t) ≤ r / 100 ∧
      m (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * hCircle)) ∧
      OptimalConstants.Ratios.EndpointLoop m r a θ u v u ∧ OptimalConstants.Ratios.EndpointLoop m r a θ u v v

theorem H_iff_HBody (D D' : LSCMetric) (ξ Q : ℝ) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) (hCircle : ℝ) :
    OptimalConstants.Ratios.H D D' ξ Q r a C θ hCircle ↔
      HBody D D' (fun x y => ENNReal.ofReal C * x ≤ y) ξ Q r a θ hCircle :=
  Iff.rfl

theorem Htilde_iff_HBody (D D' : LSCMetric) (ξ Q : ℝ) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) (hCircle : ℝ) :
    OptimalConstants.Ratios.Htilde D D' ξ Q r a C θ hCircle ↔
      HBody D' D (fun x y => x ≤ ENNReal.ofReal C * y) ξ Q r a θ hCircle :=
  Iff.rfl

 
def hCarrier (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) : Set ℂ :=
  Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (a * r)

theorem isCompact_hCarrier (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) :
    IsCompact (hCarrier r a) :=
  (isCompact_closedBall _ _).diff Metric.isOpen_ball

 
def HCodeBody (m n : LSCMetric) (cmp : ℝ≥0∞ → ℝ≥0∞ → Prop) (ξ Q : ℝ) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) (hCircle : ℝ) (u v : ℂ) (γ : PathCode) :
    Prop :=
  u ∈ Metric.sphere (0 : ℂ) (a * r) ∧
  v ∈ Metric.sphere (0 : ℂ) r ∧
  cmp (m (u, v)) (n (u, v)) ∧
  IsGeoCode m γ ∧ γ 0 = u ∧ γ 1 = v ∧
  (∀ τ, γ τ ∈ hCarrier r a) ∧
  (∀ τ₁ τ₂, dist (γ τ₁) (γ τ₂) ≤ (r : ℝ) / 100) ∧
  m (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * hCircle)) ∧
  (m, (u, m (u, v))) ∈ LoopSet r a θ ∧
  (m, (v, m (u, v))) ∈ LoopSet r a θ

 
theorem ne_of_mem_spheres {r : Ioi (0 : ℝ)} {a : Ioo (3 / 4 : ℝ) 1} {u v : ℂ}
    (hu : u ∈ Metric.sphere (0 : ℂ) (a * r)) (hv : v ∈ Metric.sphere (0 : ℂ) r) : u ≠ v := by
  intro h
  have h1 : dist u 0 = (a : ℝ) * r := Metric.mem_sphere.mp hu
  have h2 : dist v 0 = (r : ℝ) := Metric.mem_sphere.mp hv
  rw [h, h2] at h1
  have ha : (a : ℝ) < 1 := a.2.2
  have hr : (0 : ℝ) < r := r.2
  nlinarith

 
theorem HBody_iff_exists_code (m n : LSCMetric) (cmp : ℝ≥0∞ → ℝ≥0∞ → Prop) (ξ Q : ℝ)
    (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) (hCircle : ℝ) :
    HBody m n cmp ξ Q r a θ hCircle ↔
      ∃ u v : ℂ, ∃ γ : PathCode, HCodeBody m n cmp ξ Q r a θ hCircle u v γ := by
  have hK := isCompact_hCarrier r a
  constructor
  · rintro ⟨u, v, hu, hv, -, -, hcmp, P, s, t, hgeo, htr, hdiam, hN, hLu, hLv⟩
    obtain ⟨γ, hγ, hγ0, hγ1, hγK, hγd⟩ :=
      (exists_geodesic_iff_code m u v hK ((r : ℝ) / 100)).mp ⟨P, s, t, hgeo, htr, hdiam⟩
    have hfin : m (u, v) ≠ ⊤ := hgeo.2.2.2.2.ne
    exact ⟨u, v, γ, hu, hv, hcmp, hγ, hγ0, hγ1, hγK, hγd, hN,
      (endpointLoop_iff_mem_loopSet m r a θ u v u hfin).mp hLu,
      (endpointLoop_iff_mem_loopSet m r a θ u v v hfin).mp hLv⟩
  · rintro ⟨u, v, γ, hu, hv, hcmp, hγ, hγ0, hγ1, hγK, hγd, hN, hLu, hLv⟩
    obtain ⟨P, s, t, hgeo, htr, hdiam⟩ :=
      (exists_geodesic_iff_code m u v hK ((r : ℝ) / 100)).mpr ⟨γ, hγ, hγ0, hγ1, hγK, hγd⟩
    have hfin : m (u, v) < ⊤ := hgeo.2.2.2.2
    have huv : u ≠ v := ne_of_mem_spheres hu hv
    refine ⟨u, v, hu, hv, ?_, ?_, hcmp, P, s, t, hgeo, htr, hdiam, hN,
      (endpointLoop_iff_mem_loopSet m r a θ u v u hfin.ne).mpr hLu,
      (endpointLoop_iff_mem_loopSet m r a θ u v v hfin.ne).mpr hLv⟩
    · intro hs
      exact hfin.ne (hs v huv.symm)
    · intro hs
      exact hfin.ne ((m.isExtMetric.2.2.1 u v).trans (hs u huv))

 
abbrev HWit : Type := ℝ × ℂ × ℂ × PathCode

 
def HCodeRel (M N : DistC → LSCMetric) (cmp : ℝ≥0∞ → ℝ≥0∞ → Prop) (ξ Q : ℝ)
    (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) : Set (DistC × HWit) :=
  {x | IsCircleAverage x.1 r 0 x.2.1} ∩
    {x | HCodeBody (M x.1) (N x.1) cmp ξ Q r a θ x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2}

 

 
theorem measurableSet_isCircleAverage_rel {β : Type*} [MeasurableSpace β]
    (r : Ioi (0 : ℝ)) (z : ℂ) {c : β → ℝ} (hc : Measurable c) :
    MeasurableSet {x : DistC × β | IsCircleAverage x.1 r z (c x.2)} := by
  have hf : ∀ n : ℕ, Measurable fun x : DistC × β =>
      x.1 (LQGMetric.CircleAvg.circBump n z (r : ℝ)) := fun n =>
    (LQGMetric.measurable_evalDist _).comp measurable_fst
  have h := measurableSet_tendsto_fun (l := atTop) hf (hc.comp measurable_snd)
  have heq : {x : DistC × β | IsCircleAverage x.1 r z (c x.2)} =
      {x : DistC × β | Tendsto (fun n : ℕ => x.1 (LQGMetric.CircleAvg.circBump n z (r : ℝ)))
        atTop (𝓝 (c x.2))} := by
    ext x
    exact isCircleAverage_iff_circBump x.1 r z (c x.2)
  rw [heq]
  exact h

 
theorem measurable_metric_eval {β : Type*} [MeasurableSpace β] {M : β → LSCMetric}
    {u v : β → ℂ} (hM : Measurable M) (hu : Measurable u) (hv : Measurable v) :
    Measurable fun x => M x (u x, v x) := by
  have h1 : Measurable fun x => ((M x, (u x, v x)) : LSCMetric × (ℂ × ℂ)) :=
    hM.prodMk (hu.prodMk hv)
  have h2 := TwoScale.S36Events.jointEval_lsc.measurable.comp h1
  simpa only [Function.comp_def] using h2

section Coordinates

variable {M N : DistC → LSCMetric}

theorem measurable_wc : Measurable fun x : DistC × HWit => x.2.1 :=
  measurable_fst.comp measurable_snd

theorem measurable_wu : Measurable fun x : DistC × HWit => x.2.2.1 :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem measurable_wv : Measurable fun x : DistC × HWit => x.2.2.2.1 :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem measurable_wγ : Measurable fun x : DistC × HWit => x.2.2.2.2 :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem measurable_wM (hM : Measurable M) : Measurable fun x : DistC × HWit => M x.1 :=
  hM.comp measurable_fst

theorem measurable_wMuv (hM : Measurable M) :
    Measurable fun x : DistC × HWit => M x.1 (x.2.2.1, x.2.2.2.1) :=
  measurable_metric_eval (measurable_wM hM) measurable_wu measurable_wv

end Coordinates

 
theorem measurableSet_code_closed {S : Set PathCode} (hS : IsClosed S) :
    MeasurableSet {x : DistC × HWit | x.2.2.2.2 ∈ S} :=
  measurable_wγ hS.measurableSet

theorem isClosed_trace (K : Set ℂ) (hK : IsClosed K) :
    IsClosed {γ : PathCode | ∀ τ, γ τ ∈ K} := by
  have h : {γ : PathCode | ∀ τ, γ τ ∈ K} = ⋂ τ : unitInterval, {γ : PathCode | γ τ ∈ K} := by
    ext γ
    simp only [mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun τ => hK.preimage (continuous_eval_const τ)

theorem isClosed_pairDist (c : ℝ) :
    IsClosed {γ : PathCode | ∀ τ₁ τ₂, dist (γ τ₁) (γ τ₂) ≤ c} := by
  have h : {γ : PathCode | ∀ τ₁ τ₂, dist (γ τ₁) (γ τ₂) ≤ c} =
      ⋂ τ₁ : unitInterval, ⋂ τ₂ : unitInterval, {γ : PathCode | dist (γ τ₁) (γ τ₂) ≤ c} := by
    ext γ
    simp only [mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun τ₁ => isClosed_iInter fun τ₂ =>
    isClosed_le ((continuous_eval_const τ₁).dist (continuous_eval_const τ₂)) continuous_const

 
theorem measurableSet_HCodeBody {M N : DistC → LSCMetric} (hM : Measurable M)
    (hN : Measurable N) {cmp : ℝ≥0∞ → ℝ≥0∞ → Prop}
    (hcmp : MeasurableSet {p : ℝ≥0∞ × ℝ≥0∞ | cmp p.1 p.2}) (ξ Q : ℝ)
    (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) :
    MeasurableSet {x : DistC × HWit |
      HCodeBody (M x.1) (N x.1) cmp ξ Q r a θ x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2} := by
  have hMuv := measurable_wMuv hM
  have hNuv := measurable_wMuv hN
  have h1 : MeasurableSet {x : DistC × HWit | x.2.2.1 ∈ Metric.sphere (0 : ℂ) (a * r)} :=
    measurable_wu Metric.isClosed_sphere.measurableSet
  have h2 : MeasurableSet {x : DistC × HWit | x.2.2.2.1 ∈ Metric.sphere (0 : ℂ) r} :=
    measurable_wv Metric.isClosed_sphere.measurableSet
  have h3 : MeasurableSet {x : DistC × HWit |
      cmp (M x.1 (x.2.2.1, x.2.2.2.1)) (N x.1 (x.2.2.1, x.2.2.2.1))} :=
    (hMuv.prodMk hNuv) hcmp
  have h4 : MeasurableSet {x : DistC × HWit | IsGeoCode (M x.1) x.2.2.2.2} :=
    ((measurable_wM hM).prodMk measurable_wγ) measurableSet_isGeoCode
  have h5 : MeasurableSet {x : DistC × HWit | x.2.2.2.2 0 = x.2.2.1} :=
    measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_wγ) measurable_wu
  have h6 : MeasurableSet {x : DistC × HWit | x.2.2.2.2 1 = x.2.2.2.1} :=
    measurableSet_eq_fun ((continuous_eval_const 1).measurable.comp measurable_wγ) measurable_wv
  have h7 : MeasurableSet {x : DistC × HWit | ∀ τ, x.2.2.2.2 τ ∈ hCarrier r a} :=
    measurableSet_code_closed (isClosed_trace _ (isCompact_hCarrier r a).isClosed)
  have h8 : MeasurableSet {x : DistC × HWit |
      ∀ τ₁ τ₂, dist (x.2.2.2.2 τ₁) (x.2.2.2.2 τ₂) ≤ (r : ℝ) / 100} :=
    measurableSet_code_closed (isClosed_pairDist _)
  have hbound : Measurable fun x : DistC × HWit =>
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * x.2.1)) :=
    (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul measurable_wc))).ennreal_ofReal
  have h9 : MeasurableSet {x : DistC × HWit | M x.1 (x.2.2.1, x.2.2.2.1) ≤
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * x.2.1))} :=
    measurableSet_le hMuv hbound
  have h10 : MeasurableSet {x : DistC × HWit |
      (M x.1, (x.2.2.1, M x.1 (x.2.2.1, x.2.2.2.1))) ∈ LoopSet r a θ} :=
    ((measurable_wM hM).prodMk (measurable_wu.prodMk hMuv)) (measurableSet_loopSet r a θ)
  have h11 : MeasurableSet {x : DistC × HWit |
      (M x.1, (x.2.2.2.1, M x.1 (x.2.2.1, x.2.2.2.1))) ∈ LoopSet r a θ} :=
    ((measurable_wM hM).prodMk (measurable_wv.prodMk hMuv)) (measurableSet_loopSet r a θ)
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter (h7.inter (h8.inter
    (h9.inter (h10.inter h11)))))))))

theorem measurableSet_HCodeRel {M N : DistC → LSCMetric} (hM : Measurable M)
    (hN : Measurable N) {cmp : ℝ≥0∞ → ℝ≥0∞ → Prop}
    (hcmp : MeasurableSet {p : ℝ≥0∞ × ℝ≥0∞ | cmp p.1 p.2}) (ξ Q : ℝ)
    (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) :
    MeasurableSet (HCodeRel M N cmp ξ Q r a θ) :=
  (measurableSet_isCircleAverage_rel r 0 measurable_fst).inter
    (measurableSet_HCodeBody hM hN hcmp ξ Q r a θ)

 
theorem setOf_HBody_eq (M N : DistC → LSCMetric) (cmp : ℝ≥0∞ → ℝ≥0∞ → Prop) (ξ Q : ℝ)
    (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) :
    {g : DistC | ∃ hCircle : ℝ, IsCircleAverage g r 0 hCircle ∧
        HBody (M g) (N g) cmp ξ Q r a θ hCircle} =
      {g : DistC | ∃ w : HWit, (g, w) ∈ HCodeRel M N cmp ξ Q r a θ} := by
  ext g
  constructor
  · rintro ⟨c, hc, hH⟩
    obtain ⟨u, v, γ, hb⟩ := (HBody_iff_exists_code _ _ cmp ξ Q r a θ c).mp hH
    exact ⟨(c, u, v, γ), hc, hb⟩
  · rintro ⟨⟨c, u, v, γ⟩, hc, hb⟩
    exact ⟨c, hc, (HBody_iff_exists_code _ _ cmp ξ Q r a θ c).mpr ⟨u, v, γ, hb⟩⟩

 
theorem HBodyEvent_um {M N : DistC → LSCMetric} (hM : Measurable M) (hN : Measurable N)
    {cmp : ℝ≥0∞ → ℝ≥0∞ → Prop} (hcmp : MeasurableSet {p : ℝ≥0∞ × ℝ≥0∞ | cmp p.1 p.2})
    (ξ Q : ℝ) (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet {g : DistC | ∃ hCircle : ℝ, IsCircleAverage g r 0 hCircle ∧
        HBody (M g) (N g) cmp ξ Q r a θ hCircle} := by
  rw [setOf_HBody_eq]
  exact LQGMetric.UMeasurableSet.setOf_exists (measurableSet_HCodeRel hM hN hcmp ξ Q r a θ)

 

theorem HEvent_um (D D' : DistC → LSCMetric) (hD : Measurable D) (hD' : Measurable D')
    (ξ Q : ℝ) (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet {g : DistC | OptimalConstants.Ratios.HEvent D D' ξ Q r a C θ g} := by
  have hcmp : MeasurableSet {p : ℝ≥0∞ × ℝ≥0∞ | ENNReal.ofReal C * p.1 ≤ p.2} :=
    measurableSet_le (measurable_const.mul measurable_fst) measurable_snd
  exact HBodyEvent_um (cmp := fun x y => ENNReal.ofReal C * x ≤ y) hD hD' hcmp ξ Q r a θ

 
theorem HtildeEvent_um (D D' : DistC → LSCMetric) (hD : Measurable D) (hD' : Measurable D')
    (ξ Q : ℝ) (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet {g : DistC | OptimalConstants.Ratios.HtildeEvent D D' ξ Q r a C θ g} := by
  have hcmp : MeasurableSet {p : ℝ≥0∞ × ℝ≥0∞ | p.1 ≤ ENNReal.ofReal C * p.2} :=
    measurableSet_le measurable_fst (measurable_const.mul measurable_snd)
  exact HBodyEvent_um (cmp := fun x y => x ≤ ENNReal.ofReal C * y) hD' hD hcmp ξ Q r a θ

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
