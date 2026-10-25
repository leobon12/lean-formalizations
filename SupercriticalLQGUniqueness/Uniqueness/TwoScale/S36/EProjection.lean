import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EClauses




 















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

 
theorem measurable_aroundDist_fixed (A : EuclideanAnnulus) :
    Measurable fun D : LSCMetric => aroundDist D A := by
  have h1 : Measurable fun D : LSCMetric =>
      ((D, (A.center, A.innerRadius, A.outerRadius)) : LSCMetric × (ℂ × ℝ × ℝ)) :=
    measurable_id.prodMk measurable_const
  have h2 := TwoScale.Consolidated.measurable_aroundRat.comp h1
  have heq : (fun D : LSCMetric => aroundDist D A) =
      TwoScale.Consolidated.aroundRat ∘ fun D : LSCMetric =>
        ((D, (A.center, A.innerRadius, A.outerRadius)) : LSCMetric × (ℂ × ℝ × ℝ)) := by
    funext D
    exact TwoScale.Consolidated.aroundDist_eq_aroundRat D A
  rw [heq]
  exact h2

 
def middleExh (z : ℂ) (r : ℝ) (n : ℕ) : Set ℂ :=
  Metric.closedBall z (3 * r / 2 - r / (n + 2)) \ Metric.ball z (3 * r / 4 + r / (n + 2))

theorem iUnion_middleExh (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ⋃ n : ℕ, middleExh z r n = TwoScale.S36Events.eventMiddle z r := by
  ext x
  simp only [mem_iUnion, middleExh, TwoScale.S36Events.eventMiddle, Set.mem_sdiff, Metric.mem_closedBall,
    Metric.mem_ball, not_lt, not_le]
  constructor
  · rintro ⟨n, h1, h2⟩
    have hpos : 0 < r / (n + 2) := div_pos hr (by positivity)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have hm : 0 < min (dist x z - 3 * r / 4) (3 * r / 2 - dist x z) :=
      lt_min (by linarith) (by linarith)
    obtain ⟨n, hn⟩ := exists_nat_gt (r / min (dist x z - 3 * r / 4) (3 * r / 2 - dist x z))
    have hn2 : (0 : ℝ) < n + 2 := by positivity
    have hlt : r / (n + 2) < min (dist x z - 3 * r / 4) (3 * r / 2 - dist x z) := by
      rw [div_lt_iff₀ hn2]
      have := (div_lt_iff₀ hm).mp hn
      nlinarith [min_le_left (dist x z - 3 * r / 4) (3 * r / 2 - dist x z)]
    exact ⟨n, by linarith [min_le_right (dist x z - 3 * r / 4) (3 * r / 2 - dist x z)],
      by linarith [min_le_left (dist x z - 3 * r / 4) (3 * r / 2 - dist x z)]⟩

 
theorem measurable_setDist_middle (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Measurable fun D : LSCMetric =>
      OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
  have hK : ∀ n : ℕ, IsCompact (middleExh z r n ×ˢ TwoScale.S36Events.eventBoundary z r) := fun n =>
    ((isCompact_closedBall _ _).diff Metric.isOpen_ball).prod
      ((isCompact_sphere _ _).union (isCompact_sphere _ _))
  have heq : (fun D : LSCMetric =>
      OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) =
      fun D => ⨅ n : ℕ, ⨅ q ∈ middleExh z r n ×ˢ TwoScale.S36Events.eventBoundary z r, D q := by
    funext D
    rw [← iUnion_middleExh z hr]
    simp only [OptimalConstants.Ratios.setDist, iInf_iUnion]
    refine iInf_congr fun n => ?_
    rw [← OptimalConstants.Ratios.setDist_eq_iInf_prod]
    rfl
  rw [heq]
  exact Measurable.iInf fun n => LSCMetric.measurable_iInf_of_isCompact (hK n)

 

 
def outerAnn (z : ℂ) (r : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  ⟨(z, (3 * r / 2, 2 * r)), by
    have hr : 0 < (r : ℝ) := r.2
    constructor <;> nlinarith⟩

 
def shortAnn (z : ℂ) (r : Ioi (0 : ℝ)) {q : Ioo (0 : ℝ) (1 / 100)}
    (a : Ioo (1 - (q : ℝ)) 1) : EuclideanAnnulus :=
  ⟨(z, ((a : ℝ) * r, r)), by
    have hr : 0 < (r : ℝ) := r.2
    have hq : (q : ℝ) < 1 / 100 := q.2.2
    have ha : 1 - (q : ℝ) < a := a.2.1
    have ha1 : (a : ℝ) < 1 := a.2.2
    constructor <;> nlinarith⟩

 
def E2Prop (D : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ)) (Cminus Cplus c : ℝ) : Prop :=
  aroundDist D (outerAnn z r) ≤
    min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)))
      (ENNReal.ofReal (Cminus / (2 * Cplus) * (q : ℝ) ^ (-(θ : ℝ))) *
        OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r))

 
def E4Prop (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) {q : Ioo (0 : ℝ) (1 / 100)}
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) : Prop :=
  aroundDist D (shortAnn z r a) ≤ ENNReal.ofReal K * acrossDist D (shortAnn z r a)

theorem attained_iff (D D' : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (C θ : Ioi (0 : ℝ)) (Cminus Cplus c : ℝ) :
    TwoScale.S36Events.Attained D D' ξ Q z r q a K C θ Cminus Cplus c ↔
      TwoScale.S36Events.EventClause1 D z r q θ ∧ E2Prop D ξ Q z r q a θ Cminus Cplus c ∧
        TwoScale.S36Events.EventClause3 D z r q a ∧ E4Prop D z r a K ∧
        E5Lit D D' ξ Q z r q a C θ Cminus Cplus c :=
  Iff.rfl

 

 
def Bad1 (D : DistC → LSCMetric) (z : ℂ) (r q θ : ℝ) :
    Set (DistC × (PathCode × ℝ × ℂ)) :=
  {x | IsIntCode (D x.1) (TwoScale.S36Events.eventCarrier z r) x.2.1 ∧
    x.2.1 0 ∈ TwoScale.S36Events.eventBoundary z r ∧ x.2.1 1 ∈ TwoScale.S36Events.eventBoundary z r ∧
    0 < x.2.2.1 ∧ x.2.2.1 ≤ q ∧ x.2.2.2 ∈ TwoScale.S36Events.eventMiddle z r ∧
    (∃ τ, x.2.1 τ ∈ Metric.ball x.2.2.2 (x.2.2.1 * r)) ∧
    ENNReal.ofReal (x.2.2.1 ^ θ) *
        TwoScale.S36Events.spherePairInf (D x.1) x.2.2.2 (x.2.2.1 * r) (Real.sqrt x.2.2.1 * r) <
      TwoScale.Consolidated.aroundAt (D x.1) x.2.2.2 (x.2.2.1 * r) (Real.sqrt x.2.2.1 * r)}

theorem e1Code_iff_forall_not_bad (D : DistC → LSCMetric) (z : ℂ) (r q θ : ℝ) (g : DistC) :
    E1Code (D g) z r q θ ↔ ∀ w : PathCode × ℝ × ℂ, (g, w) ∈ (Bad1 D z r q θ)ᶜ := by
  constructor
  · rintro h ⟨γ, δ, x⟩ ⟨hγ, h0, h1, hδ0, hδq, hx, hhit, hlt⟩
    exact (not_lt_of_ge (h γ δ x hγ h0 h1 hδ0 hδq hx hhit)) hlt
  · intro h γ δ x hγ h0 h1 hδ0 hδq hx hhit
    by_contra hn
    exact h (γ, δ, x) ⟨hγ, h0, h1, hδ0, hδq, hx, hhit, lt_of_not_ge hn⟩

 
theorem measurable_small_costs {D : DistC → LSCMetric} (hD : Measurable D) (r : ℝ) :
    Measurable (fun x : DistC × (PathCode × ℝ × ℂ) =>
      TwoScale.S36Events.spherePairInf (D x.1) x.2.2.2 (x.2.2.1 * r) (Real.sqrt x.2.2.1 * r)) ∧
    Measurable (fun x : DistC × (PathCode × ℝ × ℂ) =>
      TwoScale.Consolidated.aroundAt (D x.1) x.2.2.2 (x.2.2.1 * r) (Real.sqrt x.2.2.1 * r)) := by
  have hδ : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => x.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hx : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => x.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hρ : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => x.2.2.1 * r :=
    hδ.mul_const r
  have hσ : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => Real.sqrt x.2.2.1 * r :=
    (Real.continuous_sqrt.measurable.comp hδ).mul_const r
  have hM : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => D x.1 := hD.comp measurable_fst
  constructor
  · have h1 : Measurable fun x : DistC × (PathCode × ℝ × ℂ) =>
        ((D x.1, (x.2.2.2, (x.2.2.1 * r, Real.sqrt x.2.2.1 * r))) :
          LSCMetric × (ℂ × (ℝ × ℝ))) :=
      hM.prodMk (hx.prodMk (hρ.prodMk hσ))
    have h2 := TwoScale.S36Events.spherePairInf_joint_measurable.comp h1
    simpa only [Function.comp_def] using h2
  · have h1 : Measurable fun x : DistC × (PathCode × ℝ × ℂ) =>
        ((D x.1, (x.2.2.2, x.2.2.1 * r, Real.sqrt x.2.2.1 * r)) :
          LSCMetric × (ℂ × ℝ × ℝ)) :=
      hM.prodMk (hx.prodMk (hρ.prodMk hσ))
    have h2 := TwoScale.Consolidated.measurable_aroundRat.comp h1
    simpa only [Function.comp_def, TwoScale.Consolidated.aroundAt] using h2

theorem isOpen_hit (r : ℝ) :
    IsOpen {w : PathCode × ℝ × ℂ | ∃ τ, w.1 τ ∈ Metric.ball w.2.2 (w.2.1 * r)} := by
  have h : {w : PathCode × ℝ × ℂ | ∃ τ, w.1 τ ∈ Metric.ball w.2.2 (w.2.1 * r)} =
      ⋃ τ : unitInterval, {w : PathCode × ℝ × ℂ | dist (w.1 τ) w.2.2 < w.2.1 * r} := by
    ext w
    simp only [mem_ofPred_eq, mem_iUnion, Metric.mem_ball]
  rw [h]
  refine isOpen_iUnion fun τ => isOpen_lt ?_ ?_
  · exact ((continuous_eval_const τ).comp continuous_fst).dist (continuous_snd.comp continuous_snd)
  · exact (continuous_fst.comp continuous_snd).mul continuous_const

theorem measurableSet_bad1 {D : DistC → LSCMetric} (hD : Measurable D) (z : ℂ) (r q θ : ℝ) :
    MeasurableSet (Bad1 D z r q θ) := by
  have hY := isCompact_eventCarrier z r
  have hM : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => D x.1 := hD.comp measurable_fst
  have hγ : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => x.2.1 :=
    measurable_fst.comp measurable_snd
  have hδ : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => x.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hx : Measurable fun x : DistC × (PathCode × ℝ × ℂ) => x.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have h1 : MeasurableSet {x : DistC × (PathCode × ℝ × ℂ) |
      IsIntCode (D x.1) (TwoScale.S36Events.eventCarrier z r) x.2.1} :=
    (hM.prodMk hγ) (measurableSet_isIntCode hY)
  have h2 : MeasurableSet {x : DistC × (PathCode × ℝ × ℂ) |
      x.2.1 0 ∈ TwoScale.S36Events.eventBoundary z r} :=
    ((continuous_eval_const (0 : unitInterval)).measurable.comp hγ)
      (isClosed_eventBoundary z r).measurableSet
  have h3 : MeasurableSet {x : DistC × (PathCode × ℝ × ℂ) |
      x.2.1 1 ∈ TwoScale.S36Events.eventBoundary z r} :=
    ((continuous_eval_const (1 : unitInterval)).measurable.comp hγ)
      (isClosed_eventBoundary z r).measurableSet
  have h4 : MeasurableSet {x : DistC × (PathCode × ℝ × ℂ) | 0 < x.2.2.1} :=
    measurableSet_lt measurable_const hδ
  have h5 : MeasurableSet {x : DistC × (PathCode × ℝ × ℂ) | x.2.2.1 ≤ q} :=
    measurableSet_le hδ measurable_const
  have h6 : MeasurableSet {x : DistC × (PathCode × ℝ × ℂ) | x.2.2.2 ∈ TwoScale.S36Events.eventMiddle z r} :=
    hx (isOpen_eventMiddle z r).measurableSet
  have h7 : MeasurableSet {x : DistC × (PathCode × ℝ × ℂ) |
      ∃ τ, x.2.1 τ ∈ Metric.ball x.2.2.2 (x.2.2.1 * r)} :=
    measurable_snd (isOpen_hit r).measurableSet
  obtain ⟨hacr, haro⟩ := measurable_small_costs hD r
  have h8 : MeasurableSet {x : DistC × (PathCode × ℝ × ℂ) |
      ENNReal.ofReal (x.2.2.1 ^ θ) *
          TwoScale.S36Events.spherePairInf (D x.1) x.2.2.2 (x.2.2.1 * r) (Real.sqrt x.2.2.1 * r) <
        TwoScale.Consolidated.aroundAt (D x.1) x.2.2.2 (x.2.2.1 * r) (Real.sqrt x.2.2.1 * r)} :=
    measurableSet_lt ((hδ.pow_const θ).ennreal_ofReal.mul hacr) haro
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter (h7.inter h8))))))

 
theorem E1set_um {D : DistC → LSCMetric} (hD : Measurable D) (z : ℂ) {r q : ℝ} (θ : ℝ)
    (hr : 0 < r) (hq : q < 1) :
    LQGMetric.UMeasurableSet {g : DistC | TwoScale.S36Events.EventClause1 (D g) z r q θ} := by
  have heq : {g : DistC | TwoScale.S36Events.EventClause1 (D g) z r q θ} =
      {g : DistC | ∀ w : PathCode × ℝ × ℂ, (g, w) ∈ (Bad1 D z r q θ)ᶜ} := by
    ext g
    exact (eventClause1_iff_code (D g) z θ hr hq).trans (e1Code_iff_forall_not_bad D z r q θ g)
  rw [heq]
  exact LQGMetric.UMeasurableSet.setOf_forall (measurableSet_bad1 hD z r q θ).compl

 

 
theorem continuous_codeExt_joint : Continuous fun p : PathCode × ℝ => codeExt p.1 p.2 := by
  have h : Continuous fun p : PathCode × ℝ =>
      (p.1, Set.projIcc (0 : ℝ) 1 (zero_le_one' ℝ) p.2) :=
    continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)
  exact continuous_eval.comp h

 
def Bad3 (D : DistC → LSCMetric) (z : ℂ) (r q a : ℝ) :
    Set (DistC × (PathCode × ℝ × ℝ)) :=
  {x | IsIntCode (D x.1) (TwoScale.S36Events.eventCarrier z r) x.2.1 ∧
    x.2.1 0 ∈ TwoScale.S36Events.eventBoundary z r ∧ x.2.1 1 ∈ TwoScale.S36Events.eventBoundary z r ∧
    0 ≤ x.2.2.1 ∧ x.2.2.1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ 1 ∧
    (∀ τ : ℝ, codeExt x.2.1 (max x.2.2.1 (min x.2.2.2 τ)) ∈ shortCarrier z r a) ∧
    q * r < dist (codeExt x.2.1 x.2.2.1) (codeExt x.2.1 x.2.2.2)}

theorem e3Code_iff_forall_not_bad (D : DistC → LSCMetric) (z : ℂ) (r q a : ℝ) (g : DistC) :
    E3Code (D g) z r q a ↔ ∀ w : PathCode × ℝ × ℝ, (g, w) ∈ (Bad3 D z r q a)ᶜ := by
  constructor
  · rintro h ⟨γ, σ, σ'⟩ ⟨hγ, h0, h1, hσ0, hσσ', hσ'1, hseg, hlt⟩
    exact (not_lt_of_ge (h γ σ σ' hγ h0 h1 hσ0 hσσ' hσ'1 hseg)) hlt
  · intro h γ σ σ' hγ h0 h1 hσ0 hσσ' hσ'1 hseg
    by_contra hn
    exact h (γ, σ, σ') ⟨hγ, h0, h1, hσ0, hσσ', hσ'1, hseg, lt_of_not_ge hn⟩

theorem isClosed_clampedSeg (z : ℂ) (r a : ℝ) :
    IsClosed {w : PathCode × ℝ × ℝ |
      ∀ τ : ℝ, codeExt w.1 (max w.2.1 (min w.2.2 τ)) ∈ shortCarrier z r a} := by
  have h : {w : PathCode × ℝ × ℝ |
      ∀ τ : ℝ, codeExt w.1 (max w.2.1 (min w.2.2 τ)) ∈ shortCarrier z r a} =
      ⋂ τ : ℝ, {w : PathCode × ℝ × ℝ |
        codeExt w.1 (max w.2.1 (min w.2.2 τ)) ∈ shortCarrier z r a} := by
    ext w
    simp only [mem_ofPred_eq, mem_iInter]
  rw [h]
  refine isClosed_iInter fun τ => (isCompact_shortCarrier z r a).isClosed.preimage ?_
  have hc : Continuous fun w : PathCode × ℝ × ℝ => (w.1, max w.2.1 (min w.2.2 τ)) :=
    continuous_fst.prodMk ((continuous_fst.comp continuous_snd).max
      ((continuous_snd.comp continuous_snd).min continuous_const))
  exact continuous_codeExt_joint.comp hc

theorem measurableSet_bad3 {D : DistC → LSCMetric} (hD : Measurable D) (z : ℂ) (r q a : ℝ) :
    MeasurableSet (Bad3 D z r q a) := by
  have hY := isCompact_eventCarrier z r
  have hM : Measurable fun x : DistC × (PathCode × ℝ × ℝ) => D x.1 := hD.comp measurable_fst
  have hγ : Measurable fun x : DistC × (PathCode × ℝ × ℝ) => x.2.1 :=
    measurable_fst.comp measurable_snd
  have hσ : Measurable fun x : DistC × (PathCode × ℝ × ℝ) => x.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hσ' : Measurable fun x : DistC × (PathCode × ℝ × ℝ) => x.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have h1 : MeasurableSet {x : DistC × (PathCode × ℝ × ℝ) |
      IsIntCode (D x.1) (TwoScale.S36Events.eventCarrier z r) x.2.1} :=
    (hM.prodMk hγ) (measurableSet_isIntCode hY)
  have h2 : MeasurableSet {x : DistC × (PathCode × ℝ × ℝ) |
      x.2.1 0 ∈ TwoScale.S36Events.eventBoundary z r} :=
    ((continuous_eval_const (0 : unitInterval)).measurable.comp hγ)
      (isClosed_eventBoundary z r).measurableSet
  have h3 : MeasurableSet {x : DistC × (PathCode × ℝ × ℝ) |
      x.2.1 1 ∈ TwoScale.S36Events.eventBoundary z r} :=
    ((continuous_eval_const (1 : unitInterval)).measurable.comp hγ)
      (isClosed_eventBoundary z r).measurableSet
  have h4 : MeasurableSet {x : DistC × (PathCode × ℝ × ℝ) | 0 ≤ x.2.2.1} :=
    measurableSet_le measurable_const hσ
  have h5 : MeasurableSet {x : DistC × (PathCode × ℝ × ℝ) | x.2.2.1 ≤ x.2.2.2} :=
    measurableSet_le hσ hσ'
  have h6 : MeasurableSet {x : DistC × (PathCode × ℝ × ℝ) | x.2.2.2 ≤ 1} :=
    measurableSet_le hσ' measurable_const
  have h7 : MeasurableSet {x : DistC × (PathCode × ℝ × ℝ) |
      ∀ τ : ℝ, codeExt x.2.1 (max x.2.2.1 (min x.2.2.2 τ)) ∈ shortCarrier z r a} :=
    measurable_snd (isClosed_clampedSeg z r a).measurableSet
  have h8 : MeasurableSet {x : DistC × (PathCode × ℝ × ℝ) |
      q * r < dist (codeExt x.2.1 x.2.2.1) (codeExt x.2.1 x.2.2.2)} := by
    have hc : Continuous fun w : PathCode × ℝ × ℝ =>
        dist (codeExt w.1 w.2.1) (codeExt w.1 w.2.2) :=
      (continuous_codeExt_joint.comp (continuous_fst.prodMk
        (continuous_fst.comp continuous_snd))).dist
        (continuous_codeExt_joint.comp (continuous_fst.prodMk
          (continuous_snd.comp continuous_snd)))
    exact measurable_snd (isOpen_lt continuous_const hc).measurableSet
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter (h7.inter h8))))))

 
theorem E3set_um {D : DistC → LSCMetric} (hD : Measurable D) (z : ℂ) {r q : ℝ} (a : ℝ)
    (hr : 0 < r) (hq : 0 < q) :
    LQGMetric.UMeasurableSet {g : DistC | TwoScale.S36Events.EventClause3 (D g) z r q a} := by
  have heq : {g : DistC | TwoScale.S36Events.EventClause3 (D g) z r q a} =
      {g : DistC | ∀ w : PathCode × ℝ × ℝ, (g, w) ∈ (Bad3 D z r q a)ᶜ} := by
    ext g
    exact (eventClause3_iff_code (D g) z a hr hq).trans (e3Code_iff_forall_not_bad D z r q a g)
  rw [heq]
  exact LQGMetric.UMeasurableSet.setOf_forall (measurableSet_bad3 hD z r q a).compl

 

theorem measurableSet_E2rel {D : DistC → LSCMetric} (hD : Measurable D) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (θ : Ioi (0 : ℝ)) (Cminus Cplus : ℝ) :
    MeasurableSet {x : DistC × ℝ | E2Prop (D x.1) ξ Q z r q a θ Cminus Cplus x.2} := by
  have hM : Measurable fun x : DistC × ℝ => D x.1 := hD.comp measurable_fst
  have harnd : Measurable fun x : DistC × ℝ => aroundDist (D x.1) (outerAnn z r) :=
    (measurable_aroundDist_fixed _).comp hM
  have hb1 : Measurable fun x : DistC × ℝ =>
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * x.2)) :=
    (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul measurable_snd))).ennreal_ofReal
  have hb2 : Measurable fun x : DistC × ℝ =>
      ENNReal.ofReal (Cminus / (2 * Cplus) * (q : ℝ) ^ (-(θ : ℝ))) *
        OptimalConstants.Ratios.setDist (D x.1) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) :=
    measurable_const.mul ((measurable_setDist_middle z r.2).comp hM)
  exact measurableSet_le harnd (hb1.min hb2)

 
theorem E2all_um {D : DistC → LSCMetric} (hD : Measurable D) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (θ : Ioi (0 : ℝ)) (Cminus Cplus : ℝ) :
    LQGMetric.UMeasurableSet {g : DistC | ∀ c : ℝ, IsCircleAverage g r z c →
      E2Prop (D g) ξ Q z r q a θ Cminus Cplus c} := by
  have hCA : MeasurableSet {x : DistC × ℝ | IsCircleAverage x.1 r z x.2} :=
    measurableSet_isCircleAverage_rel (c := fun t : ℝ => t) r z measurable_id
  have hS := hCA.imp (measurableSet_E2rel hD ξ Q z r q a θ Cminus Cplus)
  exact LQGMetric.UMeasurableSet.setOf_forall hS

theorem measurableSet_E4 {D : DistC → LSCMetric} (hD : Measurable D) (z : ℂ)
    (r : Ioi (0 : ℝ)) {q : Ioo (0 : ℝ) (1 / 100)} (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) :
    MeasurableSet {g : DistC | E4Prop (D g) z r a K} :=
  measurableSet_le ((measurable_aroundDist_fixed _).comp hD)
    (measurable_const.mul ((measurable_acrossDist _).comp hD))

 

 
def Bad5 (D D' : DistC → LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (C θ : Ioi (0 : ℝ))
    (Cminus Cplus : ℝ) : Set (DistC × HWit) :=
  {x | IsCircleAverage x.1 r z x.2.1 ∧
    x.2.2.1 ∈ Metric.sphere z (a * r) ∧ x.2.2.2.1 ∈ Metric.sphere z r ∧
    dist x.2.2.1 x.2.2.2.1 ≤ q * r ∧
    TwoScale.Consolidated.aroundAt (D x.1) x.2.2.2.1 (q * r) (Real.sqrt q * r) ≤
      ENNReal.ofReal (Cminus / (2 * Cplus)) *
        OptimalConstants.Ratios.setDist (D x.1) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) ∧
    IsGeoCode (D x.1) x.2.2.2.2 ∧ x.2.2.2.2 0 = x.2.2.1 ∧ x.2.2.2.2 1 = x.2.2.2.1 ∧
    (∀ τ, x.2.2.2.2 τ ∈ shortCarrier z r a) ∧
    (∀ τ₁ τ₂, dist (x.2.2.2.2 τ₁) (x.2.2.2.2 τ₂) ≤ (r : ℝ) / 100) ∧
    D x.1 (x.2.2.1, x.2.2.2.1) ≤
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * x.2.1)) ∧
    (D x.1, (x.2.2.1, D x.1 (x.2.2.1, x.2.2.2.1))) ∈ LoopSet r (aWin a) θ ∧
    (D x.1, (x.2.2.2.1, D x.1 (x.2.2.1, x.2.2.2.1))) ∈ LoopSet r (aWin a) θ ∧
    ENNReal.ofReal C * D x.1 (x.2.2.1, x.2.2.2.1) < D' x.1 (x.2.2.1, x.2.2.2.1)}

theorem e5all_iff_forall_not_bad (D D' : DistC → LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (C θ : Ioi (0 : ℝ)) (Cminus Cplus : ℝ) (g : DistC) :
    (∀ c : ℝ, IsCircleAverage g r z c → E5Code (D g) (D' g) ξ Q z r q a C θ Cminus Cplus c) ↔
      ∀ w : HWit, (g, w) ∈ (Bad5 D D' ξ Q z r q a C θ Cminus Cplus)ᶜ := by
  constructor
  · rintro h ⟨c, u, v, γ⟩ ⟨hc, hu, hv, huv, hsh, hγ, hγ0, hγ1, hγK, hγd, hN, hLu, hLv, hlt⟩
    exact (not_lt_of_ge (h c hc u v γ hu hv huv hsh hγ hγ0 hγ1 hγK hγd hN hLu hLv)) hlt
  · intro h c hc u v γ hu hv huv hsh hγ hγ0 hγ1 hγK hγd hN hLu hLv
    by_contra hn
    exact h (c, u, v, γ) ⟨hc, hu, hv, huv, hsh, hγ, hγ0, hγ1, hγK, hγd, hN, hLu, hLv,
      lt_of_not_ge hn⟩

theorem measurableSet_bad5 {D D' : DistC → LSCMetric} (hD : Measurable D)
    (hD' : Measurable D') (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (C θ : Ioi (0 : ℝ))
    (Cminus Cplus : ℝ) : MeasurableSet (Bad5 D D' ξ Q z r q a C θ Cminus Cplus) := by
  have hMuv := measurable_wMuv hD
  have hNuv := measurable_wMuv hD'
  have h0 : MeasurableSet {x : DistC × HWit | IsCircleAverage x.1 r z x.2.1} :=
    measurableSet_isCircleAverage_rel r z measurable_fst
  have h1 : MeasurableSet {x : DistC × HWit | x.2.2.1 ∈ Metric.sphere z (a * r)} :=
    measurable_wu Metric.isClosed_sphere.measurableSet
  have h2 : MeasurableSet {x : DistC × HWit | x.2.2.2.1 ∈ Metric.sphere z r} :=
    measurable_wv Metric.isClosed_sphere.measurableSet
  have h3 : MeasurableSet {x : DistC × HWit | dist x.2.2.1 x.2.2.2.1 ≤ q * r} :=
    measurableSet_le (measurable_wu.dist measurable_wv) measurable_const
  have hsh : Measurable fun x : DistC × HWit =>
      TwoScale.Consolidated.aroundAt (D x.1) x.2.2.2.1 (q * r) (Real.sqrt q * r) := by
    have h1' : Measurable fun x : DistC × HWit =>
        ((D x.1, (x.2.2.2.1, (q : ℝ) * r, Real.sqrt q * r)) : LSCMetric × (ℂ × ℝ × ℝ)) :=
      (measurable_wM hD).prodMk (measurable_wv.prodMk measurable_const)
    have h2' := TwoScale.Consolidated.measurable_aroundRat.comp h1'
    simpa only [Function.comp_def, TwoScale.Consolidated.aroundAt] using h2'
  have h4 : MeasurableSet {x : DistC × HWit |
      TwoScale.Consolidated.aroundAt (D x.1) x.2.2.2.1 (q * r) (Real.sqrt q * r) ≤
        ENNReal.ofReal (Cminus / (2 * Cplus)) *
          OptimalConstants.Ratios.setDist (D x.1) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)} :=
    measurableSet_le hsh (measurable_const.mul
      ((measurable_setDist_middle z r.2).comp (measurable_wM hD)))
  have h5 : MeasurableSet {x : DistC × HWit | IsGeoCode (D x.1) x.2.2.2.2} :=
    ((measurable_wM hD).prodMk measurable_wγ) measurableSet_isGeoCode
  have h6 : MeasurableSet {x : DistC × HWit | x.2.2.2.2 0 = x.2.2.1} :=
    measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_wγ) measurable_wu
  have h7 : MeasurableSet {x : DistC × HWit | x.2.2.2.2 1 = x.2.2.2.1} :=
    measurableSet_eq_fun ((continuous_eval_const 1).measurable.comp measurable_wγ) measurable_wv
  have h8 : MeasurableSet {x : DistC × HWit | ∀ τ, x.2.2.2.2 τ ∈ shortCarrier z r a} :=
    measurableSet_code_closed (isClosed_trace _ (isCompact_shortCarrier z r a).isClosed)
  have h9 : MeasurableSet {x : DistC × HWit |
      ∀ τ₁ τ₂, dist (x.2.2.2.2 τ₁) (x.2.2.2.2 τ₂) ≤ (r : ℝ) / 100} :=
    measurableSet_code_closed (isClosed_pairDist _)
  have hbound : Measurable fun x : DistC × HWit =>
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * x.2.1)) :=
    (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul measurable_wc))).ennreal_ofReal
  have h10 : MeasurableSet {x : DistC × HWit | D x.1 (x.2.2.1, x.2.2.2.1) ≤
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * x.2.1))} :=
    measurableSet_le hMuv hbound
  have h11 : MeasurableSet {x : DistC × HWit |
      (D x.1, (x.2.2.1, D x.1 (x.2.2.1, x.2.2.2.1))) ∈ LoopSet r (aWin a) θ} :=
    ((measurable_wM hD).prodMk (measurable_wu.prodMk hMuv)) (measurableSet_loopSet r _ θ)
  have h12 : MeasurableSet {x : DistC × HWit |
      (D x.1, (x.2.2.2.1, D x.1 (x.2.2.1, x.2.2.2.1))) ∈ LoopSet r (aWin a) θ} :=
    ((measurable_wM hD).prodMk (measurable_wv.prodMk hMuv)) (measurableSet_loopSet r _ θ)
  have h13 : MeasurableSet {x : DistC × HWit |
      ENNReal.ofReal C * D x.1 (x.2.2.1, x.2.2.2.1) < D' x.1 (x.2.2.1, x.2.2.2.1)} :=
    measurableSet_lt (measurable_const.mul hMuv) hNuv
  exact h0.inter (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter (h7.inter
    (h8.inter (h9.inter (h10.inter (h11.inter (h12.inter h13))))))))))))

 
theorem E5all_um {D D' : DistC → LSCMetric} (hD : Measurable D) (hD' : Measurable D')
    (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (C θ : Ioi (0 : ℝ)) (Cminus Cplus : ℝ) :
    LQGMetric.UMeasurableSet {g : DistC | ∀ c : ℝ, IsCircleAverage g r z c →
      E5Lit (D g) (D' g) ξ Q z r q a C θ Cminus Cplus c} := by
  have heq : {g : DistC | ∀ c : ℝ, IsCircleAverage g r z c →
      E5Lit (D g) (D' g) ξ Q z r q a C θ Cminus Cplus c} =
      {g : DistC | ∀ w : HWit, (g, w) ∈ (Bad5 D D' ξ Q z r q a C θ Cminus Cplus)ᶜ} := by
    ext g
    have h := e5all_iff_forall_not_bad D D' ξ Q z r q a C θ Cminus Cplus g
    refine Iff.trans ?_ h
    exact forall_congr' fun c => imp_congr_right fun _ =>
      e5Lit_iff_code (D g) (D' g) ξ Q z r q a C θ Cminus Cplus c
  rw [heq]
  exact LQGMetric.UMeasurableSet.setOf_forall
    (measurableSet_bad5 hD hD' ξ Q z r q a C θ Cminus Cplus).compl

 

theorem measurableSet_exists_circleAverage (r : Ioi (0 : ℝ)) (z : ℂ) :
    MeasurableSet {g : DistC | ∃ c : ℝ, IsCircleAverage g r z c} := by
  have h := measurableSet_exists_tendsto (l := atTop)
    (f := fun (n : ℕ) (g : DistC) => g (LQGMetric.CircleAvg.circBump n z (r : ℝ)))
    (fun n => LQGMetric.measurable_evalDist _)
  have heq : {g : DistC | ∃ c : ℝ, IsCircleAverage g r z c} =
      {g : DistC | ∃ c : ℝ, Tendsto (fun n : ℕ => g (LQGMetric.CircleAvg.circBump n z (r : ℝ)))
        atTop (𝓝 c)} := by
    ext g
    exact exists_congr fun c => isCircleAverage_iff_circBump g r z c
  rw [heq]
  exact h

 

theorem AttainedEvent_um (D D' : DistC → LSCMetric) (hD : Measurable D) (hD' : Measurable D')
    (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ)) (Cminus Cplus : ℝ) :
    LQGMetric.UMeasurableSet (TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cminus Cplus) := by
  have hr : (0 : ℝ) < r := r.2
  have hq0 : (0 : ℝ) < q := q.2.1
  have hq1 : (q : ℝ) < 1 := by have := q.2.2; linarith
  have heq : TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cminus Cplus =
      {g : DistC | ∃ c : ℝ, IsCircleAverage g r z c} ∩
        {g : DistC | TwoScale.S36Events.EventClause1 (D g) z r q θ} ∩
        {g : DistC | TwoScale.S36Events.EventClause3 (D g) z r q a} ∩
        {g : DistC | E4Prop (D g) z r a K} ∩
        {g : DistC | ∀ c : ℝ, IsCircleAverage g r z c →
          E2Prop (D g) ξ Q z r q a θ Cminus Cplus c} ∩
        {g : DistC | ∀ c : ℝ, IsCircleAverage g r z c →
          E5Lit (D g) (D' g) ξ Q z r q a C θ Cminus Cplus c} := by
    ext g
    constructor
    · rintro ⟨c, hc, hA⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ :=
        (attained_iff (D g) (D' g) ξ Q z r q a K C θ Cminus Cplus c).mp hA
      refine ⟨⟨⟨⟨⟨⟨c, hc⟩, h1⟩, h3⟩, h4⟩, fun c' hc' => ?_⟩, fun c' hc' => ?_⟩
      · rw [← isCircleAverage_unique hc hc']
        exact h2
      · rw [← isCircleAverage_unique hc hc']
        exact h5
    · rintro ⟨⟨⟨⟨⟨⟨c, hc⟩, h1⟩, h3⟩, h4⟩, h2⟩, h5⟩
      exact ⟨c, hc, (attained_iff (D g) (D' g) ξ Q z r q a K C θ Cminus Cplus c).mpr
        ⟨h1, h2 c hc, h3, h4, h5 c hc⟩⟩
  rw [heq]
  exact (((((LQGMetric.UMeasurableSet.of_measurableSet
    (measurableSet_exists_circleAverage r z)).inter (E1set_um hD z θ hr hq1)).inter
    (E3set_um hD z a hr hq0)).inter
    (LQGMetric.UMeasurableSet.of_measurableSet (measurableSet_E4 hD z r a K))).inter
    (E2all_um hD ξ Q z r q a θ Cminus Cplus)).inter
    (E5all_um hD hD' ξ Q z r q a C θ Cminus Cplus)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
