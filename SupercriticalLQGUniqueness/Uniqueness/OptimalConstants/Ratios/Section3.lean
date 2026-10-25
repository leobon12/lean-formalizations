import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import SLUMetricAPI2




 







set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios

open LQGMetric (DistC)

 
def Singular (D : LSCMetric) (z : ℂ) : Prop :=
  ∀ w : ℂ, w ≠ z → D (z, w) = ⊤

 
def RatioPair (D : LSCMetric) (z w : ℂ) : Prop :=
  z ≠ w ∧ ¬ Singular D z ∧ ¬ Singular D w ∧
    0 < D (z, w) ∧ D (z, w) < ⊤

 
def lowerOptimal (D D' : LSCMetric) : ℝ≥0∞ :=
  ⨅ (z : ℂ) (w : ℂ) (_ : RatioPair D z w), D' (z, w) / D (z, w)

 
def upperOptimal (D D' : LSCMetric) : ℝ≥0∞ :=
  ⨆ (z : ℂ) (w : ℂ) (_ : RatioPair D z w), D' (z, w) / D (z, w)

 
theorem lowerOptimal_le_ratio (D D' : LSCMetric) {z w : ℂ}
    (h : RatioPair D z w) :
    lowerOptimal D D' ≤ D' (z, w) / D (z, w) := by
  exact iInf_le_of_le z (iInf_le_of_le w
    (iInf_le (fun _ : RatioPair D z w => D' (z, w) / D (z, w)) h))

 
theorem ratio_le_upperOptimal (D D' : LSCMetric) {z w : ℂ}
    (h : RatioPair D z w) :
    D' (z, w) / D (z, w) ≤ upperOptimal D D' := by
  exact le_iSup_of_le z (le_iSup_of_le w
    (le_iSup (fun _ : RatioPair D z w => D' (z, w) / D (z, w)) h))

 
theorem measurable_fixedRatio (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D') (z w : ℂ) :
    Measurable fun g : DistC =>
      (D' g (z, w)).toReal / (D g (z, w)).toReal := by
  exact ((LSCMetric.measurable_apply (z, w)).comp hD').ennreal_toReal.div
    ((LSCMetric.measurable_apply (z, w)).comp hD).ennreal_toReal

 
def BiLipBound (D D' : LSCMetric) (c C : ℝ≥0∞) : Prop :=
  ∀ z w : ℂ, c * D (z, w) ≤ D' (z, w) ∧
    D' (z, w) ≤ C * D (z, w)

 
theorem ratio_mem_Icc_of_biLipBound {D D' : LSCMetric} {c C : ℝ≥0∞}
    (hB : BiLipBound D D' c C) {z w : ℂ} (hp : RatioPair D z w) :
    c ≤ D' (z, w) / D (z, w) ∧
      D' (z, w) / D (z, w) ≤ C := by
  have h0 : D (z, w) ≠ 0 := hp.2.2.2.1.ne'
  have ht : D (z, w) ≠ ⊤ := hp.2.2.2.2.ne
  constructor
  · exact (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht)).2
      (by simpa only [mul_comm] using (hB z w).1)
  · exact (ENNReal.div_le_iff' h0 ht).2
      (by simpa only [mul_comm] using (hB z w).2)

 
theorem optimal_mem_Icc_of_biLipBound {D D' : LSCMetric} {c C : ℝ≥0∞}
    (hB : BiLipBound D D' c C) :
    c ≤ lowerOptimal D D' ∧ upperOptimal D D' ≤ C := by
  constructor
  · exact le_iInf fun z => le_iInf fun w => le_iInf fun hp =>
      (ratio_mem_Icc_of_biLipBound hB hp).1
  · exact iSup_le fun z => iSup_le fun w => iSup_le fun hp =>
      (ratio_mem_Icc_of_biLipBound hB hp).2

 
theorem lowerOptimal_le_upperOptimal {D D' : LSCMetric}
    (hpair : ∃ z w : ℂ, RatioPair D z w) :
    lowerOptimal D D' ≤ upperOptimal D D' := by
  obtain ⟨z, w, hp⟩ := hpair
  exact (lowerOptimal_le_ratio D D' hp).trans (ratio_le_upperOptimal D D' hp)

 
theorem optimal_pos_finite_of_biLipBound {D D' : LSCMetric} {c C : ℝ≥0∞}
    (hc : 0 < c) (hC : C < ⊤) (hB : BiLipBound D D' c C)
    (hpair : ∃ z w : ℂ, RatioPair D z w) :
    0 < lowerOptimal D D' ∧
      lowerOptimal D D' ≤ upperOptimal D D' ∧ upperOptimal D D' < ⊤ := by
  obtain ⟨hl, hu⟩ := optimal_mem_Icc_of_biLipBound hB
  exact ⟨hc.trans_le hl, lowerOptimal_le_upperOptimal hpair, hu.trans_lt hC⟩

 

theorem optimal_allPairs_of_biLipBound {D D' : LSCMetric} {c C : ℝ≥0∞}
    (hc : 0 < c) (hB : BiLipBound D D' c C)
    (hpair : ∃ u v : ℂ, RatioPair D u v) :
    ∀ z w : ℂ,
      lowerOptimal D D' * D (z, w) ≤ D' (z, w) ∧
      D' (z, w) ≤ upperOptimal D D' * D (z, w) := by
  intro z w
  by_cases h0 : D (z, w) = 0
  · have hzw : z = w := D.isExtMetric.2.1 z w h0
    subst w
    simp only [D.isExtMetric.1, D'.isExtMetric.1, mul_zero, le_refl, and_self]
  by_cases ht : D (z, w) = ⊤
  · have hD't : D' (z, w) = ⊤ := by
      have h := (hB z w).1
      rw [ht, ENNReal.mul_top hc.ne'] at h
      exact top_le_iff.mp h
    have hlpos : 0 < lowerOptimal D D' :=
      hc.trans_le (optimal_mem_Icc_of_biLipBound hB).1
    have hupos : 0 < upperOptimal D D' :=
      hlpos.trans_le (lowerOptimal_le_upperOptimal hpair)
    simp only [ht, hD't, ENNReal.mul_top hlpos.ne', ENNReal.mul_top hupos.ne', le_refl,
      and_self]
  have hp : RatioPair D z w := by
    have hzw : z ≠ w := by
      intro hzw
      apply h0
      rw [hzw]
      exact D.isExtMetric.1 w
    refine ⟨hzw, ?_, ?_, pos_iff_ne_zero.mpr h0, lt_top_iff_ne_top.mpr ht⟩
    · intro hs
      exact ht (hs w hzw.symm)
    · intro hs
      exact ht ((D.isExtMetric.2.2.1 z w).trans (hs z hzw))
  have hDpos : D (z, w) ≠ 0 := h0
  have hDfin : D (z, w) ≠ ⊤ := ht
  constructor
  · exact (ENNReal.le_div_iff_mul_le (Or.inl hDpos) (Or.inl hDfin)).1
      (lowerOptimal_le_ratio D D' hp)
  · simpa only [mul_comm] using (ENNReal.div_le_iff' hDpos hDfin).1
      (ratio_le_upperOptimal D D' hp)

 

theorem ae_allPairs_of_ae_optima {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D D' : Ω → LSCMetric) {c C cMinus cPlus : ℝ≥0∞}
    (hc : 0 < c)
    (hB : ∀ᵐ ω ∂P, BiLipBound (D ω) (D' ω) c C)
    (hpair : ∀ᵐ ω ∂P, ∃ u v : ℂ, RatioPair (D ω) u v)
    (hMinus : ∀ᵐ ω ∂P, lowerOptimal (D ω) (D' ω) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, upperOptimal (D ω) (D' ω) = cPlus) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ,
      cMinus * D ω (z, w) ≤ D' ω (z, w) ∧
      D' ω (z, w) ≤ cPlus * D ω (z, w) := by
  filter_upwards [hB, hpair, hMinus, hPlus] with ω hb hp hm hM z w
  simpa only [hm, hM] using (optimal_allPairs_of_biLipBound hc hb hp z w)

 
theorem ratioPair_iff_finite_positive (D : LSCMetric) (z w : ℂ) :
    RatioPair D z w ↔ z ≠ w ∧ 0 < D (z, w) ∧ D (z, w) < ⊤ := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩
  · rintro ⟨hzw, hp, hf⟩
    refine ⟨hzw, ?_, ?_, hp, hf⟩
    · intro hs
      exact hf.ne (hs w hzw.symm)
    · intro hs
      exact hf.ne ((D.isExtMetric.2.2.1 z w).trans (hs z hzw))

 
theorem measurableSet_ratioPair_fixed (D : DistC → LSCMetric)
    (hD : Measurable D) (z w : ℂ) :
    MeasurableSet {g : DistC | RatioPair (D g) z w} := by
  have hm : Measurable fun g : DistC => D g (z, w) :=
    (LSCMetric.measurable_apply (z, w)).comp hD
  by_cases hzw : z ≠ w
  · have h1 : MeasurableSet {g : DistC | (0 : ℝ≥0∞) < D g (z, w)} :=
      measurableSet_lt measurable_const hm
    have h2 : MeasurableSet {g : DistC | D g (z, w) < (⊤ : ℝ≥0∞)} :=
      measurableSet_lt hm measurable_const
    simpa [ratioPair_iff_finite_positive, hzw, Set.ofPred_and] using h1.inter h2
  · simp only [ratioPair_iff_finite_positive, hzw, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

 
def setDist (D : LSCMetric) (A B : Set ℂ) : ℝ≥0∞ :=
  ⨅ z ∈ A, ⨅ w ∈ B, D (z, w)

theorem setDist_eq_iInf_prod (D : LSCMetric) (A B : Set ℂ) :
    setDist D A B = ⨅ q ∈ A ×ˢ B, D q := by
  refine le_antisymm (le_iInf₂ fun q hq => ?_) (le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_)
  · exact iInf₂_le_of_le q.1 hq.1 (iInf₂_le q.2 hq.2)
  · exact iInf₂_le (z, w) ⟨hz, hw⟩

 
theorem measurable_setDist_open (A B : Set ℂ) (hA : IsOpen A) (hB : IsOpen B) :
    Measurable fun D : LSCMetric => setDist D A B := by
  have hO : IsOpen (A ×ˢ B) := hA.prod hB
  simpa only [setDist_eq_iInf_prod] using LSCMetric.measurable_iInf_of_isOpen hO

 
def G (D D' : LSCMetric) (r κ C : Set.Ioi (0 : ℝ)) : Prop :=
  ∃ z w : ℂ, z ∈ Metric.closedBall (0 : ℂ) r ∧
    w ∈ Metric.closedBall (0 : ℂ) r ∧ RatioPair D z w ∧
    ENNReal.ofReal C * D (z, w) ≤
      setDist D' (Metric.ball z (κ * r)) (Metric.ball w (κ * r))

 
def Gtilde (D D' : LSCMetric) (r κ C : Set.Ioi (0 : ℝ)) : Prop :=
  ∃ z w : ℂ, z ∈ Metric.closedBall (0 : ℂ) r ∧
    w ∈ Metric.closedBall (0 : ℂ) r ∧ RatioPair D' z w ∧
    D' (z, w) ≤
      ENNReal.ofReal C * setDist D (Metric.ball z (κ * r)) (Metric.ball w (κ * r))

 
theorem Gtilde_iff_swap (D D' : LSCMetric) (r κ C : Set.Ioi (0 : ℝ)) :
    Gtilde D D' r κ C ↔
      G D' D r κ ⟨(C : ℝ)⁻¹, by
        have hC : 0 < (C : ℝ) := by simpa only [Set.mem_Ioi] using C.property
        exact inv_pos.mpr hC⟩ := by
  have hCp : 0 < ENNReal.ofReal (C : ℝ) := ENNReal.ofReal_pos.mpr C.property
  have hCt : ENNReal.ofReal (C : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have key (x y : ℝ≥0∞) :
      x ≤ ENNReal.ofReal (C : ℝ) * y ↔
        ENNReal.ofReal ((C : ℝ)⁻¹) * x ≤ y := by
    rw [ENNReal.ofReal_inv_of_pos C.property]
    exact (ENNReal.inv_mul_le_iff hCp.ne' hCt).symm
  constructor
  · rintro ⟨z, w, hz, hw, hp, hc⟩
    exact ⟨z, w, hz, hw, hp, (key _ _).1 hc⟩
  · rintro ⟨z, w, hz, hw, hp, hc⟩
    exact ⟨z, w, hz, hw, hp, (key _ _).2 hc⟩

 

theorem measurableSet_G_fixedWitness (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D')
    (z w : ℂ) (s C : ℝ) :
    MeasurableSet {g : DistC | RatioPair (D g) z w ∧
      ENNReal.ofReal C * D g (z, w) ≤
        setDist (D' g) (Metric.ball z s) (Metric.ball w s)} := by
  have hp := measurableSet_ratioPair_fixed D hD z w
  have hm : Measurable fun g : DistC => D g (z, w) :=
    (LSCMetric.measurable_apply (z, w)).comp hD
  have hs : Measurable fun g : DistC =>
      setDist (D' g) (Metric.ball z s) (Metric.ball w s) :=
    (measurable_setDist_open _ _ Metric.isOpen_ball Metric.isOpen_ball).comp hD'
  exact hp.inter (measurableSet_le (measurable_const.mul hm) hs)

 
theorem measurableSet_Gtilde_fixedWitness (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D')
    (z w : ℂ) (s C : ℝ) :
    MeasurableSet {g : DistC | RatioPair (D' g) z w ∧
      D' g (z, w) ≤ ENNReal.ofReal C *
        setDist (D g) (Metric.ball z s) (Metric.ball w s)} := by
  have hp := measurableSet_ratioPair_fixed D' hD' z w
  have hm : Measurable fun g : DistC => D' g (z, w) :=
    (LSCMetric.measurable_apply (z, w)).comp hD'
  have hs : Measurable fun g : DistC =>
      setDist (D g) (Metric.ball z s) (Metric.ball w s) :=
    (measurable_setDist_open _ _ Metric.isOpen_ball Metric.isOpen_ball).comp hD
  exact hp.inter (measurableSet_le hm (measurable_const.mul hs))

 
theorem G_witness_ne (D D' : LSCMetric) (r κ C : Set.Ioi (0 : ℝ))
    (hG : G D D' r κ C) :
    ∃ z w : ℂ, z ≠ w ∧ z ∈ Metric.closedBall (0 : ℂ) r ∧
      w ∈ Metric.closedBall (0 : ℂ) r := by
  obtain ⟨z, w, hz, hw, hp, _⟩ := hG
  exact ⟨z, w, hp.1, hz, hw⟩

 
def Geodesic (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) (u v : ℂ) : Prop :=
  D.IsCurve P a b ∧ P a = u ∧ P b = v ∧
    D.len P a b = D (u, v) ∧ D (u, v) < ⊤

 
def EndpointLoop (D : LSCMetric) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ)) (u v x : ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ (1 - (a : ℝ)) ^ 2 →
    ∃ A : EuclideanAnnulus,
      A.center = x ∧ A.innerRadius = δ * r ∧
      A.outerRadius = Real.sqrt δ * r ∧
      max (setDist D {x} (Metric.sphere x (δ * r))) (aroundDist D A) ≤
        ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v)

 
def H (D D' : LSCMetric) (ξ Q : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ)) (hCircle : ℝ) : Prop :=
  ∃ u v : ℂ, u ∈ Metric.sphere (0 : ℂ) (a * r) ∧
    v ∈ Metric.sphere (0 : ℂ) r ∧
    ¬ Singular D u ∧ ¬ Singular D v ∧
    ENNReal.ofReal C * D (u, v) ≤ D' (u, v) ∧
    ∃ (P : ℝ → ℂ) (s t : ℝ),
      Geodesic D P s t u v ∧
      (∀ q ∈ Icc s t, q ∈ P ⁻¹' (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (a * r))) ∧
      Metric.diam (P '' Icc s t) ≤ r / 100 ∧
      D (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * hCircle)) ∧
      EndpointLoop D r a θ u v u ∧ EndpointLoop D r a θ u v v

 
def Htilde (D D' : LSCMetric) (ξ Q : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ)) (hCircle : ℝ) : Prop :=
  ∃ u v : ℂ, u ∈ Metric.sphere (0 : ℂ) (a * r) ∧
    v ∈ Metric.sphere (0 : ℂ) r ∧
    ¬ Singular D' u ∧ ¬ Singular D' v ∧
    D' (u, v) ≤ ENNReal.ofReal C * D (u, v) ∧
    ∃ (P : ℝ → ℂ) (s t : ℝ),
      Geodesic D' P s t u v ∧
      (∀ q ∈ Icc s t, q ∈ P ⁻¹' (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) (a * r))) ∧
      Metric.diam (P '' Icc s t) ≤ r / 100 ∧
      D' (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * hCircle)) ∧
      EndpointLoop D' r a θ u v u ∧ EndpointLoop D' r a θ u v v

 
def HEvent (D D' : DistC → LSCMetric) (ξ Q : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ)) (g : DistC) : Prop :=
  ∃ hCircle : ℝ,
    IsCircleAverage g r 0 hCircle ∧
    H (D g) (D' g) ξ Q r a C θ hCircle

 
def HtildeEvent (D D' : DistC → LSCMetric) (ξ Q : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ)) (g : DistC) : Prop :=
  ∃ hCircle : ℝ,
    IsCircleAverage g r 0 hCircle ∧
    Htilde (D g) (D' g) ξ Q r a C θ hCircle

def GEvent (D D' : DistC → LSCMetric) (r κ C : Set.Ioi (0 : ℝ)) : Set DistC :=
  {g | G (D g) (D' g) r κ C}

def GtildeEvent (D D' : DistC → LSCMetric) (r κ C : Set.Ioi (0 : ℝ)) : Set DistC :=
  {g | Gtilde (D g) (D' g) r κ C}


end SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios
