import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeoCode
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.LoopFit.LoopFit




 











set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

 
theorem measurable_pointCost (R : ℝ) :
    Measurable fun p : LSCMetric × ℂ × ℝ≥0∞ => TwoScale.S36Events.pointSphereDist p.1 p.2.1 R := by
  have h : Measurable fun p : LSCMetric × ℂ × ℝ≥0∞ =>
      ((p.1, (p.2.1, R)) : LSCMetric × (ℂ × ℝ)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const)
  
  have h2 := TwoScale.S36Events.pointSphereDist_joint_measurable.comp h
  simpa only [Function.comp_def] using h2

 
theorem measurable_loopBound (c : ℝ) :
    Measurable fun p : LSCMetric × ℂ × ℝ≥0∞ => ENNReal.ofReal c * p.2.2 :=
  measurable_const.mul (measurable_snd.comp measurable_snd)

 
def PointLoopRat (r θ δ₀ : ℝ) (q : ℚ) : Set (LSCMetric × ℂ × ℝ≥0∞) :=
  {p | 0 < (q : ℝ) → (q : ℝ) ≤ δ₀ →
    TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
      ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2}

theorem measurableSet_pointLoopRat (r θ δ₀ : ℝ) (q : ℚ) :
    MeasurableSet (PointLoopRat r θ δ₀ q) := by
  by_cases h : 0 < (q : ℝ) ∧ (q : ℝ) ≤ δ₀
  · have heq : PointLoopRat r θ δ₀ q =
        {p : LSCMetric × ℂ × ℝ≥0∞ | TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
          ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2} := by
      ext p
      exact ⟨fun hp => hp h.1 h.2, fun hp _ _ => hp⟩
    rw [heq]
    exact measurableSet_le (measurable_pointCost _) (measurable_loopBound _)
  · have heq : PointLoopRat r θ δ₀ q = univ := by
      ext p
      refine ⟨fun _ => mem_univ p, fun _ h1 h2 => absurd ⟨h1, h2⟩ h⟩
    rw [heq]
    exact MeasurableSet.univ

 
def PointLoopSet (r θ δ₀ : ℝ) : Set (LSCMetric × ℂ × ℝ≥0∞) :=
  {p | p.2.2 ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    TwoScale.S36Events.pointSphereDist p.1 p.2.1 (δ * r) ≤ ENNReal.ofReal (δ ^ θ) * p.2.2}

 
theorem measurableSet_pointLoopSet (r : ℝ) {θ : ℝ} (hθ : 0 < θ) (δ₀ : ℝ) :
    MeasurableSet (PointLoopSet r θ δ₀) := by
  have hfin : MeasurableSet {p : LSCMetric × ℂ × ℝ≥0∞ | p.2.2 ≠ ⊤} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton (⊤ : ℝ≥0∞)).compl
  have hrat : MeasurableSet (⋂ q : ℚ, PointLoopRat r θ δ₀ q) :=
    MeasurableSet.iInter fun q => measurableSet_pointLoopRat r θ δ₀ q
  have heq : PointLoopSet r θ δ₀ =
      {p : LSCMetric × ℂ × ℝ≥0∞ | p.2.2 ≠ ⊤} ∩ ⋂ q : ℚ, PointLoopRat r θ δ₀ q := by
    ext p
    constructor
    · rintro ⟨hp, hall⟩
      refine ⟨hp, mem_iInter.mpr fun q => ?_⟩
      exact (TwoScale.S36Events.point_loop_forall_iff_rat p.1 p.2.1 (r := r) (δ₀ := δ₀) hθ hp).mp hall q
    · rintro ⟨hp, hall⟩
      refine ⟨hp, ?_⟩
      exact (TwoScale.S36Events.point_loop_forall_iff_rat p.1 p.2.1 (r := r) (δ₀ := δ₀) hθ hp).mpr
        fun q => mem_iInter.mp hall q
  rw [heq]
  exact hfin.inter hrat

 
def AroundLoopSet (r θ δ₀ : ℝ) : Set (LSCMetric × ℂ × ℝ≥0∞) :=
  {p | p.2.2 ≠ ⊤ ∧ ∀ δ ∈ Ioc 0 δ₀, TwoScale.Consolidated.loopF p.1 p.2.1 r δ ≤ ENNReal.ofReal (δ ^ θ) * p.2.2}

 
def LoopSet (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) :
    Set (LSCMetric × ℂ × ℝ≥0∞) :=
  PointLoopSet r θ ((1 - (a : ℝ)) ^ 2) ∩ AroundLoopSet r θ ((1 - (a : ℝ)) ^ 2)

theorem measurableSet_loopSet (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) :
    MeasurableSet (LoopSet r a θ) :=
  (measurableSet_pointLoopSet r θ.2 _).inter
    (TwoScale.LoopFit.measurableSet_endpointLoop_around r a θ)

 
theorem setDist_singleton_eq_pointSphereDist (D : LSCMetric) (x : ℂ) (R : ℝ) :
    OptimalConstants.Ratios.setDist D {x} (Metric.sphere x R) = TwoScale.S36Events.pointSphereDist D x R := by
  rw [TwoScale.S36Events.pointSphereDist, TwoScale.S36Events.spherePairInf_zero_eq]
  simp only [OptimalConstants.Ratios.setDist, iInf_singleton]

 
theorem endpointLoop_iff_mem_loopSet (D : LSCMetric) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (θ : Ioi (0 : ℝ)) (u v x : ℂ) (hfin : D (u, v) ≠ ⊤) :
    OptimalConstants.Ratios.EndpointLoop D r a θ u v x ↔ (D, (x, D (u, v))) ∈ LoopSet r a θ := by
  rw [TwoScale.LoopFit.endpointLoop_iff_loopF]
  constructor
  · intro h
    refine ⟨⟨hfin, fun δ hδ hδ₀ => ?_⟩, ⟨hfin, fun δ hδ => (h δ hδ).2⟩⟩
    rw [← setDist_singleton_eq_pointSphereDist]
    exact (h δ ⟨hδ, hδ₀⟩).1
  · rintro ⟨⟨_, hpt⟩, ⟨_, har⟩⟩ δ hδ
    refine ⟨?_, har δ hδ⟩
    rw [setDist_singleton_eq_pointSphereDist]
    exact hpt δ hδ.1 hδ.2

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
