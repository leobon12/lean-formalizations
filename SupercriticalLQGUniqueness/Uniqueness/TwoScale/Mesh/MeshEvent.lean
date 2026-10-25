import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh.MeshGeometry
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioMesh




 





set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh

open LQGMetric (DistC)

 

theorem crossingAt_toSet_eq_annulus (z : ℂ) (r : Ioi (0 : ℝ)) :
    (BiLipschitz.OneScale.crossingAt z r).toSet =
      (LQGMetric.Blueprint.annulus z (r : ℝ) (2 * (r : ℝ)) : Set ℂ) := by
  ext w
  have hr : (r : ℝ) ≠ 0 := r.2.ne'
  simp only [BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape, Positivity.Witnesses.annulusTranslate,
    EuclideanAnnulus.dilate, EuclideanAnnulus.toSet, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, smul_zero,
    zero_add, mul_one]
  rw [show (r : ℝ) * 2 = 2 * (r : ℝ) by ring]
  change w ∈ Metric.ball z (2 * (r : ℝ)) \
      closure (Metric.ball z (r : ℝ)) ↔
        (r : ℝ) < ‖w - z‖ ∧ ‖w - z‖ < 2 * (r : ℝ)
  rw [closure_ball z hr]
  simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall,
    not_le, dist_eq_norm]
  tauto

 
theorem scaleMesh_ratio_bad_tail
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (a : ℝ) (ha : 0 < a) :
    ∃ p c M : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (ε R : ℝ), 0 < ε → 0 < R → ∀ (z₀ : ℂ)
          (base : Ioi (0 : ℝ)) (N : ℕ),
          P {ω | ∃ z ∈ scaleMesh ε R z₀,
            (LQGMetric.Blueprint.countOcc
              (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
                (TwoScale.Ratio.ratioRadius base k)
                (ENNReal.ofReal M * ENNReal.ofReal M)}) N ω : ℝ) <
                  (1 / 2 : ℝ) * N} ≤
            (((2 * ⌈12 / ε⌉₊ + 1) ^ 2 : ℕ) : ℝ≥0∞) *
              ENNReal.ofReal (c * Real.exp (-a * N)) := by
  obtain ⟨p, c, M, hp0, hp1, hc, hM, htail⟩ :=
    TwoScale.Ratio.ratio_finite_mesh_union ξ Q D hD a ha
  refine ⟨p, c, M, hp0, hp1, hc, hM, ?_⟩
  intro Ω _ P _ h hh ε R hε hR z₀ base N
  calc
    P {ω | ∃ z ∈ scaleMesh ε R z₀,
      (LQGMetric.Blueprint.countOcc
        (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
          (TwoScale.Ratio.ratioRadius base k)
          (ENNReal.ofReal M * ENNReal.ofReal M)}) N ω : ℝ) <
            (1 / 2 : ℝ) * N} ≤
      ((scaleMesh ε R z₀).card : ℝ≥0∞) *
        ENNReal.ofReal (c * Real.exp (-a * N)) :=
        htail P h hh (scaleMesh ε R z₀) base N
    _ ≤ (((2 * ⌈12 / ε⌉₊ + 1) ^ 2 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (c * Real.exp (-a * N)) := by
          gcongr
          exact scaleMesh_card_le hε hR z₀

 

theorem exists_near_good_scaleMesh
    {Ω : Type} (h : Ω → DistC) (D : DistC → LSCMetric)
    (M : ℝ) (base : Ioi (0 : ℝ)) (N : ℕ)
    {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (z₀ : ℂ) (ω : Ω)
    (hgood : ¬ ∃ z ∈ scaleMesh ε R z₀,
      (LQGMetric.Blueprint.countOcc
        (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
          (TwoScale.Ratio.ratioRadius base k)
          (ENNReal.ofReal M * ENNReal.ofReal M)}) N ω : ℝ) <
            (1 / 2 : ℝ) * N)
    (x : ℂ) (hx : x ∈ Metric.ball z₀ (2 * R)) :
    ∃ z ∈ scaleMesh ε R z₀, dist x z < ε * R / 2 ∧
      (1 / 2 : ℝ) * N ≤
        (LQGMetric.Blueprint.countOcc
          (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
            (TwoScale.Ratio.ratioRadius base k)
            (ENNReal.ofReal M * ENNReal.ofReal M)}) N ω : ℝ) := by
  obtain ⟨z, hz, hnear⟩ := exists_near_scaleMesh hε hε1 hR z₀ x hx
  refine ⟨z, hz, hnear, ?_⟩
  exact le_of_not_gt (fun hbad => hgood ⟨z, hz, hbad⟩)

 

theorem exists_good_mesh_annulus_at_hit
    {Ω : Type} (h : Ω → DistC) (D : DistC → LSCMetric)
    (M : ℝ) (base : Ioi (0 : ℝ)) (N : ℕ)
    {ε R r T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hrlo : 2 * (ε * R) ≤ r) (hrhi : 2 * r + ε * R / 2 ≤ T)
    (z₀ : ℂ) (ω : Ω)
    (hgood : ¬ ∃ z ∈ scaleMesh ε R z₀,
      (LQGMetric.Blueprint.countOcc
        (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
          (TwoScale.Ratio.ratioRadius base k)
          (ENNReal.ofReal M * ENNReal.ofReal M)}) N ω : ℝ) <
            (1 / 2 : ℝ) * N)
    (x : ℂ) (hx : x ∈ Metric.ball z₀ (2 * R)) :
    ∃ z ∈ scaleMesh ε R z₀, dist x z < ε * R / 2 ∧
      (BiLipschitz.OneScale.crossingAt z ⟨r, lt_of_lt_of_le (by positivity) hrlo⟩).toSet ⊆
        (LQGMetric.Blueprint.annulus x (ε * R) T : Set ℂ) ∧
      (1 / 2 : ℝ) * N ≤
        (LQGMetric.Blueprint.countOcc
          (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
            (TwoScale.Ratio.ratioRadius base k)
            (ENNReal.ofReal M * ENNReal.ofReal M)}) N ω : ℝ) := by
  obtain ⟨z, hz, hnear, hcount⟩ :=
    exists_near_good_scaleMesh h D M base N hε hε1 hR z₀ ω hgood x hx
  refine ⟨z, hz, hnear, ?_, hcount⟩
  rw [crossingAt_toSet_eq_annulus]
  exact mesh_annulus_subset hnear hrlo hrhi

 

theorem scaleMesh_ratio_bad_tail_real
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (a : ℝ) (ha : 0 < a) :
    ∃ p c M : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (ε R : ℝ), 0 < ε → ε ≤ 1 → 0 < R → ∀ (z₀ : ℂ)
          (base : Ioi (0 : ℝ)) (N : ℕ),
          P {ω | ∃ z ∈ scaleMesh ε R z₀,
            (LQGMetric.Blueprint.countOcc
              (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
                (TwoScale.Ratio.ratioRadius base k)
                (ENNReal.ofReal M * ENNReal.ofReal M)}) N ω : ℝ) <
                  (1 / 2 : ℝ) * N} ≤
            ENNReal.ofReal ((27 / ε) ^ 2 * (c * Real.exp (-a * N))) := by
  obtain ⟨p, c, M, hp0, hp1, hc, hM, htail⟩ :=
    TwoScale.Ratio.ratio_finite_mesh_union ξ Q D hD a ha
  refine ⟨p, c, M, hp0, hp1, hc, hM, ?_⟩
  intro Ω _ P _ h hh ε R hε hε1 hR z₀ base N
  have hcard := scaleMesh_card_real_le hε hε1 hR z₀
  have hfac : 0 ≤ (27 / ε) ^ 2 := sq_nonneg _
  have hcast : ((scaleMesh ε R z₀).card : ℝ≥0∞) ≤
      ENNReal.ofReal ((27 / ε) ^ 2) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  calc
    P {ω | ∃ z ∈ scaleMesh ε R z₀,
      (LQGMetric.Blueprint.countOcc
        (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
          (TwoScale.Ratio.ratioRadius base k)
          (ENNReal.ofReal M * ENNReal.ofReal M)}) N ω : ℝ) <
            (1 / 2 : ℝ) * N} ≤
      ((scaleMesh ε R z₀).card : ℝ≥0∞) *
        ENNReal.ofReal (c * Real.exp (-a * N)) :=
        htail P h hh (scaleMesh ε R z₀) base N
    _ ≤ ENNReal.ofReal ((27 / ε) ^ 2) *
        ENNReal.ofReal (c * Real.exp (-a * N)) := by
          gcongr
    _ = ENNReal.ofReal ((27 / ε) ^ 2 * (c * Real.exp (-a * N))) :=
      (ENNReal.ofReal_mul hfac).symm


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh
