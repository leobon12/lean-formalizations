import SupercriticalConformalCovariance.Small.ConfinedLSC
import SupercriticalConformalCovariance.Small.Confinement

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness

/-- The point cost in (8) is unchanged by diagonal-corrected confinement. -/
theorem pointSphereDist_eq_conf
    (D : LSCMetric) (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (c : ℂ) (R : ℝ) (u : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall u ρ ⊆ closedBall c R) :
    TwoScale.S36Events.pointSphereDist (conf D c R) u ρ =
      TwoScale.S36Events.pointSphereDist D u ρ := by
  rw [pointSphereDist_eq_confined_boundaryBallInf D hL hC c R u hρ hsub]
  rw [← TwoScale.S36.setDist_singleton_eq_pointSphereDist]
  simp only [OptimalConstants.Ratios.setDist, iInf_singleton]
  refine iInf_congr fun y => iInf_congr fun hy => ?_
  have hu : u ∈ closedBall c R := hsub (mem_closedBall_self hρ.le)
  have hy' : y ∈ closedBall c R := hsub (sphere_subset_closedBall hy)
  rw [conf_eq_extInternal_on D c R hu hy', SupercriticalConformalCovariance.Tangent.closedBallPathInf_eq_extInternal]


theorem conf_len_eq_original_of_trace (D : LSCMetric) (c : ℂ) (R : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hK : ∀ t ∈ Icc a b, P t ∈ closedBall c R) :
    (conf D c R).len P a b = D.len P a b := by
  let K := closedBall c R
  have hbase := LQGMetric.MetricGeometry.curveLength_eq_iSup_internalEDist
    (Y := D.pt '' K) hP.2 (fun t ht => ⟨P t, hK t ht, rfl⟩)
  change LQGMetric.MetricGeometry.curveLength ((conf D c R).pt ∘ P) a b =
    LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b
  rw [hbase]
  unfold LQGMetric.MetricGeometry.curveLength eVariationOn
  refine iSup_congr fun q => Finset.sum_congr rfl fun i _ => ?_
  have h1 := hK (q.2.1 (i+1)) (q.2.2.2 (i+1))
  have h0 := hK (q.2.1 i) (q.2.2.2 i)
  change conf D c R (P (q.2.1 (i+1)), P (q.2.1 i)) =
    LQGMetric.MetricGeometry.internalEDist (D.pt '' K)
      (D.pt (P (q.2.1 (i+1)))) (D.pt (P (q.2.1 i)))
  rw [conf_apply, confKernel_eq_intrinsic D c R h1 h0]
  exact D.internal_eq_internalEDist K (⟨P (q.2.1 (i+1)), h1⟩,
    ⟨P (q.2.1 i), h0⟩)

theorem conf_isCurve_of_lipschitz_trace (D : LSCMetric) (c : ℂ) (R : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hK : ∀ t ∈ Icc a b, P t ∈ closedBall c R)
    {C : NNReal} (hLip : LipschitzOnWith C (D.pt ∘ P) (Icc a b)) :
    (conf D c R).IsCurve P a b := by
  let K := closedBall c R
  let Y : Set D.Space := D.pt '' K
  -- Apply internal Lipschitz continuity on the original real interval.
  let Q' : ℝ → Y := fun t =>
    ⟨D.pt (P (max a (min t b))),
      ⟨P (max a (min t b)), hK _ ⟨le_max_left _ _,
        max_le hab (min_le_right _ _)⟩, rfl⟩⟩
  have hQeq : ∀ t ∈ Icc a b, (Q' t : D.Space) = D.pt (P t) := by
    intro t ht
    simp only [Q', max_eq_right ht.1, min_eq_left ht.2]
  have hQLip : LipschitzOnWith C (fun t => (Q' t : D.Space)) (Icc a b) := by
    intro s hs t ht
    change edist (Q' s : D.Space) (Q' t : D.Space) ≤ _
    rw [hQeq s hs, hQeq t ht]
    exact hLip hs ht
  have hi := SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.lipschitzOnWith_internalSpace
    (X := D.Space) Y Q' hQLip
  refine ⟨hab, ?_⟩
  have hc : LipschitzOnWith C ((conf D c R).pt ∘ P) (Icc a b) := by
    intro s hs t ht
    change conf D c R (P s, P t) ≤ (C : ℝ≥0∞) * edist s t
    rw [conf_apply, confKernel_eq_intrinsic D c R (hK s hs) (hK t ht),
      LSCMetric.internal_eq_internalEDist]
    have hhi : LQGMetric.MetricGeometry.internalEDist Y (Q' s : D.Space) (Q' t : D.Space) ≤
        (C : ℝ≥0∞) * edist s t := hi hs ht
    rw [hQeq s hs, hQeq t ht] at hhi
    exact hhi
  exact hc.continuousOn


/-- Preserve the entire trace when transferring a finite source curve to confinement. -/
theorem exists_conf_curve_same_trace_len (D : LSCMetric) (c : ℂ) (R : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hfin : D.len P a b ≠ ⊤)
    (hK : ∀ t ∈ Icc a b, P t ∈ closedBall c R) :
    ∃ (Q : ℝ → ℂ) (L : ℝ),
      (conf D c R).IsCurve Q 0 L ∧ Q 0 = P a ∧ Q L = P b ∧
      Q '' Icc 0 L = P '' Icc a b ∧
      (conf D c R).len Q 0 L = D.len P a b := by
  let f : ℝ → D.Space := D.pt ∘ P
  let L : ℝ := (D.len P a b).toReal
  let Q : ℝ → ℂ := fun t => ((LQGMetric.MetricGeometry.lengthParam f a b t : D.Space) : ℂ)
  have hf : ContinuousOn f (Icc a b) := hP.2
  have hL : L = (LQGMetric.MetricGeometry.curveLength f a b).toReal := rfl
  have hDQ : D.pt ∘ Q = LQGMetric.MetricGeometry.lengthParam f a b := by
    funext t
    rfl
  have hrep (t : ℝ) (ht : t ∈ Icc a b) :
      Q (variationOnFromTo f (Icc a b) a t) = P t := by
    have h := LQGMetric.MetricGeometry.lengthParam_variationOnFromTo hfin ht
    exact congrArg (fun v : D.Space => (v : ℂ)) h
  have hQ0 : Q 0 = P a := by
    have h := hrep a ⟨le_rfl,hP.1⟩
    rw [variationOnFromTo.self] at h
    exact h
  have hQL : Q L = P b := by
    have h := hrep b ⟨hP.1,le_rfl⟩
    rw [variationOnFromTo.eq_of_le _ _ hP.1, Set.inter_self] at h
    exact h
  have himg : Q '' Icc 0 L = P '' Icc a b := by
    have hs := LQGMetric.MetricGeometry.variationOnFromTo_image_Icc hP.1 hf hfin
    ext y
    constructor
    · rintro ⟨s,hs',rfl⟩
      have hs'' : s ∈ Icc 0 (LQGMetric.MetricGeometry.curveLength f a b).toReal := by
        simpa only [hL] using hs'
      rw [← hs] at hs''
      obtain ⟨t,ht,rfl⟩ := hs''
      exact ⟨t,ht,(hrep t ht).symm⟩
    · rintro ⟨t,ht,rfl⟩
      have hs' : variationOnFromTo f (Icc a b) a t ∈ Icc 0 L := by
        rw [hL, ← hs]
        exact ⟨t,ht,rfl⟩
      exact ⟨_,hs',hrep t ht⟩
  have hQK : ∀ t ∈ Icc 0 L, Q t ∈ closedBall c R := by
    intro t ht
    have hm : Q t ∈ P '' Icc a b := by
      rw [← himg]
      exact ⟨t,ht,rfl⟩
    obtain ⟨s,hs,heq⟩ := hm
    exact heq ▸ hK s hs
  have hQLip : LipschitzOnWith (1 : NNReal) (D.pt ∘ Q) (Icc 0 L) := by
    rw [hDQ, hL]
    exact LQGMetric.MetricGeometry.lipschitzOnWith_lengthParam hP.1 hf hfin
  have hQc : (conf D c R).IsCurve Q 0 L :=
    conf_isCurve_of_lipschitz_trace D c R Q 0 L ENNReal.toReal_nonneg hQK hQLip
  have hQD : D.IsCurve Q 0 L :=
    ⟨ENNReal.toReal_nonneg, hQLip.continuousOn⟩
  refine ⟨Q,L,hQc,hQ0,hQL,himg,?_⟩
  rw [conf_len_eq_original_of_trace D c R Q 0 L hQD hQK]
  change LQGMetric.MetricGeometry.curveLength (D.pt ∘ Q) 0 L =
    LQGMetric.MetricGeometry.curveLength f a b
  rw [hDQ, hL]
  exact LQGMetric.MetricGeometry.curveLength_lengthParam hP.1 hf hfin

/-- A loop cost inside the disk is exactly preserved by confinement. -/
theorem aroundDist_eq_conf (D : LSCMetric) (c : ℂ) (R : ℝ)
    (A : EuclideanAnnulus) (hA : A.toSet ⊆ closedBall c R) :
    aroundDist (conf D c R) A = aroundDist D A := by
  apply le_antisymm
  · unfold aroundDist
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hPA => le_iInf fun hSep => ?_
    by_cases hfin : D.len P a b = ⊤
    · rw [hfin]; exact le_top
    obtain ⟨Q,L,hQc,_,_,htrace,hlen⟩ :=
      exists_conf_curve_same_trace_len D c R P a b hP hfin
        (fun t ht => hA (hPA t ht))
    have hQA : ∀ t ∈ Icc 0 L, Q t ∈ A.toSet := by
      intro t ht
      have hm : Q t ∈ P '' Icc a b := by
        rw [← htrace]
        exact ⟨t,ht,rfl⟩
      obtain ⟨s,hs,heq⟩ := hm
      exact heq ▸ hPA s hs
    have hSep' : Disconnects (Q '' Icc 0 L) A.innerBoundary A.outerBoundary := by
      rw [htrace]
      exact hSep
    have hcost : aroundDist (conf D c R) A ≤ (conf D c R).len Q 0 L := by
      unfold aroundDist
      exact iInf_le_of_le Q <| iInf_le_of_le (0 : ℝ) <| iInf_le_of_le L <|
        iInf_le_of_le hQc <| iInf_le_of_le hQA <|
        iInf_le_of_le hSep' le_rfl
    exact hcost.trans_eq hlen
  · unfold aroundDist
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hPA => le_iInf fun hSep => ?_
    have hPc := conf_curve_original_curve D c R P a b hP
    have hcost : aroundDist D A ≤ D.len P a b := by
      unfold aroundDist
      exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
        iInf_le_of_le hPc <| iInf_le_of_le hPA <|
        iInf_le_of_le hSep le_rfl
    exact hcost.trans (original_len_le_conf_len D c R P a b)
