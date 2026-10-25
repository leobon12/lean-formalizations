import SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.SelectedMetric
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.ScaleNumerics
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh.MeshGeometry




 






set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

 

theorem aroundDist_le_of_nested
    (D : LSCMetric) (big small : EuclideanAnnulus)
    (hset : small.toSet ⊆ big.toSet)
    (hin : big.innerBoundary ⊆ closedBall small.center small.innerRadius)
    (hout : big.outerBoundary ⊆ (ball small.center small.outerRadius)ᶜ) :
    aroundDist D big ≤ aroundDist D small := by
  unfold aroundDist
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun hPs => le_iInf fun hsep => ?_
  have hclosed : IsClosed (P '' Icc a b) := hP.isClosed_image
  have hpath : LQGMetric.Disconnects (P '' Icc a b)
      small.innerBoundary small.outerBoundary :=
    (disconnects_iff_lqgMetric_disconnects hclosed).mp hsep
  have hpath' : LQGMetric.Disconnects (P '' Icc a b)
      big.innerBoundary big.outerBoundary :=
    (LQGMetric.Disconnects.closedBall_compl_ball small.2.2.le hpath).mono
      (Subset.refl _) hin hout
  have hsep' : Disconnects (P '' Icc a b)
      big.innerBoundary big.outerBoundary :=
    (disconnects_iff_lqgMetric_disconnects hclosed).mpr hpath'
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le (fun t ht => hset (hPs t ht)) <|
      iInf_le_of_le hsep' le_rfl

 


theorem acrossDist_le_of_nested
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (big small : EuclideanAnnulus)
    (hin : big.innerBoundary ⊆ closedBall small.center small.innerRadius)
    (hout : big.outerBoundary ⊆ (ball small.center small.outerRadius)ᶜ) :
    acrossDist D small ≤ acrossDist D big := by
  unfold acrossDist
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  have hxr : ‖x - small.center‖ ≤ small.innerRadius := by
    simpa only [mem_closedBall, dist_eq_norm] using hin hx
  have hyr : small.outerRadius ≤ ‖y - small.center‖ := by
    simpa only [mem_compl_iff, mem_ball, not_lt, dist_eq_norm] using hout hy
  change acrossDist D small ≤ D (x, y)
  rw [BiLipschitz.Barrier.acrossDist_eq_iInf_internal D hB hL small (Y := Set.univ)
    (subset_univ _)]
  exact BiLipschitz.Barrier.iInf_internal_le D hB hL small.2.2.le (Y := Set.univ)
    (subset_univ _) hxr hyr

 

theorem nested_annulus_geometry
    (big small : EuclideanAnnulus)
    (hin : big.innerRadius + dist big.center small.center ≤ small.innerRadius)
    (hout : small.outerRadius + dist big.center small.center ≤ big.outerRadius) :
    small.toSet ⊆ big.toSet ∧
      big.innerBoundary ⊆ closedBall small.center small.innerRadius ∧
      big.outerBoundary ⊆ (ball small.center small.outerRadius)ᶜ := by
  have hset : small.toSet ⊆ big.toSet := by
    rw [small.toSet_eq, big.toSet_eq]
    intro w hw
    have htri₁ := dist_triangle w big.center small.center
    have htri₂ := dist_triangle w small.center big.center
    rw [dist_comm small.center big.center] at htri₂
    constructor <;> linarith [hw.1, hw.2]
  have hbin : big.innerBoundary ⊆ closedBall small.center small.innerRadius := by
    intro w hw
    have hw' : dist w big.center = big.innerRadius := by
      simpa only [EuclideanAnnulus.innerBoundary, mem_sphere] using hw
    have htri := dist_triangle w big.center small.center
    rw [mem_closedBall]
    linarith
  have hbout : big.outerBoundary ⊆ (ball small.center small.outerRadius)ᶜ := by
    intro w hw
    have hw' : dist w big.center = big.outerRadius := by
      simpa only [EuclideanAnnulus.outerBoundary, mem_sphere] using hw
    have htri := dist_triangle w small.center big.center
    rw [dist_comm small.center big.center] at htri
    rw [mem_compl_iff, mem_ball, not_lt]
    linarith
  exact ⟨hset, hbin, hbout⟩

 
theorem shifted_annulus_comparisons
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (big small : EuclideanAnnulus)
    (hin : big.innerRadius + dist big.center small.center ≤ small.innerRadius)
    (hout : small.outerRadius + dist big.center small.center ≤ big.outerRadius) :
    aroundDist D big ≤ aroundDist D small ∧
      acrossDist D small ≤ acrossDist D big := by
  obtain ⟨hset, hbin, hbout⟩ := nested_annulus_geometry big small hin hout
  exact ⟨aroundDist_le_of_nested D big small hset hbin hbout,
    acrossDist_le_of_nested D hB hL big small hbin hbout⟩




theorem crossingAt_center (z : ℂ) (r : Ioi (0 : ℝ)) :
    (BiLipschitz.OneScale.crossingAt z r).center = z := by
  simp only [BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape, Positivity.Witnesses.annulusTranslate,
    EuclideanAnnulus.dilate, EuclideanAnnulus.center, smul_zero, zero_add]

theorem crossingAt_inner (z : ℂ) (r : Ioi (0 : ℝ)) :
    (BiLipschitz.OneScale.crossingAt z r).innerRadius = (r : ℝ) := by
  simp only [BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape, Positivity.Witnesses.annulusTranslate,
    EuclideanAnnulus.dilate, EuclideanAnnulus.innerRadius, mul_one]

theorem crossingAt_outer (z : ℂ) (r : Ioi (0 : ℝ)) :
    (BiLipschitz.OneScale.crossingAt z r).outerRadius = 2 * (r : ℝ) := by
  simp only [BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape, Positivity.Witnesses.annulusTranslate,
    EuclideanAnnulus.dilate, EuclideanAnnulus.outerRadius, mul_comm]

 

theorem ratio_family_shift_margins
    (A : EuclideanAnnulus) (z : ℂ) (base : Ioi (0 : ℝ))
    (N : ℕ) (m : ℝ)
    (hnear : dist A.center z < m)
    (hN : A.innerRadius + m ≤ (TwoScale.Ratio.ratioRadius base N : ℝ))
    (h1 : 2 * (TwoScale.Ratio.ratioRadius base 1 : ℝ) + m ≤ A.outerRadius)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 N) :
    A.innerRadius + dist A.center z ≤
        (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)).innerRadius ∧
      (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)).outerRadius +
        dist A.center z ≤ A.outerRadius := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjN : j ≤ N := (Finset.mem_Icc.mp hj).2
  have hmono := TwoScale.OrderedCrossings.ratioRadius_antitone base
  have hrN : (TwoScale.Ratio.ratioRadius base N : ℝ) ≤
      (TwoScale.Ratio.ratioRadius base j : ℝ) := hmono hjN
  have hr1 : (TwoScale.Ratio.ratioRadius base j : ℝ) ≤
      (TwoScale.Ratio.ratioRadius base 1 : ℝ) := hmono hj1
  rw [crossingAt_inner, crossingAt_outer]
  constructor <;> linarith

 

theorem ratio_family_shifted_comparisons
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (A : EuclideanAnnulus) (z : ℂ) (base : Ioi (0 : ℝ))
    (N : ℕ) (m : ℝ)
    (hnear : dist A.center z < m)
    (hN : A.innerRadius + m ≤ (TwoScale.Ratio.ratioRadius base N : ℝ))
    (h1 : 2 * (TwoScale.Ratio.ratioRadius base 1 : ℝ) + m ≤ A.outerRadius)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 N) :
    (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)).toSet ⊆ A.toSet ∧
      aroundDist D A ≤ aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)) ∧
      acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)) ≤ acrossDist D A := by
  obtain ⟨hin, hout⟩ := ratio_family_shift_margins A z base N m hnear hN h1 hj
  have hcenter : (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)).center = z :=
    crossingAt_center z _
  obtain ⟨hset, hbin, hbout⟩ :=
    nested_annulus_geometry A (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j))
      (by simpa only [hcenter] using hin) (by simpa only [hcenter] using hout)
  exact ⟨hset, aroundDist_le_of_nested D A _ hset hbin hbout,
    acrossDist_le_of_nested D hB hL A _ hbin hbout⟩

 

theorem ratio_family_outer_endpoint
    (A : EuclideanAnnulus) (z : ℂ) (base : Ioi (0 : ℝ))
    (N : ℕ) (m : ℝ)
    (hnear : dist A.center z < m)
    (h1 : 2 * (TwoScale.Ratio.ratioRadius base 1 : ℝ) + m ≤ A.outerRadius)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 N)
    {y : ℂ} (hy : A.outerRadius ≤ dist y A.center) :
    2 * (TwoScale.Ratio.ratioRadius base j : ℝ) ≤ dist y z := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hmono := TwoScale.OrderedCrossings.ratioRadius_antitone base hj1
  have htri := dist_triangle y z A.center
  rw [dist_comm z A.center] at htri
  linarith

 

theorem scale_family_margins
    {lam R α : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hR : 0 < R) (hα1 : α < 1)
    (A : EuclideanAnnulus)
    (hinner : A.innerRadius = lam * R)
    (houter : A.outerRadius = lam ^ α * R) :
    A.innerRadius + lam * R / 2 ≤
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) (scaleCount lam α) : ℝ) ∧
      2 * (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) 1 : ℝ) +
        lam * R / 2 ≤ A.outerRadius := by
  constructor
  · rw [hinner]
    have hlast : (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR)
        (scaleCount lam α) : ℝ) = 2 * lam * R := by
      change (2 * lam * R * (10 : ℝ) ^ scaleCount lam α) *
        (1 / 10 : ℝ) ^ scaleCount lam α = 2 * lam * R
      exact scaleBase_last lam R α
    rw [hlast]
    nlinarith [mul_pos hlam hR]
  · rw [houter]
    simpa only [TwoScale.Ratio.ratioRadius, pow_one] using
      scaleBase_outer_margin hlam hlam1 hR hα1

 

theorem exists_scale_mesh_family_comparisons
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {lam R α : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hR : 0 < R) (hα1 : α < 1)
    (z₀ : ℂ) (A : EuclideanAnnulus)
    (hcenter : A.center ∈ Metric.ball z₀ (2 * R))
    (hinner : A.innerRadius = lam * R)
    (houter : A.outerRadius = lam ^ α * R) :
    ∃ z ∈ TwoScale.Mesh.scaleMesh lam R z₀,
      dist A.center z < lam * R / 2 ∧
      ∀ j ∈ Finset.Icc 1 (scaleCount lam α),
        (BiLipschitz.OneScale.crossingAt z
          (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) j)).toSet ⊆ A.toSet ∧
        aroundDist D A ≤ aroundDist D (BiLipschitz.OneScale.crossingAt z
          (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) j)) ∧
        acrossDist D (BiLipschitz.OneScale.crossingAt z
          (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) j)) ≤ acrossDist D A := by
  obtain ⟨z, hz, hnear⟩ :=
    TwoScale.Mesh.exists_near_scaleMesh hlam hlam1.le hR z₀ A.center hcenter
  obtain ⟨hN, h1⟩ := scale_family_margins hlam hlam1 hR hα1 A hinner houter
  refine ⟨z, hz, hnear, ?_⟩
  intro j hj
  exact ratio_family_shifted_comparisons D hB hL A z
    (scaleBase lam R α hlam hR) (scaleCount lam α)
      (lam * R / 2) hnear hN h1 hj

 
theorem scale_hit_le_last_radius
    {lam R α : ℝ} (hlam : 0 < lam) (hR : 0 < R)
    {x z y : ℂ} (hnear : dist x z < lam * R / 2)
    (hy : dist y x ≤ lam * R) :
    dist y z ≤
      (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) (scaleCount lam α) : ℝ) := by
  have hlast : (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR)
      (scaleCount lam α) : ℝ) = 2 * lam * R := by
    change (2 * lam * R * (10 : ℝ) ^ scaleCount lam α) *
      (1 / 10 : ℝ) ^ scaleCount lam α = 2 * lam * R
    exact scaleBase_last lam R α
  rw [hlast]
  have htri := dist_triangle y x z
  linarith [mul_pos hlam hR]


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
