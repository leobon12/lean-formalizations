import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism.HDet




 





set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls

open LQGMetric (DistC)

 
theorem aroundDist_exists_finite_trace (d : LSCMetric) (A : EuclideanAnnulus)
    (hfin : aroundDist d A < ⊤) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ A.toSet) ∧
      Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary ∧
      d.len P a b < ⊤ := by
  unfold aroundDist at hfin
  simp only [iInf_lt_iff] at hfin
  obtain ⟨P, a, b, hP, hA, hdisc, hlen⟩ := hfin
  exact ⟨P, a, b, hP, hA, hdisc, hlen⟩

theorem ae_aroundDist_lt_top
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (A : EuclideanAnnulus) :
    ∀ᵐ ω ∂μ, aroundDist (D (h ω)) A < ⊤ := by
  let r : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  let X : Set.Ioi (0 : ℝ) → Ω → ℝ≥0∞ := fun s ω =>
    ENNReal.ofReal ((s : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) s 0))) *
      aroundDist (D (h ω)) (A.dilate s s.2)
  have hV : IsTwoSidedTight μ X :=
    (hD.tightness μ h hh
      (fun s ω => LQGMetric.circleAvg (h ω) s 0)
      (fun s => ae_isCircleAverage_old hh.1 s 0) A).2
  filter_upwards [OptimalConstants.Determinism.ae_lt_top_of_twoSidedTight μ X hV r] with ω hfin
  have hcoef : 0 < ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r 0))) := by
    dsimp [r]
    positivity
  have hAfin : aroundDist (D (h ω)) (A.dilate r r.2) < ⊤ := by
    by_contra hn
    have ht : aroundDist (D (h ω)) (A.dilate r r.2) = ⊤ :=
      eq_top_iff.mpr (not_lt.mp hn)
    have hcf : ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r 0))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hcoef).ne'
    have : X r ω = ⊤ := by simpa only [X, ht] using ENNReal.mul_top hcf
    exact (ne_top_of_lt hfin) this
  have hone : A.dilate r r.2 = A := by
    apply Subtype.ext
    rcases A with ⟨⟨z, rin, rout⟩, hA⟩
    simp [r, EuclideanAnnulus.dilate, EuclideanAnnulus.center,
      EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius]
  simpa only [hone] using hAfin

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls
