import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.PlanarTransfer
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.RatioAlgebra




 






set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

 


theorem selected_growth_at_hit_annulus
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (K : Set ℂ) (hK : IsCompact K)
    {lam R α : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hR : 0 < R) (hα1 : α < 1)
    (A : EuclideanAnnulus) (hAK : A.toSet ⊆ K)
    (hinner : A.innerRadius = lam * R)
    (houter : A.outerRadius = lam ^ α * R)
    (z : ℂ) (hnear : dist A.center z < lam * R / 2)
    (S : Finset ℕ) (hcard : 2 ≤ S.card)
    (hS : S ⊆ Finset.Icc 1 (scaleCount lam α))
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    {P : ℝ → ℂ} {T q : ℝ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (h0 : A.outerRadius ≤ dist (P 0) A.center)
    (hT : A.outerRadius ≤ dist (P T) A.center)
    (hq : dist (P q) A.center ≤ A.innerRadius)
    (hgood : ∀ i ∈ S,
      aroundDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)) ≤
        C * acrossDist D (BiLipschitz.OneScale.crossingAt z
          (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)))
    (hfin : ∀ i ∈ S,
      aroundDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)) ≠ ∞)
    (hsmall : lam ≤ scaleCutoff α C.toReal)
    (hhalf : (scaleCount lam α : ℝ) / 2 ≤ (S.card : ℝ)) :
    ∃ i ∈ S, ∃ j ∈ S,
      aroundDist D A ≤ aroundDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) j)) ∧
      aroundDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)) ≤
          C * acrossDist D A ∧
      (1 / C.toReal) * (1 + 1 / C.toReal) ^ (S.card - 2) *
        (aroundDist D (BiLipschitz.OneScale.crossingAt z
          (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) j))).toReal ≤
        (aroundDist D (BiLipschitz.OneScale.crossingAt z
          (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i))).toReal ∧
      (acrossDist D A = ∞ ∨
        (aroundDist D A).toReal ≤
          (C.toReal ^ 2 / (1 + 1 / C.toReal) ^ (S.card - 2)) *
            (acrossDist D A).toReal) ∧
      aroundDist D A ≤
        ENNReal.ofReal (lam ^ (ratioExponent α C.toReal / 2)) * acrossDist D A := by
  obtain ⟨hN, h1⟩ := scale_family_margins hlam hlam1 hR hα1 A hinner houter
  have hgeom : ∀ k ∈ S,
      (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)).toSet ⊆ A.toSet ∧
      aroundDist D A ≤ aroundDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)) ∧
      acrossDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)) ≤ acrossDist D A := by
    intro k hk
    exact ratio_family_shifted_comparisons D hB hL A z
      (scaleBase lam R α hlam hR) (scaleCount lam α)
      (lam * R / 2) hnear hN h1 (hS hk)
  have hqN : dist (P q) z ≤
      (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) (scaleCount lam α) : ℝ) :=
    scale_hit_le_last_radius hlam hR hnear (by simpa only [hinner] using hq)
  obtain ⟨i, hi, j, hj, -, -, hgrowth⟩ :=
    TwoScale.OrderedCrossings.selected_ratio_growth_on_internal_geodesic D K hK z
      (scaleBase lam R α hlam hR) (scaleCount lam α)
      S hcard hS C hC0 hCtop hq0 hqT hP hPK hgeo
      (fun k hk => (hgeom k hk).1.trans hAK)
      (fun k hk => ratio_family_outer_endpoint A z
        (scaleBase lam R α hlam hR) (scaleCount lam α)
        (lam * R / 2) hnear h1 (hS hk) h0)
      (fun k hk => ratio_family_outer_endpoint A z
        (scaleBase lam R α hlam hR) (scaleCount lam α)
        (lam * R / 2) hnear h1 (hS hk) hT)
      hqN hgood hfin
  have hBigAround := (hgeom j hj).2.1
  have hOuter : aroundDist D (BiLipschitz.OneScale.crossingAt z
      (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)) ≤
        C * acrossDist D A := by
    calc
      aroundDist D (BiLipschitz.OneScale.crossingAt z
      (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)) ≤
      C * acrossDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)) := hgood i hi
    _ ≤ C * acrossDist D A := by
        gcongr
        exact (hgeom i hi).2.2
  have hratio := finite_cost_gain_to_scaled_ratio hlam hα1 C
    (aroundDist D A)
    (aroundDist D (BiLipschitz.OneScale.crossingAt z
      (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) j)))
    (aroundDist D (BiLipschitz.OneScale.crossingAt z
      (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)))
    (acrossDist D A) S.card hC0 hCtop hsmall hhalf
    (hfin j hj) (hfin i hi) hBigAround hOuter hgrowth
  refine ⟨i, hi, j, hj, hBigAround, hOuter, hgrowth, ?_, hratio⟩
  by_cases hY : acrossDist D A = ∞
  · exact Or.inl hY
  · exact Or.inr (finite_cost_gain_to_ratio C (aroundDist D A)
      (aroundDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) j)))
      (aroundDist D (BiLipschitz.OneScale.crossingAt z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) i)))
      (acrossDist D A) (S.card - 2) hC0 hCtop
      (hfin j hj) (hfin i hi) hY hBigAround hOuter hgrowth)


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
