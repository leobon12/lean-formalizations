import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.FiniteScaleProbability




 



set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

open LQGMetric (DistC)

 
def finiteScaleGoodSample
    {Ω : Type} (h : Ω → DistC) (D : DistC → LSCMetric)
    (α M lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z₀ : ℂ) (ω : Ω) : Prop :=
  BiLipschitz.Barrier.Barrier (D (h ω)) ∧
  (D (h ω)).IsLengthSpace ∧
  (∀ z ∈ TwoScale.Mesh.scaleMesh lam R z₀, ∀ k : ℕ,
    aroundDist (D (h ω))
      (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius
        (scaleBase lam R α hlam hR) k)) ≠ ∞) ∧
  ¬ ∃ z ∈ TwoScale.Mesh.scaleMesh lam R z₀,
    (LQGMetric.Blueprint.countOcc
      (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
        (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)
        (ENNReal.ofReal M * ENNReal.ofReal M)})
      (scaleCount lam α) ω : ℝ) <
        (1 / 2 : ℝ) * scaleCount lam α

 



theorem finite_scale_ratio_f0
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ M C β lam₀ : ℝ,
      1 ≤ M ∧ 0 < C ∧ 0 < β ∧ 0 < lam₀ ∧
      lam₀ = scaleCutoff α
        (ENNReal.ofReal M * ENNReal.ofReal M).toReal ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (lam R : ℝ) (hlam : 0 < lam), lam ≤ lam₀ →
          (hR : 0 < R) → ∀ (z₀ : ℂ),
          P {ω | ¬ finiteScaleGoodSample h D α M lam R hlam hR z₀ ω} ≤
            ENNReal.ofReal (C * lam ^ (4 : ℕ)) ∧
          ∀ (ω : Ω), finiteScaleGoodSample h D α M lam R hlam hR z₀ ω →
            ∀ (A : EuclideanAnnulus), A.center ∈ Metric.ball z₀ (2 * R) →
              A.innerRadius = lam * R →
              A.outerRadius = lam ^ α * R →
              ∀ (K : Set ℂ), IsCompact K → A.toSet ⊆ K →
              ∀ {Pth : ℝ → ℂ} {T q : ℝ},
                0 < q → q < T →
                (D (h ω)).IsCurve Pth 0 T → MapsTo Pth (Icc 0 T) K →
                (∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
                  internalEDist ((D (h ω)).pt '' K)
                    ((D (h ω)).pt (Pth u)) ((D (h ω)).pt (Pth v)) =
                    ENNReal.ofReal (v - u)) →
                A.outerRadius ≤ dist (Pth 0) A.center →
                A.outerRadius ≤ dist (Pth T) A.center →
                dist (Pth q) A.center ≤ A.innerRadius →
                aroundDist (D (h ω)) A ≤
                  ENNReal.ofReal (lam ^ β) * acrossDist (D (h ω)) A := by
  obtain ⟨p, c, M, C, hp, hp1, hc, hM, hC, hprob⟩ :=
    finite_scale_good_sample_bad_probability ξ Q D hD α hα1
  let cost : ℝ≥0∞ := ENNReal.ofReal M * ENNReal.ofReal M
  have hcost0 : cost ≠ 0 := by
    dsimp [cost]
    exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne'
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne').ne'
  have hcosttop : cost ≠ ∞ := by
    dsimp [cost]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hcost : 0 < cost.toReal := ENNReal.toReal_pos hcost0 hcosttop
  let β := ratioExponent α cost.toReal / 2
  let lam₀ := scaleCutoff α cost.toReal
  have hβ : 0 < β := div_pos (ratioExponent_pos hα1 hcost) (by norm_num)
  have hlam₀ : 0 < lam₀ := Real.exp_pos _
  refine ⟨M, C, β, lam₀, hM, hC, hβ, hlam₀, rfl, ?_⟩
  intro Ω _ P _ h hh lam R hlam hsmall hR z₀
  have hlam1 : lam < 1 := (scaleCutoff_properties hα1 hcost hlam hsmall).1
  constructor
  · simpa only [finiteScaleGoodSample, cost, lam₀] using
      hprob P h hh lam R hlam hlam1 hR z₀
  · intro ω hgood A hcenter hinner houter K hK hAK Pth T q hq0 hqT
      hP hPK hgeo h0 hT hq
    rcases hgood with ⟨hB, hL, hfin, hcount⟩
    exact finite_scale_ratio_of_good_sample h ω D hlam hlam1 hR hα1 hM
      z₀ hB hL hfin hcount hsmall A hcenter hinner houter K hK hAK
      hq0 hqT hP hPK hgeo h0 hT hq


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
