import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.CutoffNumerics
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.CarrierDyadic




 



set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

open LQGMetric (DistC)

 
def carrierRatioProperty
    {Ω : Type} (h : Ω → DistC) (ω : Ω) (D : DistC → LSCMetric)
    (θ q R : ℝ) (z₀ : ℂ) : Prop :=
  ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ q →
  ∀ (x : ℂ), 3 * R / 4 ≤ dist x z₀ → dist x z₀ ≤ 3 * R / 2 →
  ∀ {Pth : ℝ → ℂ} {T s : ℝ}, 0 < s → s < T →
    (D (h ω)).IsCurve Pth 0 T →
    MapsTo Pth (Icc 0 T) (closedBall z₀ (2 * R) \ ball z₀ (R / 2)) →
    (∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist ((D (h ω)).pt ''
        (closedBall z₀ (2 * R) \ ball z₀ (R / 2)))
        ((D (h ω)).pt (Pth u)) ((D (h ω)).pt (Pth v)) =
          ENNReal.ofReal (v - u)) →
    (dist (Pth 0) z₀ = R / 2 ∨ dist (Pth 0) z₀ = 2 * R) →
    (dist (Pth T) z₀ = R / 2 ∨ dist (Pth T) z₀ = 2 * R) →
    dist (Pth s) x ≤ δ * R →
    ∀ A : EuclideanAnnulus,
      A.center = x → A.innerRadius = δ * R →
      A.outerRadius = δ ^ ((1 : ℝ) / 2) * R →
      aroundDist (D (h ω)) A ≤
        ENNReal.ofReal (δ ^ θ) * acrossDist (D (h ω)) A

 

theorem exists_carrier_high_probability_ratio_f0
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) :
    ∃ M C θ q : ℝ,
      1 ≤ M ∧ 0 < C ∧ 0 < θ ∧ 0 < q ∧ q ≤ 1 / 16 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (hq : 0 < q) (R : ℝ) (hR : 0 < R) (z₀ : ℂ),
          P {ω | ¬ dyadicGoodSample h D ((3 : ℝ) / 4) M q R
              hq hR z₀ ω} ≤ ENNReal.ofReal (p / 4) ∧
          ∀ (ω : Ω), dyadicGoodSample h D ((3 : ℝ) / 4) M q R
              hq hR z₀ ω →
            carrierRatioProperty h ω D θ q R z₀ := by
  obtain ⟨M, C, β, lam₀, hM, hC, hβ, hlam₀, heqcut, htail⟩ :=
    dyadic_good_sample_bad_probability ξ Q D hD ((3 : ℝ) / 4)
      (by norm_num) (by norm_num)
  obtain ⟨q, hq, hq16, hqcut, hqrad, hqradSmall, hbudget⟩ :=
    exists_ratio_cutoff hp hC hlam₀
  have hcut : q ≤ scaleCutoff ((3 : ℝ) / 4)
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal := by
    simpa only [heqcut] using hqcut
  let θ := ratioExponent ((3 : ℝ) / 4)
    (ENNReal.ofReal M * ENNReal.ofReal M).toReal / 4
  have hcost0 : (ENNReal.ofReal M * ENNReal.ofReal M) ≠ 0 := by
    exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne'
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne').ne'
  have hcosttop : (ENNReal.ofReal M * ENNReal.ofReal M) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hθ : 0 < θ := div_pos
    (ratioExponent_pos (by norm_num)
      (ENNReal.toReal_pos hcost0 hcosttop)) (by norm_num)
  refine ⟨M, C, θ, q, hM, hC, hθ, hq, hq16, ?_⟩
  intro Ω _ P _ h hh hq_unused R hR z₀
  constructor
  · exact (htail P h hh q R hq hqcut hR z₀).trans hbudget
  · intro ω hgood
    intro δ hδ hδq x hxlo hxhi Pth T s hs0 hsT hP hPK hgeo h0 hT
      hhit A hAc hAi hAo
    have hratio := carrier_dyadic_ratio_f0 h ω D M hM hq
      (hq16.trans (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8))
      hqrad hR z₀ hgood hcut hδ hδq x hxlo hxhi
      hs0 hsT hP hPK hgeo h0 hT hhit
    have hAeq : A = annulusAt x (δ * R) (δ ^ ((1 : ℝ) / 2) * R)
      (mul_pos hδ hR)
      (mul_lt_mul_of_pos_right
        (Real.self_lt_rpow_of_lt_one hδ (lt_of_le_of_lt hδq
          (by linarith : q < 1)) (by norm_num)) hR) := by
      apply Subtype.ext
      exact Prod.ext hAc (Prod.ext hAi hAo)
    subst A
    exact hratio


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
