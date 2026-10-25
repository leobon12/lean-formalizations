import SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.OrderedCrossings
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioIteration




 






set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings

 
theorem ratioRadius_step (base : Ioi (0 : ℝ)) (k : ℕ) :
    (TwoScale.Ratio.ratioRadius base (k + 1) : ℝ) =
      (TwoScale.Ratio.ratioRadius base k : ℝ) / 10 := by
  simp only [TwoScale.Ratio.ratioRadius, pow_succ]
  ring

theorem ratioRadius_sep (base : Ioi (0 : ℝ)) (k : ℕ) :
    2 * (TwoScale.Ratio.ratioRadius base (k + 1) : ℝ) ≤
      (TwoScale.Ratio.ratioRadius base k : ℝ) := by
  rw [ratioRadius_step]
  have hr := (TwoScale.Ratio.ratioRadius base k).2
  change 0 < (TwoScale.Ratio.ratioRadius base k : ℝ) at hr
  linarith

theorem ratioRadius_antitone (base : Ioi (0 : ℝ)) :
    Antitone (fun k : ℕ => (TwoScale.Ratio.ratioRadius base k : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := ratioRadius_sep base k
  have hp := (TwoScale.Ratio.ratioRadius base (k + 1)).2
  change 0 < (TwoScale.Ratio.ratioRadius base (k + 1) : ℝ) at hp
  linarith

 

theorem sum_ratio_acrossDist_le_internal_geodesic_time
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    (z : ℂ) (base : Ioi (0 : ℝ))
    {P : ℝ → ℂ} {T a b : ℝ} (n k : ℕ)
    (h0a : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (ha : 2 * (TwoScale.Ratio.ratioRadius base k : ℝ) ≤ dist (P a) z)
    (hb : dist (P b) z ≤ (TwoScale.Ratio.ratioRadius base (k + n - 1) : ℝ)) :
    (∑ j ∈ Finset.Ico k (k + n),
      acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j))) ≤
      ENNReal.ofReal (b - a) := by
  let r : ℕ → ℝ := fun j => (TwoScale.Ratio.ratioRadius base j : ℝ)
  have hrpos : ∀ j, 0 < r j := fun j => (TwoScale.Ratio.ratioRadius base j).2
  have hsep : ∀ j, 2 * r (j + 1) ≤ r j := ratioRadius_sep base
  have hmono : ∀ i j, i ≤ j → r j ≤ r i := ratioRadius_antitone base
  have hbase := sum_acrossDist_le_internal_geodesic_time D K hK z r
    hrpos hsep hmono n k h0a hab hbT hP hPK hgeo ha hb
  convert hbase using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Subtype.ext
  simp only [radialAnnulus, BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape,
    Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.dilate,
    EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius, r, smul_zero, zero_add, mul_one]
  rw [mul_comm (TwoScale.Ratio.ratioRadius base j : ℝ) 2]


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings
