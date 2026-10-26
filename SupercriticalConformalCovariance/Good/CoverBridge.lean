import SupercriticalConformalCovariance.Cover.Subsequence
import SupercriticalConformalCovariance.Improve.Improvement

/-!
The deterministic and probabilistic bridge from the literal good-annulus
event of paper lines 403–410 to the exact GoodCover used in Proposition 6.1.
The locality and probability assertion of Lemma 5.1 is an explicit remaining
input, with its quantifiers unchanged.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Good

open LQGMetric (DistC IsWholePlaneGFF)
open SupercriticalLQGUniqueness (LSCMetric)

/-- The literal event F_{z,r}; the circle average witnesses the common
normalizer of G2 and G5. Nonpositive radii have the empty event. -/
def GoodEvent {Ω : Type} (h : Ω → DistC)
    (D : Ω → LSCMetric) (e : Ω → ℂ × ℂ → ℝ≥0∞)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η : ℝ) (z : ℂ) (r : ℝ) : Set Ω :=
  {ω | ∃ hr : 0 < r, ∃ c : ℝ,
    SupercriticalLQGUniqueness.IsCircleAverage
      (h ω) ⟨r, hr⟩ z c ∧
    SupercriticalConformalCovariance.Improve.Good (D ω) (e ω) ξ Q z ⟨r, hr⟩ q a K θ k c η}

/-- The fixed summable scale sequence used by the generic covering theorem. -/
def coverScale (j : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (j + 1)

theorem coverScale_pos_le_one (j : ℕ) :
    0 < coverScale j ∧ coverScale j ≤ 1 := by
  constructor
  · exact pow_pos (by norm_num) _
  · exact pow_le_one₀ (by norm_num) (by norm_num)

/-- An actual finite-family cover supplies precisely the existential witnesses
in the Proposition 6.1 proof's GoodCover, including the interval [ε_j², ε_j]. -/
theorem goodCover_of_eventual_cover {Ω : Type} (h : Ω → DistC)
    (D : Ω → LSCMetric) (e : Ω → ℂ × ℂ → ℝ≥0∞)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η : ℝ)
    (exhaustion : ℕ → Set ℂ) (ω : Ω)
    (hcover : ∀ n, ∀ᶠ j in atTop,
      ω ∈ SupercriticalConformalCovariance.Cover.coverEvent
        (GoodEvent h D e ξ Q q a K θ k η) (exhaustion n) (coverScale j)) :
    SupercriticalConformalCovariance.Improve.GoodCover (D ω) (e ω) ξ Q q a K θ k η
      exhaustion coverScale := by
  refine ⟨SupercriticalConformalCovariance.Cover.tendsto_two_pow, coverScale_pos_le_one, ?_⟩
  intro n
  filter_upwards [hcover n] with j hj x hx
  obtain ⟨zr, hzr, hball, hgood⟩ := hj x hx
  obtain ⟨hr, c, _, hG⟩ := hgood
  obtain ⟨hrlow, hrhi⟩ :=
    SupercriticalConformalCovariance.Cover.coverFamily_radius (coverScale_pos_le_one j).1.le hzr
  refine ⟨zr.1, zr.2, hr, c, hG, hrlow, ?_, hball⟩
  linarith [(coverScale_pos_le_one j).1]

/-- Lemma 5.1, once proved with exactly its locality and compact-uniform
probability conclusion, supplies the Proposition 6.1 proof's almost-sure GoodCover. The cover
threshold p and the geometric parameters are fixed before η. -/
theorem ae_goodCover_of_lemma51
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P)
    (D : Ω → LSCMetric) (e : Ω → ℂ × ℂ → ℝ≥0∞)
    (U : Set ℂ) (hU : IsOpen U)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k : ℝ)
    (exhaustion : ℕ → Set ℂ)
    (hKc : ∀ n, IsCompact (exhaustion n))
    (hKU : ∀ n, exhaustion n ⊆ U) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ∀ η : ℝ, 0 < η →
      (∀ L : Set ℂ, IsCompact L → L ⊆ U →
        ∃ r₀ : ℝ, 0 < r₀ ∧
          ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
            LQGMetric.Blueprint.AEEventIn P (SupercriticalConformalCovariance.Cover.localSigma h z r)
              (GoodEvent h D e ξ Q q a K θ k η z r) ∧
            ENNReal.ofReal p ≤
              P (GoodEvent h D e ξ Q q a K θ k η z r)) →
      ∀ᵐ ω ∂P,
        SupercriticalConformalCovariance.Improve.GoodCover (D ω) (e ω) ξ Q q a K θ k η
          exhaustion coverScale := by
  obtain ⟨p, hp0, hp1, H⟩ := SupercriticalConformalCovariance.Cover.goodCovers_everyCompact 1 (by norm_num)
  refine ⟨p, hp0, hp1, ?_⟩
  intro η _ h51
  have hcover := H P h hh U hU
    (GoodEvent h D e ξ Q q a K θ k η) h51
    coverScale (fun j => (coverScale_pos_le_one j).1)
    SupercriticalConformalCovariance.Cover.tendsto_two_pow
    (SupercriticalConformalCovariance.Cover.summable_two_pow (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hcover] with ω hω
  apply goodCover_of_eventual_cover h D e ξ Q q a K θ k η exhaustion ω
  intro n
  exact hω (exhaustion n) (hKc n) (hKU n)

end SupercriticalConformalCovariance.Good
