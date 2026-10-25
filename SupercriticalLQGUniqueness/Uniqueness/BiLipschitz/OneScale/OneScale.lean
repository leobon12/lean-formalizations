import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus
import LQGMetric.Papers.LM.L3_4M6




 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale

open LQGMetric (DistC circleAvg)
open SupercriticalLQGUniqueness

 
def crossingShape : EuclideanAnnulus :=
  ⟨(0, 1, 2), one_pos, by norm_num⟩

def separatorShape : EuclideanAnnulus :=
  ⟨(0, 2, 3), by norm_num, by norm_num⟩

 
theorem exists_iteration_constants :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsNormalizedWPGFF h P →
        ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
          LQGMetric.Blueprint.AnnulusIterHyp h (1 / 10) (4 / 5) r E →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E K ω : ℝ) <
            (1 / 2 : ℝ) * K} ≤
            ENNReal.ofReal (c * Real.exp (-(8 * Real.log 10) * K)) := by
  have ha : 0 < 8 * Real.log (10 : ℝ) := by
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  exact LQGMetric.LM.lmLem3_1a (1 / 10) (4 / 5)
    (by norm_num) (by norm_num) (by norm_num)
    (8 * Real.log 10) ha (1 / 2) (by norm_num) (by norm_num)

 
def crossingX (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (g : DistC) (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
    acrossDist (D g) (crossingShape.dilate r r.2)

 
def separatorY (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D' : DistC → LSCMetric)
    (g : DistC) (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
    aroundDist (D' g) (separatorShape.dilate r r.2)

theorem measurable_crossingX (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (r : Ioi (0 : ℝ)) : Measurable (fun g => crossingX ξ Q D g r) :=
  measurable_normalized_across ξ Q D hD.measurable crossingShape r

theorem measurable_separatorY (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D' : DistC → LSCMetric) (hD' : IsWeakLQGMetric ξ Q D')
    (r : Ioi (0 : ℝ)) : Measurable (fun g => separatorY ξ Q D' g r) := by
  have hca : Measurable fun g : DistC => circleAvg g r 0 :=
    LQGMetric.measurable_circleAvg_left r 0
  have har : Measurable fun g : DistC =>
      aroundDist (D' g) (separatorShape.dilate r r.2) :=
    (Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD'.measurable
  exact ((measurable_const.mul
    ((Real.measurable_exp.comp (measurable_const.mul hca).neg))).ennreal_ofReal).mul har

 
theorem origin_paired_marginal {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : Ioi (0 : ℝ),
      ENNReal.ofReal p ≤ P {ω |
        ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D (h ω) r ∧
        separatorY ξ Q D' (h ω) r ≤ ENNReal.ofReal A} := by
  let ε : ℝ := (1 - p) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hV₁ : IsTwoSidedTight P (fun r ω => crossingX ξ Q D (h ω) r) :=
    (hD.tightness P h hh (fun r ω => circleAvg (h ω) r 0)
      (fun r => ae_isCircleAverage_old hh.1 r 0) crossingShape).1
  have hV₂ : IsTwoSidedTight P (fun r ω => separatorY ξ Q D' (h ω) r) :=
    (hD'.tightness P h hh (fun r ω => circleAvg (h ω) r 0)
      (fun r => ae_isCircleAverage_old hh.1 r 0) separatorShape).2
  obtain ⟨M₁, hM₁, ht₁⟩ := hV₁.2 ε hε
  obtain ⟨M₂, hM₂, ht₂⟩ := hV₂.2 ε hε
  let A := max 1 (max M₁ M₂)
  have hA : 1 ≤ A := le_max_left _ _
  have hM₁A : M₁ ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM₂A : M₂ ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  intro r
  have hcross : P {ω | crossingX ξ Q D (h ω) r < ENNReal.ofReal A⁻¹} ≤
      ENNReal.ofReal ε := by
    apply le_trans (measure_mono ?_) (ht₁ r).2
    intro ω hω
    have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
    have hAinv : A⁻¹ ≤ M₁⁻¹ := (inv_le_inv₀ hA0 hM₁).2 hM₁A
    exact lt_of_lt_of_le hω (ENNReal.ofReal_le_ofReal hAinv)
  have hsep : P {ω | ENNReal.ofReal A < separatorY ξ Q D' (h ω) r} ≤
      ENNReal.ofReal ε := by
    apply le_trans (measure_mono ?_) (ht₂ r).1
    intro ω hω
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hM₂A) hω
  have hgood : MeasurableSet {ω |
      ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D (h ω) r ∧
      separatorY ξ Q D' (h ω) r ≤ ENNReal.ofReal A} := by
    exact (measurableSet_le measurable_const
      ((measurable_crossingX ξ Q D hD r).comp hh.1.measurable)).inter
      (measurableSet_le ((measurable_separatorY ξ Q D' hD' r).comp hh.1.measurable)
        measurable_const)
  have hcomp : P {ω | ¬ (ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D (h ω) r ∧
      separatorY ξ Q D' (h ω) r ≤ ENNReal.ofReal A)} ≤
      ENNReal.ofReal (1 - p) := by
    calc
      P {ω | ¬ (ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D (h ω) r ∧
        separatorY ξ Q D' (h ω) r ≤ ENNReal.ofReal A)} ≤
          P {ω | crossingX ξ Q D (h ω) r < ENNReal.ofReal A⁻¹} +
          P {ω | ENNReal.ofReal A < separatorY ξ Q D' (h ω) r} := by
            apply le_trans (measure_mono ?_) (measure_union_le _ _)
            intro ω hω
            simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hω
            exact hω
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hcross hsep
      _ = ENNReal.ofReal (1 - p) := by
        rw [← ENNReal.ofReal_add hε.le]
        congr 1
        dsimp [ε]
        ring
        exact hε.le
  have hpE : ENNReal.ofReal p ≤ (1 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp1.le
  have hid : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - p) = ENNReal.ofReal p := by
    rw [ENNReal.ofReal_sub 1 hp0.le, ENNReal.ofReal_one]
    exact ENNReal.sub_sub_cancel (by norm_num) hpE
  have hcompl : P {ω |
      ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D (h ω) r ∧
      separatorY ξ Q D' (h ω) r ≤ ENNReal.ofReal A} =
      (1 : ℝ≥0∞) - P {ω | ¬ (ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D (h ω) r ∧
      separatorY ξ Q D' (h ω) r ≤ ENNReal.ofReal A)} := by
    simpa only [Set.compl_ofPred, not_not] using
      (prob_compl_eq_one_sub (μ := P) hgood.compl)
  rw [hcompl, ← hid]
  exact tsub_le_tsub_left hcomp 1

 
theorem origin_paired_uniform
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ r : Ioi (0 : ℝ),
        ENNReal.ofReal p ≤ P {ω |
          ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D (h ω) r ∧
          separatorY ξ Q D' (h ω) r ≤ ENNReal.ofReal A} := by
  obtain ⟨μ, hμprob, hμ⟩ := Positivity.Witnesses.exists_canonical_normalized_law
  letI : IsProbabilityMeasure μ := hμprob
  obtain ⟨A, hA, htail⟩ := origin_paired_marginal μ id hμ ξ Q D D' hD hD' p hp0 hp1
  refine ⟨A, hA, ?_⟩
  intro Ω mΩ P iP h hh r
  let B : Set DistC := {g |
    ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D g r ∧
    separatorY ξ Q D' g r ≤ ENNReal.ofReal A}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const (measurable_crossingX ξ Q D hD r)).inter
      (measurableSet_le (measurable_separatorY ξ Q D' hD' r) measurable_const)
  have hlaw : P.map h = μ := by
    simpa only [Measure.map_id] using map_eq_of_candidate_normalized hh hμ
  change ENNReal.ofReal p ≤ P (h ⁻¹' B)
  rw [← Measure.map_apply hh.1.measurable hB, hlaw]
  simpa only [id_eq] using htail r


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale
