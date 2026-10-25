import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.NormalizedCostFactor
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.HolderAdapter
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.GaussianExpMoment




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem normalizedAroundAt_moment_le
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p q : ℝ) (hp : 0 < p) (hq : 1 < q) :
    ∃ M : ENNReal, M < ∞ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (a s : Set.Ioi (0 : ℝ)) (_has : (a : ℝ) ≤ s)
          (y c : ℂ) (_hnear : ‖y - c‖ ≤ s),
          (∫⁻ ω, normalizedAroundAt ξ Q D (h ω) a s y c ^ p ∂P) ≤
            ENNReal.ofReal ((a / s) ^ (ξ * Q)) ^ p *
              M ^ (1 / (q / (q - 1))) *
              ENNReal.ofReal
                (Real.exp ((p * q * ξ) ^ 2 *
                  (Real.log (s / a) + 2 * Real.log (1 + 1)) / 2)) ^ (1 / q) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hconj : 0 < q / (q - 1) := div_pos hq0 (sub_pos.mpr hq)
  have hm : 0 < p * (q / (q - 1)) := mul_pos hp hconj
  obtain ⟨M, hMfin, hMoment⟩ :=
    normalizedAroundCost_moment ξ Q hQ D hD (p * (q / (q - 1))) hm
  refine ⟨M, hMfin, ?_⟩
  intro Ω _ P _ h hh a s has y c hnear
  let S : ENNReal := ENNReal.ofReal ((a / s) ^ (ξ * Q))
  let X : Ω → ENNReal := fun ω => normalizedAroundCost ξ Q D (h ω) a y
  let E : Ω → ENNReal := fun ω =>
    ENNReal.ofReal (Real.exp
      (ξ * LQGMetric.CircleAvg.cInc h a y s c ω))
  have hXmeas : AEMeasurable X P :=
    ((measurable_normalizedAroundCost ξ Q D hD.1 a y).comp hh.1.measurable).aemeasurable
  have hinc : Measurable (LQGMetric.CircleAvg.cInc h a y s c) :=
    LQGMetric.CircleAvg.measurable_cInc hh.1 a y s c
  have hEmeas : AEMeasurable E P := by
    have h : Measurable E := by
      dsimp [E]
      exact ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp (measurable_const.mul hinc))
    exact h.aemeasurable
  have hfactor (ω : Ω) :
      normalizedAroundAt ξ Q D (h ω) a s y c = S * (X ω * E ω) := by
    rw [normalizedAroundAt_eq]
    change S * X ω * E ω = S * (X ω * E ω)
    exact mul_assoc _ _ _
  have hXmoment : (∫⁻ ω, (X ω ^ p) ^ (q / (q - 1)) ∂P) ≤ M := by
    simp_rw [← ENNReal.rpow_mul]
    exact hMoment P h hh a y
  have hEpow (ω : Ω) :
      (E ω ^ p) ^ q =
        ENNReal.ofReal (Real.exp ((p * q * ξ) *
          LQGMetric.CircleAvg.cInc h a y s c ω)) := by
    dsimp [E]
    rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le
      (mul_pos hp hq0).le]
    rw [← Real.exp_mul]
    congr 1
    ring_nf
  have hEmoment : (∫⁻ ω, (E ω ^ p) ^ q ∂P) ≤
      ENNReal.ofReal
        (Real.exp ((p * q * ξ) ^ 2 *
          (Real.log (s / a) + 2 * Real.log (1 + 1)) / 2)) := by
    simp_rw [hEpow]
    exact lintegral_exp_circleAvg_increment_le hh.1 a.2 has (by norm_num)
      y c (by simpa only [one_mul] using hnear) (p * q * ξ)
  have hHolder := lintegral_mul_rpow_le_holder P X E hXmeas hEmeas p q hp hq
  have hSfinite : S ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  have hL : (∫⁻ ω, normalizedAroundAt ξ Q D (h ω) a s y c ^ p ∂P) =
      S ^ p * ∫⁻ ω, (X ω * E ω) ^ p ∂P := by
    calc
      _ = ∫⁻ ω, S ^ p * (X ω * E ω) ^ p ∂P := by
        apply lintegral_congr
        intro ω
        rw [hfactor ω, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      _ = _ := lintegral_const_mul' (S ^ p) _ hSfinite
  rw [hL]
  have hconjInv : 0 ≤ 1 / (q / (q - 1)) := by positivity
  have hqInv : 0 ≤ 1 / q := by positivity
  calc
    S ^ p * (∫⁻ ω, (X ω * E ω) ^ p ∂P) ≤
      S ^ p * ((∫⁻ ω, (X ω ^ p) ^ (q / (q - 1)) ∂P) ^
        (1 / (q / (q - 1))) *
        (∫⁻ ω, (E ω ^ p) ^ q ∂P) ^ (1 / q)) :=
        mul_le_mul' le_rfl hHolder
    _ ≤ S ^ p * (M ^ (1 / (q / (q - 1))) *
        ENNReal.ofReal
          (Real.exp ((p * q * ξ) ^ 2 *
            (Real.log (s / a) + 2 * Real.log (1 + 1)) / 2)) ^ (1 / q)) :=
      mul_le_mul' le_rfl (mul_le_mul'
        (ENNReal.rpow_le_rpow hXmoment hconjInv)
        (ENNReal.rpow_le_rpow hEmoment hqInv))
    _ = _ := by
      dsimp only [S]
      ac_rfl


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
