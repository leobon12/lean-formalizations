import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.ModConstClosed
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory LQGMetric.Blueprint
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

private theorem closedAnn_compact (w : ℂ) (s : ℝ) :
    IsCompact (BiLipschitz.Barrier.closedAnn w s (2*s)) := by
  have hc : IsClosed (BiLipschitz.Barrier.closedAnn w s (2*s)) := by
    exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  have hsub : BiLipschitz.Barrier.closedAnn w s (2*s) ⊆ Metric.closedBall w (2*s) := by
    intro x hx
    exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hx.2)
  exact (isCompact_closedBall w (2*s)).of_isClosed_subset hc hsub

private theorem closedAnn_subset_iterAnn (w : ℂ) (s : ℝ) (hs : 0 < s) :
    BiLipschitz.Barrier.closedAnn w s (2*s) ⊆
      annulus w ((1/4 : ℝ)*(3*s)) ((3/4 : ℝ)*(3*s)) := by
  intro x hx
  change (1/4 : ℝ)*(3*s) < ‖x-w‖ ∧ ‖x-w‖ < (3/4 : ℝ)*(3*s)
  constructor <;> nlinarith [hx.1, hx.2]

def regRadius (base : ℝ) (i : ℕ) : ℝ := base * (1/4 : ℝ)^i

private theorem regRadius_pos (base : ℝ) (hb : 0 < base) (i : ℕ) :
    0 < regRadius base i := mul_pos hb (pow_pos (by norm_num) _)

private theorem regRadius_antitone (base : ℝ) (hb : 0 < base) :
    Antitone (regRadius base) := by
  intro i j hij
  unfold regRadius
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij) hb.le

private theorem regRadius_ratio (base : ℝ) (hb : 0 < base) (i : ℕ) :
    regRadius base (i+1) / regRadius base i ≤ (1/4 : ℝ) := by
  have hi := regRadius_pos base hb i
  unfold regRadius
  rw [pow_succ]
  field_simp
  norm_num

 
theorem regGood_iteration_tail
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (a : ℝ) (ha : 0 < a) :
    ∃ p c cReg : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 0 < cReg ∧ cReg < 1 ∧
      ∀ (C : Objects.CorrectedEvent.Constants), C.c_reg ≤ cReg → ∀ (w : ℂ) (base : ℝ),
        0 < base → ∀ K : ℕ,
        μ {g | (countOcc (fun i =>
          {g | Objects.CorrectedEvent.regGood C (D g) (regRadius base i) w}) K g : ℝ) <
          (1/2 : ℝ) * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hLM⟩ :=
    Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open (1/4) (3/4)
      (by norm_num) (by norm_num) (by norm_num) a ha
      (1/2) (by norm_num) (by norm_num)
  obtain ⟨cReg, hcR0, hcR1, hmarg⟩ :=
    exists_regGood_uniform μ hμ ξ Q D hD p hp0 hp1
  refine ⟨p, c, cReg, hp0, hp1, hc0, hcR0, hcR1, ?_⟩
  intro C hC w base hb K
  let r : ℕ → ℝ := fun i => 3 * regRadius base i
  let E : ℕ → Set LQGMetric.DistC :=
    fun i => {g | Objects.CorrectedEvent.regGood C (D g) (regRadius base i) w}
  have hr : ∀ i, 0 < r i := fun i => mul_pos (by norm_num) (regRadius_pos base hb i)
  have hanti : Antitone r := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (regRadius_antitone base hb hij) (by norm_num)
  have hratio : ∀ i, r (i+1)/r i ≤ (1/4 : ℝ) := by
    intro i
    have heq : r (i+1)/r i = regRadius base (i+1)/regRadius base i := by
      dsimp [r]
      have hri : regRadius base i ≠ 0 := (regRadius_pos base hb i).ne'
      field_simp
    rw [heq]
    exact regRadius_ratio base hb i
  have hloc : ∀ i, AEEventIn μ
      (fieldSigma (fun g => LQGMetric.addConst g (-LQGMetric.circleAvg g (r i) w))
        (annulus w ((1/4 : ℝ) * r i) ((3/4 : ℝ) * r i))) (E i) := by
    intro i
    have hs := regRadius_pos base hb i
    have hclosed := aeEventIn_regGood_closed0 μ hμ ξ Q D hD C w (regRadius base i) hs
    obtain ⟨F, hFm, hEF⟩ := hclosed
    exact ⟨F, (Toolkit.AnnulusIteration.fieldSigmaClosed0_le_centered_open id
      (fun g => -LQGMetric.circleAvg g (r i) w)
      (BiLipschitz.Barrier.closedAnn w (regRadius base i) (2 * regRadius base i))
      (annulus w ((1/4 : ℝ) * r i) ((3/4 : ℝ) * r i))
      (closedAnn_compact w (regRadius base i))
      (closedAnn_subset_iterAnn w (regRadius base i) hs)) F hFm, hEF⟩
  have hprob : ∀ i, ENNReal.ofReal p ≤ μ (E i) := by
    intro i
    exact hmarg C hC w ⟨regRadius base i, regRadius_pos base hb i⟩
  exact hLM μ id hμ.1 w r E hr hanti hratio hloc hprob K

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
