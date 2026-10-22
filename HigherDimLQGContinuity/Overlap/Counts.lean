import HigherDimLQGContinuity.Overlap.Holder
import HigherDimLQGContinuity.Overlap.Depth

/-!
# Proposition 4.5 from the finite counts (packet Q8b)

This module combines the pinned overlap inequality with the depth arithmetic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Metric

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Proposition 4.5, conditional only on its explicit counting and energy premises. -/
theorem prop45_of_counts_holds {d : ℕ} (hd : 3 ≤ d) : Prop45OfCounts d := by
  classical
  intro α Idx A hA F k m₀ κ μ D₀ M₀ CJ CKJ ℓ hκ hD₀ hM₀ hCJ hCKJ hk hm₀ hℓ
    hF hsupp hcard B hlow hup
  have hρ : 0 < κ / 2 := by positivity
  have hℓCJ : Real.log CJ / D₀ ≤ ℓ :=
    le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hℓ
  have hℓ0 : 0 ≤ ℓ := by
    have hlog : 0 ≤ Real.log CJ := Real.log_nonneg hCJ
    have hdiv : 0 ≤ Real.log CJ / D₀ := div_nonneg hlog hD₀.le
    exact hdiv.trans hℓCJ
  by_cases hμ : μ ≤ -1
  · letI : IsProbabilityMeasure (pinLaw d 10) := isProbabilityMeasure_pinLaw (by omega) 10
    have hrhs : (1 : ℝ) ≤ Real.exp (-(2 * μ + 2) * ℓ) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonneg (by linarith) hℓ0
    calc
      pinLaw d 10 B ≤ (1 : ENNReal) := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * μ + 2) * ℓ)) :=
        ENNReal.ofReal_le_ofReal hrhs
  have hμpos : -1 < μ := lt_of_not_ge hμ
  have hkposR : (0 : ℝ) < k := by
    have hnum : 0 < 4 * μ + 4 := by linarith
    exact (div_pos hnum hρ).trans_le hk
  have hkpos : 0 < k := Nat.cast_pos.mp hkposR
  have hkpow : 0 < (k : ℝ) ^ k := pow_pos hkposR _
  have hL : 0 < Real.exp (m₀ * ℓ / 2) / (k : ℝ) ^ k :=
    div_pos (Real.exp_pos _) hkpow
  by_cases hIdx0 : Idx.card = 0
  · have hIdx : Idx = ∅ := Finset.card_eq_zero.mp hIdx0
    have hempty : B ≤ᵐ[pinLaw d 10] (∅ : Set (DistRd d)) := by
      apply hlow.mono
      intro g hg hB
      have hc := hg hB
      simp only [hIdx, Finset.filter_empty, Finset.card_empty, Nat.cast_zero] at hc
      exact False.elim ((not_le_of_gt hL) hc)
    have hzero : pinLaw d 10 B = 0 :=
      le_zero_iff.mp (by simpa using measure_mono_ae hempty)
    rw [hzero]
    exact bot_le
  have hIdxpos : 0 < (Idx.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hIdx0)
  let F' : Finset α → C(Rd d, ℝ) := fun Z => if Z ∈ Idx then F Z else 0
  have hF' : ∀ Z, IsCMBounded (F' Z) ((k : ℝ) * M₀) := by
    intro Z
    by_cases hZ : Z ∈ Idx
    · simpa [F', hZ] using hF Z hZ
    · have hzero : IsCMBounded (0 : C(Rd d, ℝ)) ((k : ℝ) * M₀) := by
        intro φ
        simp only [ContinuousMap.zero_apply, zero_mul, integral_zero, abs_zero]
        exact mul_nonneg (by positivity) (logNorm_nonneg _)
      simpa [F', hZ] using hzero
  have hsupp' : ∀ Z, tsupport (F' Z) ⊆ ball (0 : Rd d) 4 := by
    intro Z
    by_cases hZ : Z ∈ Idx
    · simpa [F', hZ] using hsupp Z
    · simp [F', hZ]
  have hup' : ∀ᵐ g ∂(pinLaw d 10),
      ((Idx.filter fun Z => addFun g (F' Z) ∈ A Z).card : ℝ) ≤
        CKJ ^ k * (k + 1 : ℝ) ^ k := by
    apply hup.mono
    intro g hg
    have heq := q8b_card_filter_iff Idx
      (fun Z => addFun g (F' Z) ∈ A Z)
      (fun Z => addFun g (F Z) ∈ A Z)
      (fun Z hZ => by simp [F', hZ])
    exact heq.le.trans hg
  have hM : 0 ≤ (k : ℝ) * M₀ := by positivity
  have hU : 0 ≤ CKJ ^ k * (k + 1 : ℝ) ^ k := by positivity
  have hOverlap := (lemma44_pinned_holds hd) Idx A hA F' hM hF' hsupp' hL hU
    B hlow hup'
  have hDepth := q8b_prop45_depth_from_card hκ hD₀ hM₀ hCJ hCKJ hk hm₀
    hkpos hIdxpos hℓ hcard
  have hmin : min (Idx.card : ℝ)
      (Real.exp ((k : ℝ) * M₀ * Real.sqrt (2 * Real.log Idx.card))) ≤
      Real.exp ((k : ℝ) * M₀ * Real.sqrt (2 * Real.log Idx.card)) :=
    min_le_right _ _
  have hratio : 0 ≤
      (CKJ ^ k * (k + 1 : ℝ) ^ k) /
        (Real.exp (m₀ * ℓ / 2) / (k : ℝ) ^ k) := by positivity
  have hmon := mul_le_mul_of_nonneg_left hmin hratio
  calc
    pinLaw d 10 B ≤ ENNReal.ofReal
      (((CKJ ^ k * (k + 1 : ℝ) ^ k) /
          (Real.exp (m₀ * ℓ / 2) / (k : ℝ) ^ k)) *
        min (Idx.card : ℝ)
          (Real.exp ((k : ℝ) * M₀ * Real.sqrt (2 * Real.log Idx.card)))) := hOverlap
    _ ≤ ENNReal.ofReal
      (((CKJ ^ k * (k + 1 : ℝ) ^ k) /
          (Real.exp (m₀ * ℓ / 2) / (k : ℝ) ^ k)) *
        Real.exp ((k : ℝ) * M₀ * Real.sqrt (2 * Real.log Idx.card))) :=
      ENNReal.ofReal_le_ofReal hmon
    _ = ENNReal.ofReal
      (((CKJ ^ k * (k + 1 : ℝ) ^ k) * (k : ℝ) ^ k /
          Real.exp (m₀ * ℓ / 2)) *
        Real.exp ((k : ℝ) * M₀ * Real.sqrt (2 * Real.log Idx.card))) := by
      rw [div_div_eq_mul_div]
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * μ + 2) * ℓ)) :=
      ENNReal.ofReal_le_ofReal hDepth

end HigherDimLQGContinuity
