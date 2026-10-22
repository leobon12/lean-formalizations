import HigherDimLQGMetric.Bilip.GridTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Borel–Cantelli turns the sparse-shell grid bound into an eventual cover. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter
open HigherDimLFPP (Rd)
open scoped ENNReal

theorem bilip_goodScales_ae_eventually {d : ℕ} (hd : 2 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d)
        (D₁ D₂ : Ω → ContMetric d), IsNormalizedLGF h P →
        IsXiAdditiveRd ξ P h D₁ D₂ →
      ∀ E : Rd d → ℝ → Set Ω,
        (∀ z r, 0 < r → MeasurableSet[
          fieldSigmaRd (fun ω => l7b_recenter (h ω) r z)
            (shellOpen z ((1 / 4) * r) (4 * r)) ⊔
          famSigmaRd (rescFam ξ h D₁ z r)
            (shellOpen z ((1 / 4) * r) (4 * r)) ⊔
          famSigmaRd (rescFam ξ h D₂ z r)
            (shellOpen z ((1 / 4) * r) (4 * r))] (E z r)) →
        (∀ z r, 0 < r → ENNReal.ofReal p ≤ P (E z r)) →
        ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
          ∀ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
            Metric.ball (0 : Rd d) (1 / sharpMesh n),
            ∃ k : ℕ, (sharpMesh n) ^ 2 ≤ 1 / 2 ^ k ∧
              1 / 2 ^ k ≤ sharpMesh n ∧ ω ∈ E w (1 / 2 ^ k) := by
  classical
  obtain ⟨p, K, hp, hp1, hK, htail⟩ := bilip_gridTail hd
  refine ⟨p, hp, hp1, ?_⟩
  intro ξ Ω mΩ P hProb h D₁ D₂ hh hxi E hE hpE
  let B : ℕ → Set Ω := fun n =>
    if sharpMesh n < 1 / 64 then
      {ω | ∃ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
        Metric.ball (0 : Rd d) (1 / sharpMesh n),
        ∀ k : ℕ, (sharpMesh n) ^ 2 ≤ 1 / 2 ^ k →
          1 / 2 ^ k ≤ sharpMesh n → ω ∉ E w (1 / 2 ^ k)}
    else ∅
  have hP : ∀ n, P (B n) ≤ ENNReal.ofReal (K * (sharpMesh n) ^ 2) := by
    intro n
    by_cases hn : sharpMesh n < 1 / 64
    · simpa only [B, ite_eq_left hn] using
        htail ξ P h D₁ D₂ hh hxi E hE hpE (sharpMesh n) (sharpMesh_pos n) hn
    · simp only [B, ite_eq_right hn, measure_empty]
      exact bot_le
  have hsumR : Summable (fun n => K * (sharpMesh n) ^ 2) := by
    have hgeo : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hshift : Summable (fun n : ℕ => (sharpMesh n) ^ 2) := by
      have h := Summable.mul_right (1 / 4 : ℝ) hgeo
      have heq : (fun n : ℕ => (sharpMesh n) ^ 2) =
          (fun n : ℕ => (1 / 4 : ℝ) ^ n * (1 / 4)) := by
        funext n
        dsimp [sharpMesh]
        calc
          ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 = ((1 / 2 : ℝ) ^ 2) ^ (n + 1) := by
            rw [← pow_mul, ← pow_mul, mul_comm]
          _ = (1 / 4 : ℝ) ^ (n + 1) := by norm_num
          _ = (1 / 4 : ℝ) ^ n * (1 / 4) := by rw [pow_succ]
      rw [heq]
      exact h
    exact Summable.mul_left K hshift
  have hsum : (∑' n, P (B n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hP)
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg hK (sq_nonneg _)) hsumR]
    exact ENNReal.ofReal_ne_top
  have hsmall : ∀ᶠ n : ℕ in atTop, sharpMesh n < 1 / 64 :=
    sharpMesh_tendsto_zero.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω.and hsmall] with n hn
  intro w hw
  by_contra hnot
  push Not at hnot
  have hmem : ω ∈ B n := by
    simp only [B, ite_eq_left hn.2]
    exact ⟨w, hw, fun k hlow hupp => hnot k hlow hupp⟩
  exact hn.1 hmem

end HigherDimLQGMetric
