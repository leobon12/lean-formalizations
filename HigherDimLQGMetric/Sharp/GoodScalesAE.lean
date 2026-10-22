import HigherDimLQGMetric.Sharp.GoodScales
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Almost-sure eventual shell covers along dyadic meshes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

def sharpMesh (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

theorem sharpMesh_pos (n : ℕ) : 0 < sharpMesh n := by unfold sharpMesh; positivity

theorem sharpMesh_lt_one (n : ℕ) : sharpMesh n < 1 := by
  unfold sharpMesh
  have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    nlinarith
  linarith

/-- P4 and Borel–Cantelli: every grid point in the expanding ball eventually
has a good dyadic radius. -/
theorem goodScales_ae_eventually (hA1 : ShellInputA1 d) (hd : 3 ≤ d) :
    ∃ p : ℝ, p < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ E : Rd d → ℝ → Set Ω,
          (∀ z r, 0 < r → AEEventIn P
            (fieldSigma0 h (ann z (r / 4) (4 * r))) (E z r)) →
          (∀ z r, 0 < r → ENNReal.ofReal p ≤ P (E z r)) →
          ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
            ∀ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
                Metric.ball (0 : Rd d) (1 / sharpMesh n),
              ∃ k : ℕ, (sharpMesh n) ^ 2 ≤ 1 / 2 ^ k ∧
                1 / 2 ^ k ≤ sharpMesh n ∧ ω ∈ E w (1 / 2 ^ k) := by
  obtain ⟨p, hp, K, HK⟩ := goodScales_everywhere hA1 hd (by norm_num : (0 : ℝ) < 1)
  refine ⟨p, hp, ?_⟩
  intro Ω _ P _ h hh E hE hpE
  let B : ℕ → Set Ω := fun n =>
    {ω | ∃ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
        Metric.ball (0 : Rd d) (1 / sharpMesh n),
      ∀ k : ℕ, (sharpMesh n) ^ 2 ≤ 1 / 2 ^ k →
        1 / 2 ^ k ≤ sharpMesh n → ω ∉ E w (1 / 2 ^ k)}
  let Kpos : ℝ := max K 0
  have hKpos : 0 ≤ Kpos := le_max_right K 0
  have hP : ∀ n, P (B n) ≤ ENNReal.ofReal (Kpos * sharpMesh n) := by
    intro n
    have hbase := HK P h hh E hE hpE 1 one_pos (sharpMesh n)
      ⟨sharpMesh_pos n, sharpMesh_lt_one n⟩
    have hB : P (B n) ≤ ENNReal.ofReal (K * sharpMesh n) := by
      simpa [B] using hbase
    exact hB.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left K 0) (sharpMesh_pos n).le))
  have hsumR : Summable (fun n => Kpos * sharpMesh n) := by
    have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hshift : Summable (fun n : ℕ => sharpMesh n) := by
      simpa only [sharpMesh, pow_succ] using
        Summable.mul_right (1 / 2 : ℝ) hgeo
    exact Summable.mul_left Kpos hshift
  have hsum : (∑' n, P (B n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hP)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hKpos (sharpMesh_pos n).le) hsumR]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  intro w hw
  by_contra hnot
  push Not at hnot
  exact hn ⟨w, hw, fun k hlow hupp => hnot k hlow hupp⟩

end HigherDimLQGMetric
