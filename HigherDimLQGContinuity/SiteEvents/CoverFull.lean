import HigherDimLQGContinuity.SiteEvents.Cover
import HigherDimLQGContinuity.Caps.FullScales

/-! Choice of local failure probability for the full dyadic window. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HigherDimLQGContinuity
open MeasureTheory Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

private theorem q10_fullScales_decay {d : ℕ} {K p V : ℝ}
    (hK : 1 ≤ K) (hp : 0 ≤ p)
    (hpc : p ≤ (2 : ℝ) ^ (-K * (2 * (d : ℝ) + 2)))
    (hV : 1 ≤ V) :
    Real.exp (2 * (d : ℝ) * V) *
      p ^ (((p4_fullScales V).card : ℝ) / K) ≤
      (2 : ℝ) ^ (2 * (d : ℝ) + 2) * Real.exp (-2 * V) := by
  let A : ℝ := 2 * (d : ℝ) + 2
  let m : ℝ := ((p4_fullScales V).card : ℝ)
  let L : ℝ := Real.log 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hKpos : 0 < K := by linarith
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hm : V / L - 1 ≤ m := p4_fullScales_card hV
  have hmL : V - L ≤ m * L := by
    have h := (div_le_iff₀ hL).mp (show V / L ≤ m + 1 by linarith)
    nlinarith
  have ht : 0 ≤ m / K := by positivity
  have hbase : 0 < (2 : ℝ) ^ (-K * A) := Real.rpow_pos_of_pos (by norm_num) _
  have hmon : p ^ (m / K) ≤ ((2 : ℝ) ^ (-K * A)) ^ (m / K) :=
    Real.rpow_le_rpow hp hpc ht
  have heq : ((2 : ℝ) ^ (-K * A)) ^ (m / K) =
      Real.exp (-A * m * L) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    dsimp [L]
    field_simp
  have hE : -A * m * L ≤ A * (L - V) := by
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hmL)]
  have hdec : p ^ (m / K) ≤ Real.exp (A * (L - V)) := by
    calc
      p ^ (m / K) ≤ ((2 : ℝ) ^ (-K * A)) ^ (m / K) := hmon
      _ = Real.exp (-A * m * L) := heq
      _ ≤ Real.exp (A * (L - V)) := Real.exp_le_exp.mpr hE
  have hident : Real.exp (2 * (d : ℝ) * V) * Real.exp (A * (L - V)) =
      (2 : ℝ) ^ A * Real.exp (-2 * V) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [A, L]
    ring
  calc
    Real.exp (2 * (d : ℝ) * V) * p ^ (m / K) ≤
        Real.exp (2 * (d : ℝ) * V) * Real.exp (A * (L - V)) :=
          mul_le_mul_of_nonneg_left hdec (Real.exp_pos _).le
    _ = (2 : ℝ) ^ A * Real.exp (-2 * V) := hident

/-- Full-window form of (2.10), with local failure threshold
`p_cov = 2^(-K(2d+2))`. -/
theorem cover210_full_ann4 {d : ℕ} (hd : 2 ≤ d) :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧
      ∀ {s s₀ : ℝ}, 1 ≤ s → s ≤ 10 → 1 ≤ s₀ → s₀ ≤ 10 →
      ∀ {E : Set (DistRd d)},
        AEEventIn (pinLaw d s) (fieldSigma0 id (ann 0 (1 / 2) 4)) E →
      ∀ {p W V : ℝ}, 0 ≤ p →
        p ≤ (2 : ℝ) ^ (-K * (2 * (d : ℝ) + 2)) →
        pinLaw d s Eᶜ ≤ ENNReal.ofReal p → 0 ≤ W → 1 ≤ V →
      pinLaw d s₀ {g | ∃ x ∈ closedBall (0 : Rd d) W,
        ∀ k ∈ p4_fullScales V, ∀ j : Fin d → ℤ,
          ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ < p4_radius k / 10 →
          recentre s (p4_radius k)
            (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∉ E} ≤
        ENNReal.ofReal (C * (1 + W) ^ d * Real.exp (-2 * V)) := by
  obtain ⟨K, C₀, hK, hC₀, hcover⟩ := cover210_ann4 hd
  refine ⟨K, C₀ * (2 : ℝ) ^ (2 * (d : ℝ) + 2), hK, ?_, ?_⟩
  · positivity
  intro s s₀ hs hs10 hs₀ hs₀10 E hE p W V hp hpc hpE hW hV
  have hT : ∀ k ∈ p4_fullScales V,
      Real.exp (-2 * V) ≤ p4_radius k ∧ p4_radius k ≤ Real.exp (-V) := by
    intro k hk
    exact (p4_mem_fullScales_iff (by linarith : 0 ≤ V) k).mp hk
  have hbound := hcover hs hs10 hs₀ hs₀10 hE hp hpE hW hV
    (p4_fullScales V) hT
  calc
    pinLaw d s₀ _ ≤ ENNReal.ofReal
      (C₀ * (1 + W) ^ d * Real.exp (2 * (d : ℝ) * V) *
        p ^ (((p4_fullScales V).card : ℝ) / K)) := hbound
    _ ≤ ENNReal.ofReal
        (C₀ * (2 : ℝ) ^ (2 * (d : ℝ) + 2) * (1 + W) ^ d * Real.exp (-2 * V)) := by
      apply ENNReal.ofReal_le_ofReal
      have hdec := q10_fullScales_decay (d := d) hK hp hpc hV
      have hmul : 0 ≤ C₀ * (1 + W) ^ d := by positivity
      have h := mul_le_mul_of_nonneg_left hdec hmul
      nlinarith
end HigherDimLQGContinuity
