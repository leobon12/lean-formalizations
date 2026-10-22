import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Events.RefsProb

/-!
# Uniform buffered diameter threshold

The fixed-buffer moment of Lemma 2.1 gives the internal competitor in
Step 0 (P2) of Proposition 3.5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

/-- A fixed buffered internal diameter has a deterministic high-probability
threshold, uniform in the parameter and the strong metric. -/
theorem q11_diameter_prob {d : ℕ} {ξbar s ε : ℝ}
    (hd : 2 ≤ d) (hs : 0 < s) (hε : 0 < ε)
    (hU : UniformEstimates d ξbar s) :
    ∃ M : ℝ, 0 < M ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d s {g | ¬ diamIn (rho D g) (ball 0 9)
              (closedBall (0 : Rd d) 8) ≤ ENNReal.ofReal M} ≤ ENNReal.ofReal ε := by
  obtain ⟨p, hp, hdiam⟩ := hU.diam
  have hopen : IsOpen (ball (0 : Rd d) 9) := isOpen_ball
  have hbounded : Bornology.IsBounded (ball (0 : Rd d) 9) := isBounded_ball
  have hconnected : IsConnected (ball (0 : Rd d) 9) := isConnected_ball (by norm_num)
  have hcompact : IsCompact (closedBall (0 : Rd d) 8) := isCompact_closedBall _ _
  have hsubset : closedBall (0 : Rd d) 8 ⊆ ball 0 9 := by
    intro x hx
    have h := (mem_closedBall.mp hx)
    exact mem_ball.mpr (by linarith)
  obtain ⟨K, hK⟩ := hdiam _ _ hopen hbounded hconnected hcompact hsubset
  let K' : ℝ := max K 1
  let M : ℝ := max 1 ((K' / ε) ^ p⁻¹)
  have hK' : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le one_pos hM1
  have hKM : K' / ε ≤ M ^ p := by
    calc K' / ε = ((K' / ε) ^ p⁻¹) ^ p :=
          (Real.rpow_inv_rpow (div_nonneg hK'.le hε.le) hp.ne').symm
      _ ≤ M ^ p := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hp.le
  refine ⟨M, hM, ?_⟩
  intro ξ hξ D hD
  have hl := p5b_ae_isLength_rho hd hD hs
  have hY := aemeasurable_diamIn_of_ae_length (pinLaw d s) (rho D)
    (measurable_rho hD.measurable) hl hopen hsubset
  let Y : DistRd d → ℝ≥0∞ := fun g => diamIn (rho D g) (ball 0 9) (closedBall (0 : Rd d) 8)
  let B : Set (DistRd d) := {g | ENNReal.ofReal (M ^ p) ≤ Y g ^ p}
  have hB : pinLaw d s B ≤ ENNReal.ofReal ε := by
    have hYp : AEMeasurable (fun g => Y g ^ p) (pinLaw d s) := hY.pow_const p
    have hInt : ∫⁻ g, Y g ^ p ∂(pinLaw d s) ≤ ENNReal.ofReal K' :=
      (hK ξ hξ D hD).trans (ENNReal.ofReal_le_ofReal (le_max_left K 1))
    have hmk := p5b_markov (μ := pinLaw d s) (f := fun g => Y g ^ p)
      hYp (Real.rpow_pos_of_pos hM p) hInt
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hM p)]
    rw [div_le_iff₀ hε] at hKM
    simpa only [mul_comm ε] using hKM
  have hsub : {g | ¬ Y g ≤ ENNReal.ofReal M} ⊆ B := by
    intro g hg
    have hlt : ENNReal.ofReal M < Y g := lt_of_not_ge hg
    change ENNReal.ofReal (M ^ p) ≤ Y g ^ p
    rw [← ENNReal.ofReal_rpow_of_nonneg hM.le hp.le]
    exact ENNReal.rpow_le_rpow hlt.le hp.le
  exact (measure_mono hsub).trans hB

end HigherDimLQGContinuity
