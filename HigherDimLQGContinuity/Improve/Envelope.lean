import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Events.RefsProb

/-!
# A deterministic source envelope with uniform confidence

This is the envelope part of Step 0 (P2) in the proof of Proposition 3.5.
The same threshold works for every parameter and strong metric in the window.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Metric Set MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The random envelope in Lemma 2.1 can be replaced by one deterministic
threshold, uniformly over the parameter window. -/
theorem q11_envelope_prob {d : ℕ} {ξbar s R ε : ℝ}
    (hR : 1 ≤ R) (hε : 0 < ε)
    (hU : UniformEstimates d ξbar s) :
    ∃ H σ β : ℝ, 1 ≤ H ∧ 0 < σ ∧ σ < 1 ∧ 1 < β ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d s {g | ¬ ((∀ z ∈ closedBall (0 : Rd d) R,
              ∀ r ∈ Ioc (0 : ℝ) 1,
                diamIn (rho D g) (ball z (2 * r)) (ball z r) ≤
                  ENNReal.ofReal (H * r ^ σ)) ∧
            (∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
              H⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y)))} ≤
            ENNReal.ofReal ε := by
  obtain ⟨p, σ, β, C, A, hp, hσ, hσ1, hβ, hC, hA, henv⟩ := hU.envelope
  let I : ℝ := C * (1 + R) ^ A
  let H : ℝ := max 1 ((I / ε) ^ p⁻¹)
  have hI : 0 < I := by dsimp [I]; positivity
  have hH1 : 1 ≤ H := le_max_left _ _
  have hH0 : 0 < H := lt_of_lt_of_le one_pos hH1
  have hIp : I / ε ≤ H ^ p := by
    calc I / ε = ((I / ε) ^ p⁻¹) ^ p :=
          (Real.rpow_inv_rpow (div_nonneg hI.le hε.le) hp.ne').symm
      _ ≤ H ^ p := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hp.le
  refine ⟨H, σ, β, hH1, hσ, hσ1, hβ, ?_⟩
  intro ξ hξ D hD
  obtain ⟨Hr, hHrMeas, hHr1, hMoment, hAlmost⟩ := henv ξ hξ D hD R hR
  let B : Set (DistRd d) := {g | ENNReal.ofReal (H ^ p) ≤ ENNReal.ofReal (Hr g ^ p)}
  let N : Set (DistRd d) := {g | ¬ ((∀ z ∈ closedBall (0 : Rd d) R,
      ∀ r ∈ Ioc (0 : ℝ) 1,
        diamIn (rho D g) (ball z (2 * r)) (ball z r) ≤
          ENNReal.ofReal (Hr g * r ^ σ)) ∧
    (∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
      (Hr g)⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y)))}
  have hN : pinLaw d s N = 0 := ae_iff.mp hAlmost
  have hB : pinLaw d s B ≤ ENNReal.ofReal ε := by
    have hmk := p5b_markov (μ := pinLaw d s)
      (f := fun g => ENNReal.ofReal (Hr g ^ p))
      (ENNReal.measurable_ofReal.comp (hHrMeas.pow_const p)).aemeasurable
      (Real.rpow_pos_of_pos hH0 p) hMoment
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hH0 p)]
    rw [div_le_iff₀ hε] at hIp
    simpa only [I, mul_comm ε] using hIp
  have hsub : {g | ¬ ((∀ z ∈ closedBall (0 : Rd d) R,
              ∀ r ∈ Ioc (0 : ℝ) 1,
                diamIn (rho D g) (ball z (2 * r)) (ball z r) ≤
                  ENNReal.ofReal (H * r ^ σ)) ∧
            (∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
              H⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y)))} ⊆ N ∪ B := by
    intro g hg
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨hNg, hBg⟩ := hnot
    have hHg : Hr g ≤ H := by
      by_contra hh
      push Not at hh
      apply hBg
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hH0.le hh.le hp.le)
    have hGood := not_not.mp hNg
    apply hg
    constructor
    · intro z hz r hr
      exact (hGood.1 z hz r hr).trans
        (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hHg (Real.rpow_nonneg hr.1.le _)))
    · intro x hx y hy
      have hInv : H⁻¹ ≤ (Hr g)⁻¹ :=
        (inv_le_inv₀ hH0 (lt_of_lt_of_le one_pos (hHr1 g))).2 hHg
      exact (mul_le_mul_of_nonneg_right hInv
        (Real.rpow_nonneg (norm_nonneg _) _)).trans (hGood.2 x hx y hy)
  calc
    pinLaw d s {g | ¬ ((∀ z ∈ closedBall (0 : Rd d) R,
              ∀ r ∈ Ioc (0 : ℝ) 1,
                diamIn (rho D g) (ball z (2 * r)) (ball z r) ≤
                  ENNReal.ofReal (H * r ^ σ)) ∧
            (∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
              H⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y)))}
        ≤ pinLaw d s (N ∪ B) := measure_mono hsub
    _ ≤ pinLaw d s N + pinLaw d s B := measure_union_le _ _
    _ ≤ ENNReal.ofReal ε := by simpa only [hN, zero_add] using hB

end HigherDimLQGContinuity
