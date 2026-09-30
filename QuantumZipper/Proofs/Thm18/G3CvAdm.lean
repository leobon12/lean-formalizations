import QuantumZipper.Proofs.Thm18.G3CvRefl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1c: pushforwards of admissible measures by local conformal maps

`isAdmissibleH_map_g3cv`: if `Φ` is a local conformal map at `b` (`LocConf`), bi-Lipschitz on
`closedBall b ρ` (`BiLip`) and maps `closedBall b ρ ∩ Hbar` into `Hbar`, then `Φ_*μ` is admissible
for every admissible `μ` carried by `closedBall b ρ`: the support is the compact image, and the
singular potential is bounded through the nearest point `x₀` of the disc to `y`:
`‖Φ x − y‖ ≥ ‖Φ x − Φ x₀‖ / 2 ≥ (m/2) ‖x − x₀‖`. Own elementary argument.

`cov_pull_markov'`: `cov_pull_markov` (G3CvCov.lean) with the admissibility hypotheses discharged.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3

variable {Φ : ℂ → ℂ} {b r₀ : ℝ}

theorem isAdmissibleH_map_g3cv (hΦ : LocConf Φ b r₀) {ρ m M : ℝ} (hρr : ρ < r₀)
    (hbl : BiLip Φ b ρ m M) (hup : ∀ z ∈ closedBall (b : ℂ) ρ ∩ Hbar, Φ z ∈ Hbar)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμc : μ (closedBall (b : ℂ) ρ)ᶜ = 0) :
    IsAdmissibleH (μ.map Φ) := by
  have := hμ.1
  obtain ⟨hm, -, hb⟩ := hbl
  set K := closedBall (b : ℂ) ρ with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hΦc : ContinuousOn Φ K :=
    (hΦ.diff.mono (closedBall_subset_ball hρr)).continuousOn
  have hKH : μ (K ∩ Hbar)ᶜ = 0 := by
    rw [compl_inter]
    exact measure_union_null hμc (mem_ae_iff.1 (ae_mem_Hbar_of_admissible hμ))
  refine ⟨inferInstance, ⟨Φ '' (K ∩ Hbar), (hKc.inter_right isClosed_Hbar).image_of_continuousOn
    (hΦc.mono inter_subset_left), fun _ ⟨z, hz, e⟩ => e ▸ hup z hz, ?_⟩, ?_⟩
  · have hcl : IsClosed (Φ '' (K ∩ Hbar)) :=
      ((hKc.inter_right isClosed_Hbar).image_of_continuousOn
        (hΦc.mono inter_subset_left)).isClosed
    rw [Measure.map_apply hΦ.meas hcl.measurableSet.compl]
    exact measure_mono_null (fun x hx h => hx ⟨x, h, rfl⟩) hKH
  · obtain ⟨C, hC, hCb⟩ := hμ.2.2
    refine ⟨C + ENNReal.ofReal (-Real.log (m / 2)) * μ Set.univ,
      ENNReal.add_lt_top.2 ⟨hC, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩,
      fun y => ?_⟩
    rw [lintegral_map (admissible_measurable_logNeg_sub y) hΦ.meas]
    -- the nearest point
    by_cases hKne : ρ < 0
    · have : μ Set.univ = 0 := by
        have hK0 : K = ∅ := closedBall_eq_empty.2 hKne
        rw [hK0, compl_empty] at hμc; exact hμc
      rw [Measure.measure_univ_eq_zero.1 this, lintegral_zero_measure]; exact zero_le
    push Not at hKne
    obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn (nonempty_closedBall.2 hKne)
      ((hΦc.sub continuousOn_const).norm (f := fun x => Φ x - y))
    have hne : ∀ᵐ x ∂μ, x ≠ x₀ := by
      rw [ae_iff]; simpa only [ne_eq, not_not, Set.ofPred_eq_eq_singleton] using
        measure_singleton_of_admissible hμ x₀
    have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (-Real.log ‖Φ x - y‖) ≤
        ENNReal.ofReal (-Real.log ‖x - x₀‖) + ENNReal.ofReal (-Real.log (m / 2)) := by
      filter_upwards [hne, mem_ae_iff.2 hμc] with x hx hxK
      have h1 := (hb x hxK x₀ hx₀).1
      have h2 : ‖Φ x₀ - y‖ ≤ ‖Φ x - y‖ := hmin hxK
      have h3 : ‖Φ x - Φ x₀‖ ≤ ‖Φ x - y‖ + ‖Φ x₀ - y‖ := by
        have := norm_sub_le (Φ x - y) (Φ x₀ - y)
        rwa [sub_sub_sub_cancel_right] at this
      have hxx : 0 < ‖x - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
      have ha : 0 < m / 2 * ‖x - x₀‖ := by positivity
      have hA : m / 2 * ‖x - x₀‖ ≤ ‖Φ x - y‖ := by linarith
      have hApos : 0 < ‖Φ x - y‖ := lt_of_lt_of_le ha hA
      have hlog : -Real.log ‖Φ x - y‖ ≤ -Real.log ‖x - x₀‖ + -Real.log (m / 2) := by
        have := Real.log_le_log ha hA
        rw [Real.log_mul (by positivity) hxx.ne'] at this
        linarith
      exact (ENNReal.ofReal_le_ofReal hlog).trans ENNReal.ofReal_add_le
    calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖Φ x - y‖) ∂μ
        ≤ ∫⁻ x, (ENNReal.ofReal (-Real.log ‖x - x₀‖) + ENNReal.ofReal (-Real.log (m / 2))) ∂μ :=
          lintegral_mono_ae hpt
      _ = ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - x₀‖) ∂μ +
            ENNReal.ofReal (-Real.log (m / 2)) * μ Set.univ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
      _ ≤ _ := by gcongr; exact hCb x₀

end G3Cv
end QuantumZipper
