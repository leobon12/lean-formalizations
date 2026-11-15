/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45LifePredict
import InteractingSLE.Spec.Restart.FCThresholdDriverAEMeas
import InteractingSLE.Spec.Restart.RetAux79Path

/-! # Source driver limits from the retained curve's continuous generator -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open Restart

/-- A pre-lifetime continuous driver agrees with any continuous generator of
the same trace. Freeze strictly after the time under consideration and reuse
the landed inverse-Loewner reader; the terminal hull is never read. -/
theorem driver_eq_before_of_common_trace {w W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < U}) (hw0 : w 0 = 0)
    (hW : Continuous W) (hW0 : W 0 = 0)
    (hg : IsGeneratingTrace w U γ) (hgW : IsGeneratingTrace W U γ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < U) : w t = W t := by
  obtain ⟨s, hts, hsU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hts' : t < s := ENNReal.coe_lt_coe.1 hts
  have hfc : Continuous (LP.freezeAt s w) := LP.continuous_freezeAt
    (hw.mono fun r hr => (ENNReal.coe_le_coe.2 hr).trans_lt hsU)
  have hf0 : LP.freezeAt s w 0 = 0 := by simpa only [LP.freezeAt, min_eq_left (zero_le : (0 : ℝ≥0) ≤ s)] using hw0
  have hfg : IsGeneratingTrace (LP.freezeAt s w) (s : ℝ≥0∞) γ := by
    apply StoppedK2.isGeneratingTrace_congr (w := w) _ (LP.isGeneratingTrace_mono hg hsU.le)
    intro r hr
    simp only [LP.freezeAt, min_eq_left (ENNReal.coe_lt_coe.1 hr).le]
  have h₁ := FCPlumb.fcReadDriver_eq (Γ := fun _ : Unit => γ) (ω := ()) hfc hf0 hfg hts
  have h₂ := FCPlumb.fcReadDriver_eq (Γ := fun _ : Unit => γ) (ω := ()) hW hW0 hgW ht
  simpa only [LP.freezeAt, min_eq_left hts'.le] using h₁.symm.trans h₂

namespace ClockSource
variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- Geometry may supply any continuous generator of the actual trace. Driver
uniqueness then proves the precise finite-left-limit hypothesis of the clock
constructor, even if the supplied driver has arbitrary terminal values. -/
theorem ae_leftLimit_of_continuous_generators
    (hext : ∀ᵐ ω ∂D.P, ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧
      IsGeneratingTrace W (D.U ω) (fun t => D.Γ ω t - D.y)) :
    ∀ᵐ ω ∂D.P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = D.U ω →
      ∃ c : ℝ, Tendsto (D.W₀ · ω) (𝓝[<] T) (𝓝 c) := by
  filter_upwards [D.regular, D.trace, hext] with ω hr hg he T _hT hTU
  obtain ⟨W, hWc, hW0, hWg⟩ := he
  refine ⟨W T, ((hWc.tendsto T).mono_left nhdsWithin_le_nhds).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (driver_eq_before_of_common_trace hr.1 hr.2 hWc hW0 hg hWg
    (by rw [← hTU]; exact ENNReal.coe_lt_coe.2 ht)).symm

end ClockSource
end InteractingSLE.Sec5.Aux61R45
