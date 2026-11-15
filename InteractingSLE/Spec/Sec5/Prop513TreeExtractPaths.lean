/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TreeExtractDrivers

/-!
# Measurable continuous paths for the available finite prefixes

The finite-prefix regularity and R48-safe driver-determination obligations are
kept as named inputs. Unavailable schedules are masked before regularization.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513TreeExtract

/-- The field-determined finite drivers give continuous measurable versions of
all available prefix paths simultaneously. Values of unavailable paths are not
asserted to be generating traces. -/
theorem exists_available_prefix_paths {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝒢 : MeasurableSpace Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable[𝒢] h)
    {E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {A : Schedule → Set Ω}
    (hA : ∀ s, MeasurableSet[𝒢] (A s))
    (hR : @PrefixTraceRegularity Ω mΩ P A E)
    (hF : @PrefixFieldDrivers Ω mΩ P A h E) :
    ∃ ξ : Schedule → Ω → ℝ → ℂ,
      (∀ s t, Measurable[𝒢] fun ω => ξ s ω t) ∧
      (∀ s ω, Continuous (ξ s ω)) ∧
      ∀ᵐ ω ∂P, ∀ s, ω ∈ A s → ∀ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (prefixDriver E s ω) (terminal s) η →
          EqOn (ξ s ω) (fun t : ℝ => η t.toNNReal) (Icc 0 (terminal s : ℝ)) := by
  classical
  obtain ⟨D, hDm, hDe⟩ := hF
  let D' : Schedule → Ω → ℝ≥0 → ℝ := fun s ω => D s (h ω)
  have hD'm : ∀ s, Measurable[𝒢] (D' s) := fun s => (hDm s).comp hh
  let raw : Schedule → Ω → ℝ → ℂ :=
    fun s ω t => if ω ∈ A s then prefixTrace D' s ω t else 0
  have hm : ∀ s t, Measurable[𝒢] fun ω => raw s ω t := fun s t =>
    Measurable.ite (hA s) (measurable_prefixTrace hD'm s t) measurable_const
  have hc : ∀ s, ∀ᵐ ω ∂P, ContinuousOn (raw s ω) (Icc 0 (terminal s : ℝ)) := by
    intro s
    filter_upwards [hR s, hDe s] with ω hRω hDω
    by_cases ha : ω ∈ A s
    · obtain ⟨hw, hw0, η, hη⟩ := hRω ha
      have he : EqOn (raw s ω) (fun t : ℝ => η t.toNNReal)
          (Icc 0 (terminal s : ℝ)) := by
        intro t ht
        simp only [raw, ha, ite_true]
        exact prefixTrace_eq hw hw0 (hDω ha) hη ht
      have htcont : ContinuousOn (fun t : ℝ => η t.toNNReal)
          (Icc 0 (terminal s : ℝ)) :=
        hη.2.1.comp continuous_real_toNNReal.continuousOn (fun t ht => by
          have ht' : t.toNNReal ≤ terminal s := by
            simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2
          exact ENNReal.coe_le_coe.2 ht')
      exact htcont.congr he
    · simp only [raw, ha, ite_false]
      exact continuousOn_const
  have hex := fun s => @exists_continuous_prefix_version Ω mΩ P 𝒢 (raw s)
    (hm s) (terminal s : ℝ) (by exact_mod_cast terminal_pos s) (hc s)
  choose ξ hξm hξc hξe using hex
  refine ⟨ξ, hξm, hξc, ae_all_iff.2 fun s => ?_⟩
  filter_upwards [hξe s, hR s, hDe s] with ω he hRω hDω ha η hη t ht
  rw [he ht]
  simp only [raw, ha, ite_true]
  exact prefixTrace_eq (hRω ha).1 (hRω ha).2.1 (hDω ha) hη ht

end InteractingSLE.Sec5.Prop513TreeExtract
