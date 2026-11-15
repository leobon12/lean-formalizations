/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TreeExtractAvailable

/-!
# Extraction of the measurable available prefix family from local inputs

The three displayed inputs are finite-prefix regularity, field determination of
the prefix drivers, and field determination of the availability flags. They
remain proof obligations for the actual extreme-angle staged family. No general
Theorem 1.2/1.3 determination result is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513TreeExtract

/-- Continuous measurable versions of all the strictly available finite
extreme-angle prefixes. The output flags agree a.s. with actual availability. -/
theorem extract_prefix_paths_of_inputs {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝒢 : MeasurableSpace Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable[𝒢] h)
    {E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : @PrefixTraceRegularity Ω mΩ P (fun s => {ω | scheduleAvailable E s ω}) E)
    (hF : @PrefixFieldDrivers Ω mΩ P (fun s => {ω | scheduleAvailable E s ω}) h E)
    (hA : @PrefixAvailabilityFieldStatement Ω mΩ P h E) :
    ∃ (A : Schedule → Set Ω) (ξ : Schedule → Ω → ℝ → ℂ),
      (∀ s, MeasurableSet[𝒢] (A s)) ∧
      (∀ s t, Measurable[𝒢] fun ω => ξ s ω t) ∧
      (∀ s ω, Continuous (ξ s ω)) ∧
      (∀ᵐ ω ∂P, ∀ s, ω ∈ A s ↔ scheduleAvailable E s ω) ∧
      ∀ᵐ ω ∂P, ∀ s, scheduleAvailable E s ω → ∀ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (prefixDriver E s ω) (terminal s) η →
          EqOn (ξ s ω) (fun t : ℝ => η t.toNNReal) (Icc 0 (terminal s : ℝ)) := by
  obtain ⟨a, ham, hae⟩ := hA
  let A : Schedule → Set Ω := fun s => {ω | a s (h ω) = true}
  have hAm : ∀ s, MeasurableSet[𝒢] (A s) := fun s =>
    ((ham s).comp hh) (measurableSet_singleton true)
  have hAe : ∀ᵐ ω ∂P, ∀ s, ω ∈ A s ↔ scheduleAvailable E s ω := hae
  have hR' : @PrefixTraceRegularity Ω mΩ P A E := by
    intro s
    filter_upwards [hR s, hAe] with ω hRω hAω ha
    exact hRω ((hAω s).1 ha)
  obtain ⟨D, hDm, hDe⟩ := hF
  have hF' : @PrefixFieldDrivers Ω mΩ P A h E := by
    refine ⟨D, hDm, fun s => ?_⟩
    filter_upwards [hDe s, hAe] with ω hDω hAω ha
    exact hDω ((hAω s).1 ha)
  obtain ⟨ξ, hξm, hξc, hξe⟩ :=
    @exists_available_prefix_paths Ω mΩ P 𝒢 h hh E A hAm hR' hF'
  refine ⟨A, ξ, hAm, hξm, hξc, hAe, ?_⟩
  filter_upwards [hξe, hAe] with ω hξω hAω s hs
  exact hξω s ((hAω s).2 hs)

/-- Every enumerated selected node is an available prefix a.s., and no
available deterministic prefix is omitted by the selection. -/
theorem ae_available_enumeration {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : ℕ → Set Ω} (hA : ∀ᵐ ω ∂P, ∃ n, ω ∈ A n) :
    ∀ᵐ ω ∂P, (∀ n, ω ∈ A (availableIndex A n ω)) ∧
      ∀ n, ω ∈ A n → availableIndex A n ω = n := by
  filter_upwards [hA] with ω hω
  exact ⟨availableIndex_mem hω, fun _ hn => availableIndex_eq_self hn⟩

/-- Actual prefix agreement transfers to the field-measurable versions on
every available root/descendant pair, simultaneously. -/
theorem ae_available_prefix_agreement {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : PrefixTraceRegularity P (fun s => {ω | scheduleAvailable E s ω}) E)
    (hC : PrefixEndpointCompatibility P E) {ξ : Schedule → Ω → ℝ → ℂ}
    (hξ : ∀ᵐ ω ∂P, ∀ s, scheduleAvailable E s ω → ∀ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (prefixDriver E s ω) (terminal s) η →
        EqOn (ξ s ω) (fun t : ℝ => η t.toNNReal) (Icc 0 (terminal s : ℝ))) :
    ∀ᵐ ω ∂P, ∀ n m, scheduleAvailable E (scheduleAt n) ω →
      scheduleAvailable E (scheduleAt (descendantIndex n m)) ω →
      ξ (scheduleAt (descendantIndex n m)) ω (terminal (scheduleAt n)) =
        ξ (scheduleAt n) ω (terminal (scheduleAt n)) := by
  have hRa : ∀ᵐ ω ∂P, ∀ s, ω ∈ {ω | scheduleAvailable E s ω} →
      ContinuousOn (prefixDriver E s ω) {t | (t : ℝ≥0∞) < terminal s} ∧
      prefixDriver E s ω 0 = 0 ∧
      ∃ η, IsGeneratingTrace (prefixDriver E s ω) (terminal s) η := ae_all_iff.2 hR
  filter_upwards [hRa, hC, hξ] with ω hr hc he n m hn hm
  obtain ⟨η, hη⟩ := (hr (scheduleAt n) hn).2.2
  obtain ⟨η', hη'⟩ := (hr (scheduleAt (descendantIndex n m)) hm).2.2
  have ht : (terminal (scheduleAt n) : ℝ) ∈
      Icc 0 (terminal (scheduleAt (descendantIndex n m)) : ℝ) :=
    ⟨(terminal (scheduleAt n)).coe_nonneg, by exact_mod_cast terminal_descendant_le n m⟩
  rw [he _ hm η' hη' ht, he _ hn η hη ⟨(terminal (scheduleAt n)).coe_nonneg, le_rfl⟩]
  simpa only [Real.toNNReal_coe] using hc n m hn hm η η' hη hη'

end InteractingSLE.Sec5.Prop513TreeExtract
