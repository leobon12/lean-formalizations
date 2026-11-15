/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6SourceCContact
import InteractingSLE.Spec.Sec7.StripPocketVersions

/-!
# Regular measurable versions of the two original GB6 drivers

These adapters use only killed-process measurability and the existing
canonical trace evaluation. They assume the original a.e. trace and path
regularity facts, without imposing measurability on the given traces.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.SourceC

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

/-- A common measurable full-measure event contained in any a.e. good event. -/
theorem exists_measurable_good {Good : Ω → Prop} (hgood : ∀ᵐ ω ∂P, Good ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧ ∀ ω ∈ G, Good ω := by
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  exact ⟨Nᶜ, hNm.compl, measure_eq_zero_iff_ae_notMem.1 hN0,
    fun ω hω => by by_contra hn; exact hω (hN hn)⟩

/-- A driver with a.e. infinite life has a measurable continuous version,
equal to the original entire path almost surely. -/
theorem exists_top_driver_version (hWa : AdaptedBefore 𝓕 ζ W)
    (hreg : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (W · ω)) :
    ∃ V : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (V t)) ∧ (∀ ω, Continuous (V · ω)) ∧
      (∀ ω, V 0 ω = 0) ∧ ∀ᵐ ω ∂P, ∀ t, V t ω = W t ω := by
  classical
  obtain ⟨G, hGm, hGae, hG⟩ := exists_measurable_good hreg
  let V : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then Girsanov.killed ζ W t ω else 0
  have hV : ∀ ω ∈ G, ∀ t, V t ω = W t ω := by
    intro ω hω t
    dsimp only [V]
    rw [ite_eq_left hω, Girsanov.killed_of_lt (by rw [(hG ω hω).1]; exact ENNReal.coe_lt_top)]
  refine ⟨V, fun t => Measurable.ite hGm ((Girsanov.measurable_killed hWa t).mono (𝓕.le t) le_rfl)
    measurable_const, ?_, ?_, hGae.mono fun ω hω => hV ω hω⟩
  · intro ω
    by_cases hω : ω ∈ G
    · exact ((hG ω hω).2.2).congr (fun t => (hV ω hω t).symm)
    · simpa only [V, hω, ↓reduceIte] using (continuous_const : Continuous fun _ : ℝ≥0 => (0 : ℝ))
  · intro ω
    by_cases hω : ω ∈ G
    · rw [hV ω hω 0, (hG ω hω).2.1]
    · simp only [V, hω, ↓reduceIte]

/-- A measurable version of the counterflow trace, equal to the given trace
as an entire function almost surely. -/
theorem exists_top_trace_version {V : ℝ≥0 → Ω → ℝ} (hVm : ∀ t, Measurable (V t))
    (hVc : ∀ ω, Continuous (V · ω)) (hV0 : ∀ ω, V 0 ω = 0)
    {γ : Ω → ℝ≥0 → ℂ} (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (V · ω) ⊤ (γ ω)) :
    ∃ Γ : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (Γ ω)) ∧ (∀ ω, Γ ω 0 = 0) ∧
      (∀ t, Measurable fun ω => Γ ω t) ∧ ∀ᵐ ω ∂P, Γ ω = γ ω := by
  obtain ⟨Γ, hΓc, hΓ0, -, hΓm, hΓtr⟩ := Sec7.StripPocketVersions.exists_traceVersion
    (measurable_pi_iff.2 hVm) (hγ.mono fun ω hω => ⟨hVc ω, hV0 ω, γ ω, hω⟩)
  refine ⟨Γ, hΓc, hΓ0, hΓm, ?_⟩
  filter_upwards [hγ, hΓtr] with ω hγ hΓ
  funext t
  exact (LP.traceAt_eq_of_isGeneratingTrace hΓ (hVc ω).continuousOn (hV0 ω) ENNReal.coe_lt_top).symm.trans
    (LP.traceAt_eq_of_isGeneratingTrace hγ (hVc ω).continuousOn (hV0 ω) ENNReal.coe_lt_top)

/-- Measurable globally continuous versions of a driver and its physical
trace prefix through a fixed time. The original trace need not be measurable. -/
theorem exists_prefix_versions (hWa : AdaptedBefore 𝓕 ζ W) {α : Ω → ℝ≥0 → ℂ}
    (hreg : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      IsGeneratingTrace (W · ω) (ζ ω) (α ω)) (s : ℝ≥0) :
    ∃ (V : ℝ≥0 → Ω → ℝ) (A : Ω → ℝ≥0 → ℂ),
      (∀ t, Measurable (V t)) ∧ (∀ ω, Continuous (V · ω)) ∧ (∀ ω, V 0 ω = 0) ∧
      (∀ ω, Continuous (A ω)) ∧ (∀ t, Measurable fun ω => A ω t) ∧ (∀ ω, A ω 0 = 0) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω →
        (∀ t ≤ s, V t ω = W t ω) ∧ ∀ t, A ω t = α ω (min t s) := by
  classical
  obtain ⟨G, hGm, hGae, hG⟩ := exists_measurable_good hreg
  have hsm : MeasurableSet {ω | (s : ℝ≥0∞) < ζ ω} := by
    have h := hWa s univ MeasurableSet.univ
    simp only [mem_univ, and_true] at h
    exact 𝓕.le s _ h
  let E : Set Ω := G ∩ {ω | (s : ℝ≥0∞) < ζ ω}
  have hEm : MeasurableSet E := hGm.inter hsm
  let V : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ E then Girsanov.killed ζ W (min t s) ω else 0
  have hVeq : ∀ ω ∈ E, ∀ t, V t ω = W (min t s) ω := by
    intro ω hω t
    dsimp only [V]
    rw [ite_eq_left hω, Girsanov.killed_of_lt ((ENNReal.coe_le_coe.2 (min_le_right t s)).trans_lt hω.2)]
  have hVm : ∀ t, Measurable (V t) := fun t => Measurable.ite hEm
    ((Girsanov.measurable_killed hWa (min t s)).mono (𝓕.le _) le_rfl) measurable_const
  have hVc : ∀ ω, Continuous (V · ω) := by
    intro ω
    by_cases hω : ω ∈ E
    · exact (((hG ω hω.1).2.1).comp_continuous (continuous_id.min continuous_const)
        (fun t => (ENNReal.coe_le_coe.2 (min_le_right t s)).trans_lt hω.2)).congr (fun t => (hVeq ω hω t).symm)
    · simpa only [V, hω, ↓reduceIte] using (continuous_const : Continuous fun _ : ℝ≥0 => (0 : ℝ))
  have hV0 : ∀ ω, V 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [hVeq ω hω, zero_min, (hG ω hω.1).1]
    · simp only [V, hω, ↓reduceIte]
  let A : Ω → ℝ≥0 → ℂ := fun ω t => if ω ∈ E then LP.traceAt (min t s) (V · ω) else 0
  have hAeq : ∀ ω ∈ E, ∀ t, A ω t = α ω (min t s) := by
    intro ω hω t
    dsimp only [A]
    rw [ite_eq_left hω, LP.traceAt_congr (w' := (W · ω)) (fun r hr => by
      rw [hVeq ω hω r, min_eq_left (hr.trans (min_le_right t s))])]
    exact LP.traceAt_eq_of_isGeneratingTrace (hG ω hω.1).2.2 (hG ω hω.1).2.1 (hG ω hω.1).1
      ((ENNReal.coe_le_coe.2 (min_le_right t s)).trans_lt hω.2)
  refine ⟨V, A, hVm, hVc, hV0, ?_, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ E
    · exact (((hG ω hω.1).2.2.2.1).comp_continuous (continuous_id.min continuous_const)
        (fun t => (ENNReal.coe_le_coe.2 (min_le_right t s)).trans hω.2.le)).congr (fun t => (hAeq ω hω t).symm)
    · simpa only [A, hω, ↓reduceIte] using (continuous_const : Continuous fun _ : ℝ≥0 => (0 : ℂ))
  · intro t
    exact Measurable.ite hEm ((LP.measurable_traceAt (min t s)).comp (measurable_pi_iff.2 hVm)) measurable_const
  · intro ω
    by_cases hω : ω ∈ E
    · rw [hAeq ω hω 0, zero_min, (hG ω hω.1).2.2.1]
    · simp only [A, hω, ↓reduceIte]
  · filter_upwards [hGae] with ω hω hs
    exact ⟨fun t ht => by rw [hVeq ω ⟨hω, hs⟩ t, min_eq_left ht], hAeq ω ⟨hω, hs⟩⟩

end InteractingSLE.Supp8.GB6.SourceC
