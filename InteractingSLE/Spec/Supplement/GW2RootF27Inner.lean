/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import LQGMetric.Meas.UM
import Mathlib.MeasureTheory.Measure.Trim

/-!
# Observable inner events for record-determined geometric assertions

Packet PROVE-T14-GW2ROOT2. A geometric assertion need not be globally
measurable. When it is constant on record fibres, every measurable
almost-sure certificate has a measurable record event inside it. The
inner event loses none of the certificate's probability. This implements
the Borel-unit route proposed in PROVE-GW2-FABLE's handoff, section 4.2.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory

namespace InteractingSLE.Theorem14.GW2TipSystem.RootF27

variable {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  [mΞ : MeasurableSpace Ξ] [StandardBorelSpace Ξ]
  {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → Ξ}

/-- A measurable certificate for a fibre-constant assertion can be
enlarged, modulo a null set, to an exact observable subset of that assertion. -/
theorem exists_record_subset (hf : Measurable f) {U A : Set Ω}
    (hU : ∀ x y, f x = f y → x ∈ U → y ∈ U) (hA : MeasurableSet A)
    (hAU : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ U) :
    ∃ V : Set Ω, MeasurableSet[MeasurableSpace.comap f mΞ] V ∧ V ⊆ U ∧
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ V := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hAU)
  let E := A \ N
  have hE : MeasurableSet E := hA.diff hNm
  have hEU : E ⊆ U := by
    intro ω hω
    by_contra hn
    exact hω.2 (hNsub (not_imp.mpr ⟨hω.1, hn⟩))
  have hI := LQGMetric.UMeasurableSet.image hf hE
  obtain ⟨B, hBsub, hBm, hBae⟩ :=
    (hI (P.map f) inferInstance).exists_measurable_subset_ae_eq
  refine ⟨f ⁻¹' B, (comap_measurable f) hBm, ?_, ?_⟩
  · intro ω hω
    obtain ⟨ω', hω'E, heq⟩ := hBsub hω
    exact hU ω' ω heq (hEU hω'E)
  · have hpre := ae_of_ae_map hf.aemeasurable hBae
    have hnotN : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.mp hN0
    filter_upwards [hpre, hnotN] with ω hω hωN hωA
    exact hω.mpr ⟨ω, ⟨hωA, hωN⟩, rfl⟩

/-- The measurable inner core in a specified retained sigma algebra.
Its defining complement is a measurable outer envelope for the trimmed measure. -/
def recordCore (σ : MeasurableSpace Ω) (hle : σ ≤ mΩ) (P : Measure[mΩ] Ω)
    (U : Set Ω) : Set Ω :=
  (toMeasurable (P.trim hle) Uᶜ)ᶜ

omit [StandardBorelSpace Ω] in
theorem measurableSet_recordCore (σ : MeasurableSpace Ω) (hle : σ ≤ mΩ)
    (P : Measure[mΩ] Ω) (U : Set Ω) : MeasurableSet[σ] (recordCore (mΩ := mΩ) σ hle P U) :=
  (measurableSet_toMeasurable (P.trim hle) Uᶜ).compl

omit [StandardBorelSpace Ω] in
theorem recordCore_subset (σ : MeasurableSpace Ω) (hle : σ ≤ mΩ)
    (P : Measure[mΩ] Ω) (U : Set Ω) : recordCore (mΩ := mΩ) σ hle P U ⊆ U := by
  intro ω hω
  by_contra hn
  exact hω (subset_toMeasurable (P.trim hle) Uᶜ hn)

/-- The core preserves every ambient measurable almost-sure certificate
for a record-determined assertion, even when the assertion itself is not measurable. -/
theorem ae_mem_recordCore (hf : Measurable f) {U A : Set Ω}
    (hU : ∀ x y, f x = f y → x ∈ U → y ∈ U) (hA : MeasurableSet A)
    (hAU : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ U) :
    ∀ᵐ ω ∂P, ω ∈ A →
      ω ∈ recordCore (MeasurableSpace.comap f mΞ) hf.comap_le P U := by
  obtain ⟨V, hVm, hVU, hAV⟩ := exists_record_subset hf hU hA hAU
  let σ := MeasurableSpace.comap f mΞ
  let μ := P.trim hf.comap_le
  have hzero : μ (toMeasurable μ Uᶜ ∩ V) = 0 := by
    rw [μ.measure_toMeasurable_inter hVm (measure_ne_top _ _)]
    have he : Uᶜ ∩ V = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hω.1 (hVU hω.2)
    rw [he, measure_empty]
  have hVcore : ∀ᵐ ω ∂P, ω ∈ V → ω ∈ recordCore (mΩ := mΩ) σ hf.comap_le P U := by
    apply ae_of_ae_trim hf.comap_le
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with ω hω hωV
    exact fun hn => hω ⟨hn, hωV⟩
  filter_upwards [hAV, hVcore] with ω hωA hωV hω
  exact hωV (hωA hω)

end InteractingSLE.Theorem14.GW2TipSystem.RootF27
