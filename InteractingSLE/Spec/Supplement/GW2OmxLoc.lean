/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkUnionLaw

/-!
# GW2's open lines: marked locality of a larger local set for the field-determined marks of a smaller one

Packet PROVE-GW2-STAGEMEAN, R120 round (localization of the stage mean). Under the conditional law of the earlier
pieces the instance's union (read in the launch chart) contains the kernel union; the latter is marked local for its
own stopped driving σ-algebras, which are field-determined. The larger set inherits these marks:

* **`isHistoryAvoidanceLocal_of_subset`**: if `B` is (unmarked) avoidance local, `A ⊆ B` almost surely, and `A` is
  marked local for field-determined marks `𝓝` recording its avoidance events, then `B` is marked local for `𝓝`
  (for a mark `F`, `{B ∩ U = ∅} ∩ F = {B ∩ U = ∅} ∩ ({A ∩ U = ∅} ∩ F)` almost surely; the second factor is an event of
  the field outside `U`, `WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal`, and is pulled out of the conditional
  expectation given the field).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Omx

open WholeField LocalSets WalkLaw

/-- **A larger avoidance-local set is marked local for the field-determined marks of a smaller marked local set.** -/
theorem isHistoryAvoidanceLocal_of_subset {Ω : Type*} {𝓝 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {A B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B) (hBl : IsAvoidanceLocal B h P)
    (hA𝓝 : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓝] {ω | Disjoint (A ω) U})
    (hdet : 𝓝 ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hAl : IsHistoryAvoidanceLocal 𝓝 A h P) (hAB : ∀ᵐ ω ∂P, A ω ⊆ B ω) :
    IsHistoryAvoidanceLocal 𝓝 B h P := by
  intro U G hUH hG hd F hF
  set S : Set Ω := {ω | Disjoint (B ω) (U : Set ℂ)} with hS
  set E : Set Ω := {ω | Disjoint (A ω) (U : Set ℂ)} ∩ F with hE
  have hEh : MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] E :=
    hdet _ ((hA𝓝 U hUH).inter hF)
  obtain ⟨K, ⟨B', hB', rfl⟩, hEK⟩ := mem_aeSigma_of_isHistoryAvoidanceLocal hhm hAl hUH hG hd hF hEh
  obtain ⟨gB, hgB, hgBe⟩ := hBl U G hUH hG hd
  set Y : Ω → DistOn upperHalfPlaneOpens := fun ω => markovCompl G (h ω) with hY
  set K' : Set Ω := Y ⁻¹' B' with hK'
  have hle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hYm : Measurable[MeasurableSpace.comap h inferInstance] Y :=
    (measurable_markovCompl hG).comp (comap_measurable h)
  have hK'm : MeasurableSet[MeasurableSpace.comap h inferInstance] K' := hYm hB'
  refine ⟨fun x => B'.indicator (fun _ => (1 : ℝ)) x * gB x, (measurable_const.indicator hB').mul hgB, ?_⟩
  -- the marked event is almost surely `S ∩ K'`
  have hset : (S ∩ F : Set Ω) =ᵐ[P] (S ∩ K' : Set Ω) := by
    have h1 : (S ∩ F : Set Ω) =ᵐ[P] (S ∩ E : Set Ω) := by
      filter_upwards [hAB] with ω hω
      apply propext
      simp only [hS, hE, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h' => ⟨h'.1, h'.1.mono_left hω, h'.2⟩, fun h' => ⟨h'.1, h'.2.2⟩⟩
    refine h1.trans ?_
    filter_upwards [hEK] with ω hω
    apply propext
    simp only [mem_inter_iff]
    rw [show (ω ∈ E) = (ω ∈ K') from hω]
  have hind : (S ∩ K').indicator (fun _ => (1 : ℝ)) = K'.indicator (S.indicator fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h1 : ω ∈ S <;> by_cases h2 : ω ∈ K' <;> simp [h1, h2]
  have hSm : MeasurableSet S := hBm (measurableSet_avoid U.isOpen hUH)
  calc P⟦S ∩ F | MeasurableSpace.comap h inferInstance⟧
      =ᵐ[P] P⟦S ∩ K' | MeasurableSpace.comap h inferInstance⟧ :=
        condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hset)
    _ = P[K'.indicator (S.indicator fun _ => (1 : ℝ)) | MeasurableSpace.comap h inferInstance] := by rw [hind]
    _ =ᵐ[P] K'.indicator (P⟦S | MeasurableSpace.comap h inferInstance⟧) :=
        condExp_indicator ((integrable_const (1 : ℝ)).indicator hSm) hK'm
    _ =ᵐ[P] K'.indicator (fun ω => gB (Y ω)) := by
        filter_upwards [hgBe] with ω hω
        by_cases h2 : ω ∈ K'
        · rw [indicator_of_mem h2, indicator_of_mem h2]
          exact hω
        · rw [indicator_of_notMem h2, indicator_of_notMem h2]
    _ = fun ω => B'.indicator (fun _ => (1 : ℝ)) (Y ω) * gB (Y ω) := by
        funext ω
        by_cases h2 : Y ω ∈ B'
        · have : ω ∈ K' := h2
          rw [indicator_of_mem this, indicator_of_mem h2, one_mul]
        · have : ω ∉ K' := h2
          rw [indicator_of_notMem this, indicator_of_notMem h2, zero_mul]

end InteractingSLE.Theorem14.GW2Omx
