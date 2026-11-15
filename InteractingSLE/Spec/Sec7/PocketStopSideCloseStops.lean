/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsFinStop

/-!
# Retaining an ordinary reference stop at the maximum with the pocket stop

PROVE-STRIPSYS38. Aux. 35 compares the pocket stop with countably many ordinary
reference stops. STRIPSYS41's marked Galmarino property is preserved by taking
that maximum and retaining the reference's stopped information. This supplies
its stop hypotheses without field determination or right continuity of an
initially enlarged filtration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketStopWallsFin

/-- Take the maximum with a finite ordinary stopping time and retain its entire
stopped σ-algebra. The original marked-stop information is retained as well. -/
theorem isMarkedStop_max_ordinary {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]
    {ℳ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {X : Ω → 𝒳} {T : Ω → ℝ≥0∞} (hG : IsMarkedStop ℳ 𝓕 X T)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) :
    IsMarkedStop (ℳ ⊔ hτ.measurableSpace) 𝓕 X (fun ω => max (T ω) (τ ω)) := by
  intro σ hσ M hM
  have hσle : hσ.measurableSpace ≤
      MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace := le_sup_right
  let D : Set Ω := {ω | T ω ≤ (σ ω : ℝ≥0∞)} ∩ {ω | τ ω ≤ σ ω}
  have hTσ : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      {ω | T ω ≤ (σ ω : ℝ≥0∞)} := by
    simpa only [inter_univ] using hG σ hσ univ MeasurableSet.univ
  have hτσ : MeasurableSet[hσ.measurableSpace] {ω | τ ω ≤ σ ω} := by
    simpa only [WithTop.coe_le_coe] using hτ.measurableSet_stopping_time_le hσ
  have hD : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace] D :=
    hTσ.inter (hσle _ hτσ)
  have he : {ω | max (T ω) (τ ω : ℝ≥0∞) ≤ (σ ω : ℝ≥0∞)} = D := by
    ext ω
    simp only [D, mem_ofPred_eq, max_le_iff, ENNReal.coe_le_coe, mem_inter_iff]
  rw [he]
  refine @PocketStopWalls.measurableSet_inter_of_sup Ω Ω ℳ
    (MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace) hτ.measurableSpace D hD
    id (fun F hF => ?_) (fun F hF => ?_) M (by
      change MeasurableSet[MeasurableSpace.comap (@id Ω) ℳ ⊔ hτ.measurableSpace] M
      rw [MeasurableSpace.comap_id]
      exact hM)
  · have h := (hG σ hσ F hF).inter (hσle _ hτσ)
    convert h using 1
    ext ω
    simp only [D, mem_inter_iff, mem_preimage, id_eq]
    tauto
  · have hF' : MeasurableSet[hσ.measurableSpace] (F ∩ {ω | τ ω ≤ σ ω}) := by
      have h := IsStoppingTime.measurableSpace_mono (hτ.min hσ) hσ
        (fun ω => min_le_right _ _) _ (hτ.measurableSet_inter_le hσ F hF)
      simpa only [WithTop.coe_le_coe] using h
    convert hTσ.inter (hσle _ hF') using 1
    ext ω
    simp only [D, mem_inter_iff]
    tauto

/-- The global-information inclusion required by STRIPSYS41 also survives this
maximum: a stopped ordinary σ-algebra is contained in the full driving history. -/
theorem marked_max_information_le {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]
    {ℳ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {X : Ω → 𝒳} (hS0 : ℳ ≤ MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) :
    ℳ ⊔ hτ.measurableSpace ≤ MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t :=
  sup_le hS0 (hτ.measurableSpace_le'.trans le_sup_right)

/-- Adding ordinary reference information commutes with forming the relative
prefix σ-algebra; this is just associativity and commutativity of the join. -/
theorem locPrefixSigma_sup_info {Ω : Type*} (𝓦 ℳ : MeasurableSpace Ω)
    (A : Set Ω) (γ : Ω → ℝ → ℂ) (q : ℝ≥0) :
    PocketCoupling.locPrefixSigma (𝓦 ⊔ ℳ) A γ q =
      PocketCoupling.locPrefixSigma 𝓦 A γ q ⊔ ℳ := by
  unfold PocketCoupling.locPrefixSigma
  ac_rfl

end InteractingSLE.Sec7.PocketStopSide
