/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualWidth

/-!
# A.1.5: the law of a stopped rectangle is the same in every family containing it

Packet PROVE-ZHAN-GT4-A18. Source: Astra, *Follow-up proofs*, §A.1.5 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L417–L419, R38): "For each fixed enclosure pair, all sufficiently late couplings have exactly the same joint law of its
two recorded stopped histories, namely the density from (D6)."

For two families of protected rectangles (`DualHyp` over index types `ι`, `ι'`) of the same pair of Brownian curves,
and a rectangle common to both (`S₁' i' = S₁ i`, `S₂' i' = S₂ i`):

* `DualHyp.measurableSet_stop₁_congr`, `measurableSet_stop₂_congr`: the stopped σ-algebras agree;
* `DualHyp.dualCoupling_rect_congr`: the two stopped dual couplings agree on rectangles `A ×ˢ B` with `A` an event of
  curve `1` stopped at `S₁ i` and `B` an event of curve `2` stopped at `S₂ i` (A17's `dualCoupling_rect` and the width
  independence `rectDens_congr`);
* **`DualHyp.dualCoupling_congr_of_rect`**: they agree on the whole product `F¹_{S₁ i} ⊗ F²_{S₂ i}` of the two stopped
  σ-algebras (π-λ on rectangles).
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

section Dual

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {ι ι' : Type*} [Fintype ι]
  [Fintype ι'] {n : ℕ} {κ : ℝ} {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ}
  {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂} {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {p : Fin n → ℝ}
  {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {Tm : ℝ} {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}
  {H₁' H₂' : ι' → Set ℂ} {δ' q' d' : ι' → ℝ} {Tm' : ℝ} {S₁' : ι' → Ω₁ → ℝ≥0} {S₂' : ι' → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
  (h' : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁' H₂' δ' q' d' p Tm' S₁' S₂')
include h h'

omit [Fintype ι] [Fintype ι'] in
/-- A common rectangle has the same curve-`1` stopped σ-algebra in both families. -/
theorem measurableSet_stop₁_congr {i : ι} {i' : ι'} (h₁ : S₁' i' = S₁ i) {A : Set Ω₁}
    (hA : MeasurableSet[(h.stop₁ i).measurableSpace] A) : MeasurableSet[(h'.stop₁ i').measurableSpace] A := by
  refine ⟨hA.1, fun t => ?_⟩
  have e : {ω | ((S₁' i' ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} = {ω | ((S₁ i ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} := by
    rw [h₁]
  rw [e]
  exact hA.2 t

omit [Fintype ι] [Fintype ι'] in
/-- A common rectangle has the same curve-`2` stopped σ-algebra in both families. -/
theorem measurableSet_stop₂_congr {i : ι} {i' : ι'} (h₂ : S₂' i' = S₂ i) {B : Set Ω₂}
    (hB : MeasurableSet[(h.stop₂ i).measurableSpace] B) : MeasurableSet[(h'.stop₂ i').measurableSpace] B := by
  refine ⟨hB.1, fun t => ?_⟩
  have e : {ω | ((S₂' i' ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} = {ω | ((S₂ i ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} := by
    rw [h₂]
  rw [e]
  exact hB.2 t

/-- **The two stopped dual couplings agree on the rectangles of a common stopped rectangle.** -/
theorem dualCoupling_rect_congr [Nonempty ι] [Nonempty ι'] (rr : Fin n → ℝ) {i : ι} {i' : ι'}
    (h₁ : S₁' i' = S₁ i) (h₂ : S₂' i' = S₂ i) {A : Set Ω₁} {B : Set Ω₂}
    (hA : MeasurableSet[(h.stop₁ i).measurableSpace] A) (hB : MeasurableSet[(h.stop₂ i).measurableSpace] B) :
    dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁' S₂' Tm' (A ×ˢ B) = dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm (A ×ˢ B) := by
  rw [h'.dualCoupling_rect rr i' (h.measurableSet_stop₁_congr h' h₁ hA) (h.measurableSet_stop₂_congr h' h₂ hB),
    h.dualCoupling_rect rr i hA hB]
  exact lintegral_congr fun ω => by rw [h.rectDens_congr h' rr h₁ h₂ ω]

/-- **The two stopped dual couplings agree on the product of the stopped σ-algebras of a common rectangle**
(§A.1.5: the joint law of the two recorded stopped histories of a fixed enclosure pair is the same for every family
containing it). -/
theorem dualCoupling_congr_of_rect [Nonempty ι] [Nonempty ι'] (rr : Fin n → ℝ) {i : ι} {i' : ι'}
    (h₁ : S₁' i' = S₁ i) (h₂ : S₂' i' = S₂ i) {C : Set (Ω₁ × Ω₂)}
    (hC : MeasurableSet[(h.stop₁ i).measurableSpace.prod (h.stop₂ i).measurableSpace] C) :
    dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁' S₂' Tm' C = dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm C := by
  have := h'.isProbabilityMeasure_dualCoupling rr
  have := h.isProbabilityMeasure_dualCoupling rr
  have hle : (h.stop₁ i).measurableSpace.prod (h.stop₂ i).measurableSpace ≤ mΩ₁.prod mΩ₂ :=
    sup_le_sup (MeasurableSpace.comap_mono ((h.stop₁ i).measurableSpace_le))
      (MeasurableSpace.comap_mono ((h.stop₂ i).measurableSpace_le))
  refine ext_on_measurableSpace_of_generate_finite (mΩ₁.prod mΩ₂)
    (image2 (· ×ˢ ·) {s : Set Ω₁ | MeasurableSet[(h.stop₁ i).measurableSpace] s}
      {t : Set Ω₂ | MeasurableSet[(h.stop₂ i).measurableSpace] t}) ?_ hle
    (@generateFrom_prod Ω₁ Ω₂ (h.stop₁ i).measurableSpace (h.stop₂ i).measurableSpace).symm
    (@isPiSystem_prod Ω₁ Ω₂ (h.stop₁ i).measurableSpace (h.stop₂ i).measurableSpace) ?_ hC
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact h.dualCoupling_rect_congr h' rr h₁ h₂ hA hB
  · rw [measure_univ, measure_univ]

end DualHyp

end Dual

end InteractingSLE.ZhanGT4
