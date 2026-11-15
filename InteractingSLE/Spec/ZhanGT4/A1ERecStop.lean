/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EFamWire

/-!
# Zhan's A.1, record facts: generic stopped-σ-algebra and stop-congruence lemmas

Packet PROVE-A1-EIGHTREC. Generic lemmas used by the record facts of the A.1 directional family laws (A1-RECTLAW2's
`ResStopInput`/`ResStopInputFst`): the records are stopped σ-algebras `𝓕_{τ ∧ S}` of a usual augmentation, while the
caps, image drivers and image forces read the stop `τ` itself. Where the cap is positive the frozen hull is protected
(`τ ≤ S`), so `τ` may be replaced by `τ ∧ S`, which is measurable for the record.

* `IsStoppingTime.measurableSpace_eq_of_eq`: equal stopping times have equal stopped σ-algebras;
* **`measurable_stop_nnreal`**: an `ℝ≥0`-valued stopping time is measurable for its own stopped σ-algebra;
* **`isStoppingTime_min_nnreal`**, **`measurableSpace_min_nnreal`**: `τ ∧ S` as an `ℝ≥0`-valued stopping time, with
  the stopped σ-algebra of Mathlib's `hτ.min hS`;
* **`measurableSet_le_min_nnreal`**, **`measurableSet_min_le_nnreal`**: the gates `{τ ≤ S}` and `{τ ∧ S ≤ S'}`;
* **`measurable_stoppedValue_nnreal`**: a progressive process read at an `ℝ≥0`-valued stopping time;
* **`measurableSet_stop_of_null`**: conull measurable sets are events of every stopped σ-algebra of a usual
  augmentation;
* `rDrvFst_congr_stop`, `rForceFst_congr_stop`, `capFst_congr_stop`: the large-direction canonical data read the stop
  only at the sample.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ERec

open A1Forces A1Core

/-! ### Stopped σ-algebras of `ℝ≥0`-valued stopping times -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Equal stopping times have equal stopped σ-algebras.** -/
theorem _root_.MeasureTheory.IsStoppingTime.measurableSpace_eq_of_eq {τ τ' : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓕 τ) (hτ' : IsStoppingTime 𝓕 τ') (h : τ = τ') :
    hτ.measurableSpace = hτ'.measurableSpace := by
  subst h; rfl

/-- **An `ℝ≥0`-valued stopping time is measurable for its stopped σ-algebra.** -/
theorem measurable_stop_nnreal {S : Ω → ℝ≥0} (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    Measurable[hS.measurableSpace] S := by
  refine measurable_of_Iic (mδ := hS.measurableSpace) fun x => ?_
  have e : S ⁻¹' Iic x = (fun ω => (S ω : WithTop ℝ≥0)) ⁻¹' Iic (x : WithTop ℝ≥0) := by
    ext ω; simp only [mem_preimage, mem_Iic, WithTop.coe_le_coe]
  rw [e]
  exact hS.measurable measurableSet_Iic

/-- The minimum of two `ℝ≥0`-valued stopping times, as an `ℝ≥0`-valued stopping time. -/
theorem isStoppingTime_min_nnreal {τ S : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓕 fun ω => ((min (τ ω) (S ω) : ℝ≥0) : WithTop ℝ≥0) := by
  have e : (fun ω => ((min (τ ω) (S ω) : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => min ((τ ω : ℝ≥0) : WithTop ℝ≥0) (S ω : WithTop ℝ≥0) := by
    funext ω; exact WithTop.coe_min _ _
  rw [e]
  exact hτ.min hS

/-- **The stopped σ-algebra of `τ ∧ S`** read as an `ℝ≥0`-valued stopping time is Mathlib's `(hτ.min hS)`. -/
theorem measurableSpace_min_nnreal {τ S : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    (isStoppingTime_min_nnreal hτ hS).measurableSpace = (hτ.min hS).measurableSpace :=
  IsStoppingTime.measurableSpace_eq_of_eq _ _ (funext fun _ => WithTop.coe_min _ _)

/-- **The protection gate `{τ ≤ S}` is an event of `𝓕_{τ ∧ S}`.** -/
theorem measurableSet_le_min_nnreal {τ S : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    MeasurableSet[(hτ.min hS).measurableSpace] {ω | τ ω ≤ S ω} := by
  have h := IsStoppingTime.measurableSet_stopping_time_le_min hτ hS
  have e : {ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (S ω : WithTop ℝ≥0)} = {ω | τ ω ≤ S ω} := by
    ext ω; simp only [mem_ofPred_eq, WithTop.coe_le_coe]
  rwa [e] at h

/-- **A gate `{τ ∧ S ≤ S'}` against another stopping time is an event of `𝓕_{τ ∧ S}`.** -/
theorem measurableSet_min_le_nnreal {τ S S' : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hS' : IsStoppingTime 𝓕 fun ω => (S' ω : WithTop ℝ≥0)) :
    MeasurableSet[(hτ.min hS).measurableSpace] {ω | min (τ ω) (S ω) ≤ S' ω} := by
  have h := IsStoppingTime.measurableSet_le_stopping_time (isStoppingTime_min_nnreal hτ hS) hS'
  rw [measurableSpace_min_nnreal hτ hS] at h
  have e : {ω | ((min (τ ω) (S ω) : ℝ≥0) : WithTop ℝ≥0) ≤ (S' ω : WithTop ℝ≥0)} =
      {ω | min (τ ω) (S ω) ≤ S' ω} := by
    ext ω; simp only [mem_ofPred_eq, WithTop.coe_le_coe]
  rwa [e] at h

/-- **A progressive process read at an `ℝ≥0`-valued stopping time is measurable for the stopped σ-algebra.** -/
theorem measurable_stoppedValue_nnreal {u : ℝ≥0 → Ω → ℝ} (hu : IsStronglyProgressive 𝓕 u) {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    Measurable[hS.measurableSpace] fun ω => u (S ω) ω := by
  have hm := measurable_stoppedValue hu hS
  rwa [A1Canon.stoppedValue_coe] at hm

/-- **Conull measurable sets are events of every stopped σ-algebra of a usual augmentation.** -/
theorem measurableSet_stop_of_null {P : Measure Ω} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) τ) {G : Set Ω} (hG : MeasurableSet G) (hG0 : P Gᶜ = 0) :
    MeasurableSet[hτ.measurableSpace] G := by
  have hGt : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] G := fun t => by
    have h := Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hG.compl hG0 t
    simpa only [compl_compl] using h.compl
  refine (IsStoppingTime.measurableSet hτ G).2 ⟨?_, fun i => (hGt i).inter (hτ i)⟩
  exact (le_iSup (fun t => usualAugmentation 𝓕 P t) 0) _ (hGt 0)

end Stop

/-! ### The canonical large-direction data read the stop only at the sample -/

section Congr

variable {X Y : Type*} {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ}
  {Wk : ℝ≥0 → X → ℝ} {τ τ' : X → ℝ≥0} {z : X × Y}

/-- The masked canonical image driver reads the stop only at the sample. -/
theorem rDrvFst_congr_stop (h : τ z.1 = τ' z.1) (t : ℝ≥0) :
    rDrvFst live xj Wj ζj xk Wk τ t z = rDrvFst live xj Wj ζj xk Wk τ' t z := by
  have hl : live (τ z.1) z.1 ↔ live (τ' z.1) z.1 := by rw [h]
  simp only [rDrvFst, A1Ref.cImgDrvM, A1Ref.cImgDrv, A1Ref.cImgSrc, h]
  by_cases hl' : live (τ' z.1) z.1
  · have hl'' := hl.2 hl'
    simp only [hl', hl'', ↓reduceIte]
  · have hl'' : ¬ live (τ z.1) z.1 := fun h' => hl' (hl.1 h')
    simp only [hl', hl'', ↓reduceIte]

/-- The canonical image force reads the stop only at the sample. -/
theorem rForceFst_congr_stop (h : τ z.1 = τ' z.1) (p : X → ℝ) (t : ℝ≥0) :
    rForceFst live xj Wj ζj xk Wk τ p t z = rForceFst live xj Wj ζj xk Wk τ' p t z := by
  have e₁ := rForceFst_at live xj Wj ζj xk Wk τ (fun _ => p) t z
  have e₂ := rForceFst_at live xj Wj ζj xk Wk τ' (fun _ => p) t z
  rw [h] at e₁
  exact e₁.symm.trans e₂

/-- The cap reads the stop only at the sample. -/
theorem capFst_congr_stop (h : τ z.1 = τ' z.1) (T : X × Y → ℝ) :
    capFst live xj Wj ζj xk Wk τ T z = capFst live xj Wj ζj xk Wk τ' T z := by
  have e₁ := capFst_at live xj Wj ζj xk Wk τ (fun _ => T) z
  have e₂ := capFst_at live xj Wj ζj xk Wk τ' (fun _ => T) z
  rw [h] at e₁
  exact e₁.symm.trans e₂

end Congr

end InteractingSLE.ZhanGT4.A1ERec
