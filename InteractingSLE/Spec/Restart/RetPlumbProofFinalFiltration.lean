/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalCarrier

/-!
# Transporting capacity information to a standard Borel carrier

Packet PROVE-RETPLUMB. The image filtration consists of Borel events whose
preimages are observable at the source time. It preserves adapted coordinates
and lifetime stopping events without revealing the field or future lifetime
at time zero.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
variable {Ω S : Type*} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]

/-- Borel events observable through the reader at the current source time. -/
def retImageFiltration (Y : Ω → S) (𝓗 : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 mS where
  seq t := MeasurableSpace.map Y (𝓗 t) ⊓ mS
  mono' _ _ h := inf_le_inf (MeasurableSpace.map_mono (𝓗.mono h)) le_rfl
  le' _ := inf_le_right

/-- Every event of the image filtration pulls back to a current source event. -/
theorem measurable_retImageFiltration (Y : Ω → S) (𝓗 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    Measurable[𝓗 t, retImageFiltration Y 𝓗 t] Y := by
  intro A hA
  exact hA.1

/-- Borel coordinates whose pullbacks are adapted remain adapted on the carrier. -/
theorem measurable_from_retImageFiltration {E : Type*} [MeasurableSpace E]
    {Y : Ω → S} {𝓗 : Filtration ℝ≥0 mΩ} {t : ℝ≥0} {f : S → E}
    (hf : Measurable f) (hcomp : Measurable[𝓗 t] (f ∘ Y)) :
    Measurable[retImageFiltration Y 𝓗 t] f :=
  fun _ hA => ⟨hcomp hA, hf hA⟩

/-- A Borel random time remains a stopping time when its pullback is one. -/
theorem isStoppingTime_retImageFiltration {Y : Ω → S} {𝓗 : Filtration ℝ≥0 mΩ}
    {V : S → ℝ≥0∞} (hV : Measurable V)
    (hs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V (Y ω) ≤ t}) :
    ∀ t : ℝ≥0, MeasurableSet[retImageFiltration Y 𝓗 t] {s | V s ≤ t} :=
  fun t => ⟨hs t, measurableSet_le hV measurable_const⟩

/-- In particular the compressed continuous driver is strongly adapted, using
its actual coordinate agreement and the original capacity adaptedness. -/
theorem stronglyAdapted_retCanonicalDriver {Y : Ω → RetCanonSpace}
    {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hWa : StronglyAdapted 𝓗 W)
    (he : ∀ ω t, RetCanonSpace.driver t (Y ω) = W t ω) :
    StronglyAdapted (retImageFiltration Y 𝓗) RetCanonSpace.driver := by
  intro t
  apply Measurable.stronglyMeasurable
  apply measurable_from_retImageFiltration (RetCanonSpace.measurable_driver t)
  have hef : (RetCanonSpace.driver t ∘ Y) = W t := funext fun ω => he ω t
  rw [hef]
  exact (hWa t).measurable

end InteractingSLE.Restart.RetAux79
