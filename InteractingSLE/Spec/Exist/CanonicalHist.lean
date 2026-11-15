/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalCode
import InteractingSLE.Spec.Coupling.SafeFamily
import InteractingSLE.Spec.Sec7.ContinuityProb5Trial
import InteractingSLE.Spec.Coupling.WholeField2Germ

/-!
# The history code is measurable for the σ-algebra announced at the lifetime

Packet PROVE-FLOWEXIST3 (AUD-3c N1). Let `σₖ` be real stopping times of a filtration `𝓓` announcing the lifetime
`ζ` (`σₖ < ζ` almost surely, and every `t < ζ` lies below some `σₖ`), and `𝒢 = ⋁ₖ 𝓓_{σₖ}` (containing the null sets).

* `measurableSet_announce`: an event of `𝓓_s` contained in `{s < ζ}` is an event of `𝒢` (it is almost surely the
  union of its traces on `{s < σₖ}`, which lie in `𝓓_{σₖ}`);
* hence the killed state of a process adapted before `ζ` (`AdaptedBefore 𝓓 ζ X`) is `𝒢`-measurable, and so is its
  killed-state code;
* **`comap_le_announce`**: a history code `X₀` that is almost surely in `DetSet` and equal to the frozen code of the
  killed history (`frz (codeOf …)`) generates a sub-σ-algebra of `𝒢` (`X₀ = recode (killed-state code)`,
  `Exist.recode_snd`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

open Sec2.Assembly

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓓 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
  {σ : ℕ → Ω → ℝ≥0}

/-- An event of `𝓓_s` inside `{s < ζ}` is an event of the announced σ-algebra `⋁ₖ 𝓓_{σₖ}`. -/
theorem measurableSet_announce (hσ : ∀ k, IsStoppingTime 𝓓 fun ω => (σ k ω : WithTop ℝ≥0))
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[⨆ k, (hσ k).measurableSpace] N)
    (hexh : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ k, t ≤ σ k ω)
    {s : ℝ≥0} {E : Set Ω} (hE : MeasurableSet[𝓓 s] E) (hEζ : ∀ ω ∈ E, (s : ℝ≥0∞) < ζ ω) :
    MeasurableSet[⨆ k, (hσ k).measurableSpace] E := by
  have hℋ : (⨆ k, (hσ k).measurableSpace) ≤ mΩ := iSup_le fun k => (hσ k).measurableSpace_le
  set G : Set Ω := ⋃ k, E ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < (σ k ω : WithTop ℝ≥0)} with hG
  have hGm : MeasurableSet[⨆ k, (hσ k).measurableSpace] G :=
    MeasurableSet.iUnion fun k => le_iSup (fun k => (hσ k).measurableSpace) k _
      (Sec7.Trial.measurableSet_inter_lt (hσ k) hE)
  refine WholeField.measurableSet_of_ae_eq hℋ hnull (𝓓.le s _ hE) hGm ?_
  filter_upwards [hexh] with ω hω
  apply propext
  refine ⟨fun hωE => ?_, fun hωG => ?_⟩
  · obtain ⟨t, hst, htζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hEζ ω hωE)
    obtain ⟨k, hk⟩ := hω t htζ
    refine mem_iUnion.2 ⟨k, hωE, ?_⟩
    change ((s : ℝ≥0) : WithTop ℝ≥0) < (σ k ω : WithTop ℝ≥0)
    exact WithTop.coe_lt_coe.2 (lt_of_lt_of_le (by exact_mod_cast hst) hk)
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hωG
    exact hk.1

/-- A process adapted to `𝓓` before `ζ` is adapted before `ζ` to the constant filtration of the announced σ-algebra. -/
theorem adaptedBefore_announce (hσ : ∀ k, IsStoppingTime 𝓓 fun ω => (σ k ω : WithTop ℝ≥0))
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[⨆ k, (hσ k).measurableSpace] N)
    (hexh : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ k, t ≤ σ k ω) {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓓 ζ X) :
    AdaptedBefore (Filtration.const ℝ≥0 (⨆ k, (hσ k).measurableSpace) le_rfl) ζ X := fun t A hA =>
  measurableSet_announce hσ hnull hexh (hX t A hA) fun _ hω => hω.1

/-- The killed-state code `(ζ, killed W, killed V)` of the history. -/
def killedSCode {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : SCode nL nR :=
  (ζ ω, killedCode W 0 ζ ω, fun i => killedCode (VL i) (xL i) ζ ω, fun j => killedCode (VR j) (xR j) ζ ω)

theorem codeOf_snd {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (B' : ℝ≥0 → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (codeOf xL xR B' W VL VR ζ ω).2 = killedSCode xL xR W VL VR ζ ω := rfl

/-- The killed-state code is measurable for every σ-algebra to which the state is adapted before `ζ`. -/
theorem measurable_killedSCode {nL nR : ℕ} {m : MeasurableSpace Ω} {𝓗 : Filtration ℝ≥0 m}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓗 ζ W) (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j)) : Measurable[m] (killedSCode xL xR W VL VR ζ) :=
  (measurable_lifetime hW).prodMk ((measurable_killedCode hW 0).prodMk
    ((measurable_pi_iff.2 fun i => measurable_killedCode (hVL i) (xL i)).prodMk
      (measurable_pi_iff.2 fun j => measurable_killedCode (hVR j) (xR j))))

/-- **The history code generates a sub-σ-algebra of the announced σ-algebra.** -/
theorem comap_le_announce {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω → ℝ} {X₀ : Ω → XCode nL nR} (hX₀m : Measurable X₀)
    (hX₀ : ∀ᵐ ω ∂P, X₀ ω ∈ DetSet κ xL xR ρL ρR ∧ X₀ ω = frz (codeOf xL xR B' W VL VR ζ ω))
    (hσ : ∀ k, IsStoppingTime 𝓓 fun ω => (σ k ω : WithTop ℝ≥0))
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[⨆ k, (hσ k).measurableSpace] N)
    (hexh : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ k, t ≤ σ k ω)
    (hW : AdaptedBefore 𝓓 ζ W) (hVL : ∀ i, AdaptedBefore 𝓓 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓓 ζ (VR j)) :
    MeasurableSpace.comap X₀ inferInstance ≤ ⨆ k, (hσ k).measurableSpace := by
  have hℋ : (⨆ k, (hσ k).measurableSpace) ≤ mΩ := iSup_le fun k => (hσ k).measurableSpace_le
  have hK : Measurable[⨆ k, (hσ k).measurableSpace] (killedSCode xL xR W VL VR ζ) :=
    measurable_killedSCode xL xR (adaptedBefore_announce hσ hnull hexh hW)
      (fun i => adaptedBefore_announce hσ hnull hexh (hVL i))
      (fun j => adaptedBefore_announce hσ hnull hexh (hVR j))
  rintro _ ⟨T, hT, rfl⟩
  have hRK := (measurable_recode κ ρL ρR xL xR).comp hK
  refine WholeField.measurableSet_of_ae_eq hℋ hnull (hX₀m hT) (hRK hT) ?_
  filter_upwards [hX₀] with ω hω
  have e : X₀ ω = recode κ ρL ρR xL xR (killedSCode xL xR W VL VR ζ ω) := by
    rw [← codeOf_snd xL xR B' W VL VR ω]
    change X₀ ω = recode κ ρL ρR xL xR (frz (codeOf xL xR B' W VL VR ζ ω)).2
    rw [← hω.2]
    exact (recode_snd hκ hω.1).symm
  apply propext
  change X₀ ω ∈ T ↔ recode κ ρL ρR xL xR (killedSCode xL xR W VL VR ζ ω) ∈ T
  rw [e]

end Exist

end InteractingSLE
