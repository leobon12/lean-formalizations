/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcDrv

/-!
# F2b′: measurability in the completed line filtration by freezing under the conditional laws

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B). F2b′'s line filtration is completed:
`lineFiltC P 𝓖 t = mΩ ⊓ aeSigma (𝓖 t) P`. A measurable quantity lies in it as soon as it is frozen under the
conditional laws given `𝓖 t` (`WalkLaw.mem_aeSigma_of_frozen`). Frozen data: retained pasts (`ae_ae_pastMap_eq`), hence
runs of regular families (`ae_ae_run_eq_of_regular`), and every quantity already measurable for the completion
(`ae_ae_mem_iff_of_aeSigma`, `ae_ae_eq_of_measurable_aeSigma`).

* **`measurableSet_inf_aeSigma_of_frozen`**, **`measurable_inf_aeSigma_of_frozen`**: measurable + frozen ⇒ measurable
  for `mΩ ⊓ aeSigma 𝒢 P`;
* `ae_ae_mem_iff_of_aeSigma`, `ae_ae_eq_of_measurable_aeSigma`: completion-measurable ⇒ frozen;
* `ae_ae_pastMap_eq`, `ae_ae_run_eq_of_regular`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open LocalSets Exist.Staged Exist.StagedLaw

section

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **A frozen measurable event is an event of the completion.** -/
theorem measurableSet_inf_aeSigma_of_frozen (h𝒢 : 𝒢 ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s)
    (hfr : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (ω ∈ s ↔ ω₀ ∈ s)) :
    MeasurableSet[mΩ ⊓ aeSigma 𝒢 P] s :=
  ⟨hs, WalkLaw.mem_aeSigma_of_frozen h𝒢 hs (M := univ) (Eventually.of_forall fun _ => mem_univ _)
    (fun _ _ => Iff.rfl) hfr⟩

/-- **A frozen measurable map is measurable for the completion.** -/
theorem measurable_inf_aeSigma_of_frozen {β : Type*} [MeasurableSpace β] (h𝒢 : 𝒢 ≤ mΩ) {Y : Ω → β}
    (hY : Measurable Y) (hfr : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), Y ω = Y ω₀) :
    Measurable[mΩ ⊓ aeSigma 𝒢 P] Y := fun B hB =>
  measurableSet_inf_aeSigma_of_frozen h𝒢 (hY hB) (by
    filter_upwards [hfr] with ω₀ h
    filter_upwards [h] with ω hω
    show Y ω ∈ B ↔ Y ω₀ ∈ B
    rw [hω])

/-- **An event of the completion is frozen.** -/
theorem ae_ae_mem_iff_of_aeSigma (h𝒢 : 𝒢 ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[aeSigma 𝒢 P] s) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (ω ∈ s ↔ ω₀ ∈ s) := by
  obtain ⟨s', hs', he⟩ := hs
  have hmem : ∀ᵐ ω ∂P, (ω ∈ s ↔ ω ∈ s') := he.mem_iff
  filter_upwards [ae_ae_mem_iff (P := P) h𝒢 hs', Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hmem, hmem]
    with ω₀ h1 h2 h3
  filter_upwards [h1, h2] with ω g1 g2
  exact g2.trans (g1.trans h3.symm)

/-- **A map measurable for the completion, with values in a second-countable `T₀` space, is frozen.** -/
theorem ae_ae_eq_of_measurable_aeSigma {β : Type*} [TopologicalSpace β] [SecondCountableTopology β] [T0Space β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (h𝒢 : 𝒢 ≤ mΩ) {Z : Ω → β} (hZ : Measurable[aeSigma 𝒢 P] Z) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), Z ω = Z ω₀ := by
  set 𝓑 := TopologicalSpace.countableBasis β with h𝓑
  have h𝓑c : 𝓑.Countable := TopologicalSpace.countable_countableBasis β
  have h𝓑o : ∀ U ∈ 𝓑, IsOpen U := fun U hU => TopologicalSpace.isOpen_of_mem_countableBasis hU
  have hU : ∀ᵐ ω₀ ∂P, ∀ U ∈ 𝓑, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (Z ω ∈ U ↔ Z ω₀ ∈ U) := by
    rw [ae_ball_iff h𝓑c]
    intro U hU'
    exact ae_ae_mem_iff_of_aeSigma (P := P) h𝒢 (s := Z ⁻¹' U) (hZ (h𝓑o U hU').measurableSet)
  filter_upwards [hU] with ω₀ hω₀
  have hall : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ U ∈ 𝓑, (Z ω ∈ U ↔ Z ω₀ ∈ U) := (ae_ball_iff h𝓑c).2 hω₀
  filter_upwards [hall] with ω hω
  refine ((TopologicalSpace.isBasis_countableBasis β).inseparable_iff.2 fun U hU => hω U hU).eq

end

section Past

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A retained past observed by `𝒢` is frozen under the conditional laws given `𝒢`.** -/
theorem ae_ae_pastMap_eq (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (h𝒢 : 𝒢 ≤ mΩ)
    (hpast : pastSigma κ b jumps spec E k ≤ 𝒢) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), pastMap κ b jumps spec E k ω = pastMap κ b jumps spec E k ω₀ := by
  let := upgradeStandardBorel (PastData k)
  have hpm : Measurable[𝒢] (pastMap κ b jumps spec E k) :=
    (comap_measurable (pastMap κ b jumps spec E k)).mono hpast le_rfl
  exact Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 hpm

/-- **The runs of a regular family observed by `𝒢` are frozen.** -/
theorem ae_ae_run_eq_of_regular (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ} (h𝒢 : 𝒢 ≤ mΩ) (hpast : pastSigma κ b jumps spec E k ≤ 𝒢) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ n, n ≤ k →
      ExplState.run κ b jumps spec (fun j => E j ω) n = ExplState.run κ b jumps spec (fun j => E j ω₀) n := by
  filter_upwards [ae_ae_pastMap_eq (P := P) spec h𝒢 hpast] with ω₀ h
  filter_upwards [h] with ω hω n hn
  exact run_eq_of_pastMap_eq_of_le (spec := spec) (fun j _ ω => hreg j ω) hω hn

end Past

end InteractingSLE.Theorem14.SB.Nc
