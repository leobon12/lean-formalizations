/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtCReindex

/-!
# Aux. lemma 55 at time `0`: the reference extension reduced to the two-seed history (R3)

Packet PROVE-LOCEXT-C. LOCEXT-B's named input `ReferenceExtensionStatement κ` asks, for every coupling with an admissible
seed, for an extended reference pair recovering the **original** history stopped at the local stop `S` (the driver,
the merged seed marks and every distant mark). By (R3) (`LocalExtCReindex`) the original history through `S` is a fixed
measurable function `reindexHist` of its **two-seed history** `twoSeedProj 𝒳_S` (driver and merged seed marks), so the
distant marks disappear from the input:

* `HasReferenceExtension.of_ae_eq`: an extended reference pair recovering `Y` recovers every `Y'` that is almost surely
  a measurable function of `(H, Y)`;
* `TwoSeedReferenceExtensionStatement κ` (**named input**, steps 3–6 of Aux. 55 in two-seed form): the extended
  reference pair of `ReferenceExtensionStatement` recovering only the two-seed history `twoSeedProj 𝒳_S`. Through `S`
  the measure change of (HL3) makes the driver and the merged seed marks a two-seed evolution, the recoded field
  `h₀ = T(h)` of (HL8) a stopped two-seed coupling ((HL9)), and Aux. 54 extends it; the reference recovers its own
  two-seed history, so the natural recovery map is `seedProj` (`F (H, y) = seedProj y`);
* **`referenceExtensionStatement_of_twoSeed`**: `TwoSeedReferenceExtensionStatement κ → ReferenceExtensionStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Determination

/-- **An extended reference pair recovering `Y` recovers every measurable function of `(H, Y)`**: if `Y' = g(H, Y)`
almost surely (`g` measurable), an extended reference pair over `(Ω, Q)` recovering `Y` recovers `Y'`. -/
theorem HasReferenceExtension.of_ae_eq {κ rL rR r : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {γ β β' : Type*} [MeasurableSpace γ] [MeasurableSpace β] [MeasurableSpace β'] {H : Ω → γ} {Y : Ω → β}
    {Y' : Ω → β'} (hext : HasReferenceExtension.{u} κ rL rR r Q H Y) (g : γ × β → β') (hg : Measurable g)
    (hY' : ∀ᵐ ω ∂Q, Y' ω = g (H ω, Y ω)) : HasReferenceExtension.{u} κ rL rR r Q H Y' := by
  obtain ⟨T, hT, C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hEQ, hC', G', hG'm, hG'0, hG', F, hFm, hagree⟩ := hext
  refine ⟨T, hT, C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hEQ, hC', G', hG'm, hG'0, hG',
    fun p => g (p.1, F p), hg.comp (measurable_fst.prodMk hFm), ?_⟩
  have h1 : ∀ᵐ p ∂E, Y' p.1 = g (H p.1, Y p.1) := by
    have h2 : ∀ᵐ ω ∂(E.map Prod.fst), Y' ω = g (H ω, Y ω) := by rw [hEQ]; exact hY'
    exact ae_of_ae_map measurable_fst.aemeasurable h2
  filter_upwards [h1, hagree] with p hp1 hp2
  rw [hp1, hp2]

/-- **Named input: the extended reference pair of Aux. lemma 55 in two-seed form** (specification pp. 247–250,
(HL1)–(HL9), with Aux. lemma 54; steps 3–6 of the split in `planning/handoffs/PROVE-AUX52-55.md`). For every coupling of
an ordered force word with an admissible seed and every good event `G` (`S = capStop r G ζ W`, `r = seedRadius xL xR`):
a probability measure `Q` equivalent to `P` ((HL3)) and an extended reference pair over `(Ω, Q)` for the seed weights
`(seedSumL, seedSumR)` and the radius `r`, whose field is the recoded field of (HL8), recovering the **two-seed history**
`twoSeedProj 𝒳_S` of the original coupling (the driver and the merged seed marks through `S`). The distant marks of
`ReferenceExtensionStatement` are recovered from it by (R3) (`referenceExtensionStatement_of_twoSeed`). -/
def TwoSeedReferenceExtensionStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
      ∀ G : Set Ω, MeasurableSet G → P Gᶜ = 0 → (∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) →
      ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ P ≪ Q ∧ Q ≪ P ∧
        HasReferenceExtension.{u} κ (seedSumL xL ρL) (seedSumR xR ρR) (seedRadius xL xR) Q h
          (fun ω => twoSeedProj xL xR
            (stoppedHistory (completedState W VL VR ζ) (capStop (seedRadius xL xR) G ζ W) ω))

/-- **(R3) at time `0`: the two-seed form of the extended reference pair gives LOCEXT-B's named input
`ReferenceExtensionStatement`.** On the good event (of full `Q`-measure, `Q ≪ P`) the original stopped history is
`reindexHist` of its two-seed history (`reindexHist_twoSeedProj_stoppedHistory`). -/
theorem referenceExtensionStatement_of_twoSeed {κ : ℝ} (htwo : TwoSeedReferenceExtensionStatement.{u} κ) :
    ReferenceExtensionStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF hseed Ω mΩ P _ 𝓕 W VL VR B ζ h hC G hGm hG0 hG
  obtain ⟨Q, hQ, hPQ, hQP, hext⟩ := htwo xL xR ρL ρR hF hseed P 𝓕 W VL VR B ζ h hC G hGm hG0 hG
  refine ⟨Q, hQ, hPQ, hQP, hext.of_ae_eq (fun p => reindexHist xL xR (seedRadius xL xR) p.2)
    ((measurable_reindexHist xL xR (seedRadius_pos xL xR)).comp measurable_snd) ?_⟩
  have hGQ : ∀ᵐ ω ∂Q, ω ∈ G := ae_iff.2 (hQP hG0)
  filter_upwards [hGQ] with ω hω
  exact (reindexHist_twoSeedProj_stoppedHistory hF (isSeedRadius_seedRadius xL xR) hseed hG hω).symm

end LocalExt

end InteractingSLE
