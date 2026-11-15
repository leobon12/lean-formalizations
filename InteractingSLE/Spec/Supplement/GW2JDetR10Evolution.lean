/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootW8Family
import InteractingSLE.Spec.Supplement.LP1Seed

/-!
# Actual finite-force reference evolutions for GW2 comparisons

Theorem 2.2 supplies the reference evolutions in every universe, including
words with nonadmissible far totals. No retained-kernel assertion enters
this construction.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR10

open GW2TipSystem.RootN4 GW2TipSystem.RootW8

/-- Ordered positions suffice for existence; no partial-sum assumption on
the weights is needed for a threshold-killed reference evolution. -/
theorem exists_referenceEvolution {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) :
    ∃ e : EvolutionData.{u} nL nR, e.IsEvolution κ xL ρL xR ρR := by
  obtain ⟨Ω, mΩ, P, _, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    LP.exists_isIntegratedSLEEvolution_ulift.{u} (ρL := ρL) (ρR := ρR) hκ hF
  exact ⟨⟨Ω, mΩ, P, 𝓕, W, VL, VR, B, ζ⟩, hE⟩

/-- One fixed choice of an actual reference evolution for each finite word. -/
def referenceEvolution {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) :
    EvolutionData.{u} nL nR :=
  (exists_referenceEvolution.{u} hκ ρL ρR hF).choose

theorem referenceEvolution_isEvolution {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) :
    (referenceEvolution.{u} hκ ρL ρR hF).IsEvolution κ xL ρL xR ρR :=
  (exists_referenceEvolution.{u} hκ ρL ρR hF).choose_spec

/-- Qualitative near-crossing data determine actual reference laws. In
particular the sequence and limiting integrated evolutions are constructed,
and are not additional mathematical inputs. -/
def qualitativeFamilyOfWords {κ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρLs : ℕ → Fin nL → ℝ) (ρRs : ℕ → Fin nR → ℝ)
    (ρL₀ : Fin nL → ℝ) (ρR₀ : Fin nR → ℝ)
    (mL mR : ℕ) (η : ℝ) (goLeft : Bool) (hη : 0 < η)
    (hxL0 : xL ⟨0, hnL⟩ = 0) (hxR0 : xR ⟨0, hnR⟩ = 0)
    (hxL : ∀ i, xL i ≠ 0 → xL i ≤ -η)
    (hxR : ∀ j, xR j ≠ 0 → η ≤ xR j)
    (hF : IsOrderedForceWord xL xR)
    (hpsL : ∀ i : Fin nL, (i : ℕ) < mL →
      -2 < ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), ρL₀ j)
    (hpsR : ∀ i : Fin nR, (i : ℕ) < mR →
      -2 < ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), ρR₀ j)
    (hρL : Tendsto ρLs atTop (𝓝 ρL₀)) (hρR : Tendsto ρRs atTop (𝓝 ρR₀))
    (horientation :
      (goLeft = true ∧ mR = nR - 1 ∧
        0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ ∧
        xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3 ∧
        (∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3) ∧
        (∑ i, ρL₀ i) = κ - 4 ∧ (∑ j, ρR₀ j) = κ / 2 - 2) ∨
      (goLeft = false ∧ mL = nL - 1 ∧
        xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0 ∧
        3 ≤ xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ ∧
        (∀ j : Fin nR, mR ≤ (j : ℕ) → 3 ≤ xR j) ∧
        (∑ j, ρR₀ j) = κ - 4 ∧ (∑ i, ρL₀ i) = κ / 2 - 2)) :
    QualitativeFamily.{u} κ where
  nL := nL
  nR := nR
  hnL := hnL
  hnR := hnR
  xL := xL
  xR := xR
  ρLs := ρLs
  ρRs := ρRs
  ρL₀ := ρL₀
  ρR₀ := ρR₀
  sequence := fun m => referenceEvolution hκ (ρLs m) (ρRs m) hF
  limit := referenceEvolution hκ ρL₀ ρR₀ hF
  mL := mL
  mR := mR
  η := η
  goLeft := goLeft
  hη := hη
  hxL0 := hxL0
  hxR0 := hxR0
  hxL := hxL
  hxR := hxR
  hF := hF
  hpsL := hpsL
  hpsR := hpsR
  hρL := hρL
  hρR := hρR
  hE := fun m => referenceEvolution_isEvolution hκ (ρLs m) (ρRs m) hF
  hE₀ := referenceEvolution_isEvolution hκ ρL₀ ρR₀ hF
  horientation := horientation

end InteractingSLE.Theorem14.GW2JDetR10
