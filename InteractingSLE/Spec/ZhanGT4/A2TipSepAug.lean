/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part2
import InteractingSLE.Spec.ZhanGT4.A2Part3Pull

/-!
# A.2, part 2, step 1: the dual pair with the image law at usual-augmentation stopping times

Packet PROVE-ZHAN-A2TIPSEP. Source: Astra, *Follow-up proofs and dependency audit*, §A.2 L548–L553
(`source/external/AstraIG1/ig1_followup_proofs.txt`; R38, R53, R70).

The conditional separation (L548–L553) conditions on the large curve stopped at its first hit of a compact set. That
time is a pathwise time of the large driver, which is continuous only almost surely, so it is a stopping time of the
usual augmentation of `𝓕₂` and not of `𝓕₂` itself (PROVE-ZHAN-A2P2). Per R70 the conditional image law is supplied
at the stopping times of the usual augmentation:

* `IsA2DualPairG3Aug`, `IsA2DualPairEightAug`: the dual pair of A2X together with the large-to-small conditional image
  law at every stopping time of `usualAugmentation 𝓕₂ P` (same live event, image source, image word and weights);
* `A2TipSepG3AugStatement`, `A2TipSepEightAugStatement`: A2P2's conditional separation at first hits, for these pairs;
* `A2HullInsideG3AugStatement`, `A2HullInsideEightAugStatement`: A.2 part 2 for these pairs, derived from the former
  by A2P2's countable argument (`a2HullInside…AugStatement_of_tipSepAug`).

The image endpoint input (probability only, about local evolutions of the image word):

* `imgU w ζ`, the union of the image hulls before `ζ`, and `ImageEndpointAlt w ζ b`: either the image hulls form the
  open part of a simple crosscut from the image source `0` to a point beyond the large tip `b`, or the image curve
  stopped prematurely (bounded hulls, closure meeting `ℝ` only at the source, points near the source in the early
  hulls);
* `ImageEndpointG3Statement`, `ImageEndpointEightStatement`: every local evolution of the (G3) / (Eight) image word
  satisfies `ImageEndpointAlt` almost surely on its live event.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

/-! ### Pairs with the augmented image law -/

section Pair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The (G3) dual pair with the image law at usual-augmentation stopping times** (R70): `IsA2DualPairG3` together
with the large-to-small conditional image law at every stopping time of `usualAugmentation 𝓕₂ P`. -/
def IsA2DualPairG3Aug (κ y x : ℝ) (P : Measure Ω) (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ)
    (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞)
    (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ)
    (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞) : Prop :=
  IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
    IsCondImageLaw (kh κ) P (usualAugmentation 𝓕₂ P)
      (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0 W₂ (fun t ω => VL₂ 1 t ω)
      (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω])
      (smallG3RhoL κ) (smallG3RhoR κ)

/-- **The (Eight) dual pair with the image law at usual-augmentation stopping times** (R70). -/
def IsA2DualPairEightAug (κ x : ℝ) (P : Measure Ω) (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞)
    (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ)
    (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞) : Prop :=
  IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
    IsCondImageLaw (kh κ) P (usualAugmentation 𝓕₂ P)
      (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0 W₂ (fun t ω => VL₂ 0 t ω)
      (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ)

end Pair

/-! ### The conditional separation and A.2 part 2 for these pairs -/

/-- **A.2, part 2, step 1, (G3), augmented** (A2P2's `A2TipSepG3Statement` for the pairs of R70). -/
def A2TipSepG3AugStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3Aug κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ L : Set ℂ, IsCompact L → L ⊆ H →
          ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsFirstHit (Strip.extPath (W₂ · ω)) L s →
            Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) s →
              ∀ γ : ℝ → ℂ, IsSmallCrosscut y (W₁ · ω) (ζ₁ ω) γ →
                TipSeparated (Strip.extPath (W₂ · ω)) s (γ '' Ioo 0 1)

/-- **A.2, part 2, step 1, (Eight), augmented.** -/
def A2TipSepEightAugStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEightAug κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ L : Set ℂ, IsCompact L → L ⊆ H →
          ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsFirstHit (Strip.extPath (W₂ · ω)) L s →
            Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) s →
              ∀ γ : ℝ → ℂ, IsSmallCrosscut x (W₁ · ω) (ζ₁ ω) γ →
                TipSeparated (Strip.extPath (W₂ · ω)) s (γ '' Ioo 0 1)

/-- **A.2, part 2, (G3), augmented**: `A2X.A2HullInsideG3Statement` for the pairs of R70. -/
def A2HullInsideG3AugStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3Aug κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ᵐ ω ∂P, ∀ γ : ℝ → ℂ, IsSmallCrosscut y (W₁ · ω) (ζ₁ ω) γ →
          ∃ D : Set ℂ, IsCrosscutDomain D γ ∧ Disjoint (lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) D

/-- **A.2, part 2, (Eight), augmented**: `A2X.A2HullInsideEightStatement` for the pairs of R70. -/
def A2HullInsideEightAugStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEightAug κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ᵐ ω ∂P, ∀ γ : ℝ → ℂ, IsSmallCrosscut x (W₁ · ω) (ζ₁ ω) γ →
          ∃ D : Set ℂ, IsCrosscutDomain D γ ∧ Disjoint (lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) D

/-- **A.2, part 2, (G3), augmented**, from the conditional separation at first hits (A2P2's countable argument). -/
theorem a2HullInsideG3AugStatement_of_tipSepAug {κ : ℝ} (h : A2TipSepG3AugStatement.{u} κ) :
    A2HullInsideG3AugStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hall := ae_forall_goodChain (h hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair)
  filter_upwards [hall, hpair.1.1.2.2.2.2] with ω hω hp γ hγ
  obtain ⟨D, hD⟩ := exists_isCrosscutDomain hγ.1 (by rw [hγ.2.1]; linarith [hγ.2.2.1])
  exact ⟨D, hD, disjoint_lifeHullClosure_of_tipSeparated hp.2.2.2.1 hp.1 hD
    fun F hF s hs hl => hω F hF s hs hl γ hγ⟩

/-- **A.2, part 2, (Eight), augmented**, from the conditional separation at first hits. -/
theorem a2HullInsideEightAugStatement_of_tipSepAug {κ : ℝ} (h : A2TipSepEightAugStatement.{u} κ) :
    A2HullInsideEightAugStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hall := ae_forall_goodChain (h hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair)
  filter_upwards [hall, hpair.1.1.2.2.2.2] with ω hω hp γ hγ
  obtain ⟨D, hD⟩ := exists_isCrosscutDomain hγ.1 (by rw [hγ.2.1]; linarith [hγ.2.2.1])
  exact ⟨D, hD, disjoint_lifeHullClosure_of_tipSeparated hp.2.2.2.1 hp.1 hD
    fun F hF s hs hl => hω F hF s hs hl γ hγ⟩

/-! ### The image endpoint input -/

/-- The union of the hulls of the driver `w` before `ζ`. -/
def imgU (w : ℝ → ℝ) (ζ : ℝ≥0∞) : Set ℂ := ⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ), fwdHull w t

/-- **The two alternatives for the image curve** of the small curve given a large prefix, in image coordinates
(source `0`, large tip `b > 0`): either (crosscut) its hulls before `ζ` form the open part of a simple crosscut from
`0` to a point beyond `b` — the completed image ends strictly between the large tip and `∞` (L548–L551) — or
(premature stop) its hulls stay bounded, their closure meets `ℝ` only at the source, and their points near the source
belong to arbitrarily early hulls (the image curve was stopped before its first force collision, so its trace up to
`ζ` is a simple arc in `ℍ ∪ {0}`). -/
def ImageEndpointAlt (w : ℝ → ℝ) (ζ : ℝ≥0∞) (b : ℝ) : Prop :=
  (∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ γ 0 = 0 ∧ b < (γ 1).re ∧ γ '' Ioo 0 1 = imgU w ζ) ∨
    (Bornology.IsBounded (imgU w ζ) ∧ (∀ u : ℝ, (u : ℂ) ∈ closure (imgU w ζ) → u = 0) ∧
      ∀ t : ℝ, 0 < t → ∃ δ > (0 : ℝ), imgU w ζ ∩ ball 0 δ ⊆ fwdHull w t)

/-- **The image endpoint theorem, (G3)** (L548–L551, probability only): for `4 < κ < 8`, every local integrated
`SLE_{κ̂}` evolution (`κ̂ = 16/κ`) of the (G3) image word — left seed `0` (weight `3κ̂/2 − 4`), right seed `0`
(`2 − κ̂/2`), the image of `x` at `a > 0` (`κ̂ − 4`) and the large tip at `b > a` (`−κ̂/2`), the word `𝓔`-measurable
and random — satisfies `ImageEndpointAlt` almost surely on its live event `F`. The `𝓔` binder comes before `mΩ`
(A2P3's pitfall). -/
def ImageEndpointG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ {Ω : Type u} (𝓔 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Set Ω) (ΘL : Ω → Fin 1 → ℝ) (ΘR : Ω → Fin 3 → ℝ) (𝓖 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 3 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    Restart.StoppedK2.IsRandomWordEvolutionUpTo (kh κ) P 𝓔 F ΘL ΘR (smallG3RhoL κ) (smallG3RhoR κ) 𝓖 W VL VR B ζ →
      (∀ᵐ ω ∂P, ω ∈ F → ΘL ω 0 = 0 ∧ ΘR ω 0 = 0 ∧ 0 < ΘR ω 1 ∧ ΘR ω 1 < ΘR ω 2) →
        ∀ᵐ ω ∂P, ω ∈ F → ImageEndpointAlt (Strip.extPath (W · ω)) (ζ ω) (ΘR ω 2)

/-- **The image endpoint theorem, (Eight)** (L548–L551 with §A.3.1): for `κ ≥ 8`, every local evolution of the (Eight)
image word — left seed `0` (`−κ̂/2`), right seed `0` (`κ̂/2 − 2`) and the large tip at `b > 0` (`−κ̂/2`) — satisfies
`ImageEndpointAlt` almost surely on its live event. -/
def ImageEndpointEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ {Ω : Type u} (𝓔 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Set Ω) (ΘL : Ω → Fin 1 → ℝ) (ΘR : Ω → Fin 2 → ℝ) (𝓖 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 2 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    Restart.StoppedK2.IsRandomWordEvolutionUpTo (kh κ) P 𝓔 F ΘL ΘR (smallEightRhoL κ) (smallEightRhoR κ) 𝓖 W VL VR B
        ζ →
      (∀ᵐ ω ∂P, ω ∈ F → ΘL ω 0 = 0 ∧ ΘR ω 0 = 0 ∧ 0 < ΘR ω 1) →
        ∀ᵐ ω ∂P, ω ∈ F → ImageEndpointAlt (Strip.extPath (W · ω)) (ζ ω) (ΘR ω 1)

end InteractingSLE.ZhanGT4.A2TipSep
