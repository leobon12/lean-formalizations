/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2TipSepMain
import InteractingSLE.Spec.ZhanGT4.A1DualStatement

/-!
# A.2, part 2, for dual pairs whose large curve is regular at every sample; A.2 and A.3 rewired

Packet PROVE-ZHAN-A2TIPSEP. Source: Astra, *Follow-up proofs*, §A.2 L537–L561 and §A.1 (R38, R53, R70).

The first-hit times of A.2's countable argument are stopping times of `𝓕₂` itself as soon as the large driver and
its inner mark are continuous before the lifetime **at every sample** (`ae_of_firstHit_of_stop_reg`). This is the
regularity a reference construction can provide on its own space (PROVE-ZHAN-A1DUAL, item (c): "regularize on
`Ω₀`"), and it survives A1DUAL's glue (the pulled-back processes are compositions with the projection). So:

* `IsA2DualPairG3Reg`, `IsA2DualPairEightReg`: the dual pair of A2X with the large driver and its inner mark continuous
  before the lifetime at every sample (no augmentation of the image law is needed);
* `a2TipSepG3RegStatement_of_imageEndpoint`, `a2HullInsideG3RegStatement_of_imageEndpoint` (and Eight): A.2 part 2 for
  these pairs from the image endpoint theorem;
* `A1DualCouplingG3RegRefStatement` / `…RegVerStatement` (and Eight): A1DUAL's reference and version forms with the
  regularity; `a1DualCouplingG3RegVerStatement_of_regRef` (A1DUAL's glue, which keeps the regularity);
* `fourForceCrosscutG3LifeStatement_of_dualRegVer`, `threeForceCrosscutEightStatement_of_dualRegVer`,
  `firstSwallowCrosscutStatement_of_dualRegVer` and their `_of_regRef` and `_of_imageEndpoint` forms: A.2 and A.3
  from these.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

section Pair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The large driver `W₂` and the mark `V` are continuous before the lifetime `ζ₂` at every sample. -/
def IsLargeReg (W₂ V : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) : Prop :=
  ∀ ω, ContinuousOn (W₂ · ω) {t | (t : ℝ≥0∞) < ζ₂ ω} ∧ ContinuousOn (V · ω) {t | (t : ℝ≥0∞) < ζ₂ ω}

/-- **The (G3) dual pair with a large curve regular at every sample.** -/
def IsA2DualPairG3Reg (κ y x : ℝ) (P : Measure Ω) (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ)
    (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞)
    (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ)
    (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞) : Prop :=
  IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧ IsLargeReg W₂ (VL₂ 0) ζ₂

/-- **The (Eight) dual pair with a large curve regular at every sample.** -/
def IsA2DualPairEightReg (κ x : ℝ) (P : Measure Ω) (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞)
    (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ)
    (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞) : Prop :=
  IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧ IsLargeReg W₂ (VL₂ 0) ζ₂

end Pair

/-- **A.2, part 2, step 1, (G3), regular pairs.** -/
def A2TipSepG3RegStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3Reg κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ L : Set ℂ, IsCompact L → L ⊆ H →
          ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsFirstHit (Strip.extPath (W₂ · ω)) L s →
            Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) s →
              ∀ γ : ℝ → ℂ, IsSmallCrosscut y (W₁ · ω) (ζ₁ ω) γ →
                TipSeparated (Strip.extPath (W₂ · ω)) s (γ '' Ioo 0 1)

/-- **A.2, part 2, step 1, (Eight), regular pairs.** -/
def A2TipSepEightRegStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEightReg κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ L : Set ℂ, IsCompact L → L ⊆ H →
          ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsFirstHit (Strip.extPath (W₂ · ω)) L s →
            Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) s →
              ∀ γ : ℝ → ℂ, IsSmallCrosscut x (W₁ · ω) (ζ₁ ω) γ →
                TipSeparated (Strip.extPath (W₂ · ω)) s (γ '' Ioo 0 1)

/-- **A.2, part 2, (G3), regular pairs.** -/
def A2HullInsideG3RegStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3Reg κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ᵐ ω ∂P, ∀ γ : ℝ → ℂ, IsSmallCrosscut y (W₁ · ω) (ζ₁ ω) γ →
          ∃ D : Set ℂ, IsCrosscutDomain D γ ∧ Disjoint (lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) D

/-- **A.2, part 2, (Eight), regular pairs.** -/
def A2HullInsideEightRegStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEightReg κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ᵐ ω ∂P, ∀ γ : ℝ → ℂ, IsSmallCrosscut x (W₁ · ω) (ζ₁ ω) γ →
          ∃ D : Set ℂ, IsCrosscutDomain D γ ∧ Disjoint (lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) D

/-- **A.2, part 2, step 1, (G3), regular pairs**, from the image endpoint theorem. -/
theorem a2TipSepG3RegStatement_of_imageEndpoint {κ : ℝ} (hI : ImageEndpointG3Statement.{u} κ) :
    A2TipSepG3RegStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair L hL hLH
  exact ae_of_firstHit_of_stop_reg hpair.1.1.2.1 (hpair.1.1.2.2.1 0) (fun ω => (hpair.2 ω).1)
    (fun ω => (hpair.2 ω).2)
    (fun τ hτ => ae_tipSeparated_at_stop_G3_of_law hκ4 hκ8 hI hyx hx hpair.1.1 hpair.1.2.2.1 hτ) hL hLH

/-- **A.2, part 2, step 1, (Eight), regular pairs**, from the image endpoint theorem. -/
theorem a2TipSepEightRegStatement_of_imageEndpoint {κ : ℝ} (hI : ImageEndpointEightStatement.{u} κ) :
    A2TipSepEightRegStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair L hL hLH
  exact ae_of_firstHit_of_stop_reg hpair.1.1.2.1 (hpair.1.1.2.2.1 0) (fun ω => (hpair.2 ω).1)
    (fun ω => (hpair.2 ω).2)
    (fun τ hτ => ae_tipSeparated_at_stop_eight_of_law hκ8 hI hx hpair.1.1 hpair.1.2.2.1 hτ) hL hLH

/-- **A.2, part 2, (G3), regular pairs**, from the conditional separation (A2P2's countable argument). -/
theorem a2HullInsideG3RegStatement_of_tipSepReg {κ : ℝ} (h : A2TipSepG3RegStatement.{u} κ) :
    A2HullInsideG3RegStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hall := ae_forall_goodChain (h hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair)
  filter_upwards [hall, hpair.1.1.2.2.2.2] with ω hω hp γ hγ
  obtain ⟨D, hD⟩ := exists_isCrosscutDomain hγ.1 (by rw [hγ.2.1]; linarith [hγ.2.2.1])
  exact ⟨D, hD, disjoint_lifeHullClosure_of_tipSeparated hp.2.2.2.1 hp.1 hD
    fun F hF s hs hl => hω F hF s hs hl γ hγ⟩

/-- **A.2, part 2, (Eight), regular pairs**, from the conditional separation. -/
theorem a2HullInsideEightRegStatement_of_tipSepReg {κ : ℝ} (h : A2TipSepEightRegStatement.{u} κ) :
    A2HullInsideEightRegStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hall := ae_forall_goodChain (h hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair)
  filter_upwards [hall, hpair.1.1.2.2.2.2] with ω hω hp γ hγ
  obtain ⟨D, hD⟩ := exists_isCrosscutDomain hγ.1 (by rw [hγ.2.1]; linarith [hγ.2.2.1])
  exact ⟨D, hD, disjoint_lifeHullClosure_of_tipSeparated hp.2.2.2.1 hp.1 hD
    fun F hF s hs hl => hω F hF s hs hl γ hγ⟩

theorem a2HullInsideG3RegStatement_of_imageEndpoint {κ : ℝ} (hI : ImageEndpointG3Statement.{u} κ) :
    A2HullInsideG3RegStatement.{u} κ :=
  a2HullInsideG3RegStatement_of_tipSepReg (a2TipSepG3RegStatement_of_imageEndpoint hI)

theorem a2HullInsideEightRegStatement_of_imageEndpoint {κ : ℝ} (hI : ImageEndpointEightStatement.{u} κ) :
    A2HullInsideEightRegStatement.{u} κ :=
  a2HullInsideEightRegStatement_of_tipSepReg (a2TipSepEightRegStatement_of_imageEndpoint hI)


/-! ### A.1 with a regular large curve; A.2 and A.3 rewired -/

/-- **A.1 (G3) on one reference space, with a regular large curve**: A1DUAL's `A1DualCouplingG3RefStatement` whose
pair also has the large driver and its inner mark continuous before the lifetime at every sample. -/
def A1DualCouplingG3RegRefStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (μ : Measure Ω₀)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀))
      (W₂ : ℝ≥0 → Ω₀ → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω₀ → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ) (B₂ : ℝ≥0 → Ω₀ → ℝ)
      (ζ₂ : Ω₀ → ℝ≥0∞) (W₁ : ℝ≥0 → Ω₀ → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω₀ → ℝ)
      (B₁ : ℝ≥0 → Ω₀ → ℝ) (ζ₁ : Ω₀ → ℝ≥0∞),
      IsA2DualPairG3Reg κ y x μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **A.1 (Eight) on one reference space, with a regular large curve.** -/
def A1DualCouplingEightRegRefStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (μ : Measure Ω₀)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀))
      (W₂ : ℝ≥0 → Ω₀ → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ) (B₂ : ℝ≥0 → Ω₀ → ℝ)
      (ζ₂ : Ω₀ → ℝ≥0∞) (W₁ : ℝ≥0 → Ω₀ → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω₀ → ℝ)
      (B₁ : ℝ≥0 → Ω₀ → ℝ) (ζ₁ : Ω₀ → ℝ≥0∞),
      IsA2DualPairEightReg κ x μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **A.1 (G3) over a version of every given large curve, with a regular version** (A1DUAL's
`A1DualCouplingG3VerStatement` with `IsA2DualPairG3Reg`). -/
def A1DualCouplingG3RegVerStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 2 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] P 𝓕 W VL VR B ζ →
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (K : Kernel Ω Ω'), IsMarkovKernel K ∧
          ∃ (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω'))) (W₂ : ℝ≥0 → Ω × Ω' → ℝ)
            (VL₂ : Fin 2 → ℝ≥0 → Ω × Ω' → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω × Ω' → ℝ) (B₂ : ℝ≥0 → Ω × Ω' → ℝ)
            (ζ₂ : Ω × Ω' → ℝ≥0∞) (W₁ : ℝ≥0 → Ω × Ω' → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω × Ω' → ℝ)
            (VR₁ : Fin 3 → ℝ≥0 → Ω × Ω' → ℝ) (B₁ : ℝ≥0 → Ω × Ω' → ℝ) (ζ₁ : Ω × Ω' → ℝ≥0∞),
            A1Dual.IsFstVersion (P ⊗ₘ K) W VL VR B ζ W₂ VL₂ VR₂ B₂ ζ₂ ∧
              IsA2DualPairG3Reg κ y x (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **A.1 (Eight) over a version of every given large curve, with a regular version.** -/
def A1DualCouplingEightRegVerStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] P 𝓕 W VL VR B ζ →
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (K : Kernel Ω Ω'), IsMarkovKernel K ∧
          ∃ (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω'))) (W₂ : ℝ≥0 → Ω × Ω' → ℝ)
            (VL₂ : Fin 1 → ℝ≥0 → Ω × Ω' → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω × Ω' → ℝ) (B₂ : ℝ≥0 → Ω × Ω' → ℝ)
            (ζ₂ : Ω × Ω' → ℝ≥0∞) (W₁ : ℝ≥0 → Ω × Ω' → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω × Ω' → ℝ)
            (VR₁ : Fin 2 → ℝ≥0 → Ω × Ω' → ℝ) (B₁ : ℝ≥0 → Ω × Ω' → ℝ) (ζ₁ : Ω × Ω' → ℝ≥0∞),
            A1Dual.IsFstVersion (P ⊗ₘ K) W VL VR B ζ W₂ VL₂ VR₂ B₂ ζ₂ ∧
              IsA2DualPairEightReg κ x (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **The glue keeps the regularity** (A1DUAL's `a1DualCouplingG3VerStatement_of_ref`, same construction): the pulled
back large processes are compositions with the projection, so they are regular at every sample. -/
theorem a1DualCouplingG3RegVerStatement_of_regRef {κ : ℝ} (h : A1DualCouplingG3RegRefStatement κ) :
    A1DualCouplingG3RegVerStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair, hreg⟩ :=
    h hκ4 hκ8 y x hyx hx
  obtain ⟨K, hK, hsnd, hver⟩ := A1Dual.exists_glue_version.{u} (by linarith : (0 : ℝ) < κ)
    (A1Dual.isOrderedForceWord_largeG3 hyx hx) hE hpair.1
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ := P)
  have hπ : Measurable fun z : Ω × ULift.{u} Ω₀ => z.2.down := measurable_down.comp measurable_snd
  have hs : Function.Surjective fun z : Ω × ULift.{u} Ω₀ => z.2.down :=
    fun ω₀ => ⟨(Classical.arbitrary Ω, ⟨ω₀⟩), rfl⟩
  exact ⟨ULift.{u} Ω₀, inferInstance, K, hK, Coupling.filtrationComap 𝓕₂ hπ, Coupling.filtrationComap 𝓕₁ hπ,
    fun t z => W₂ t z.2.down, fun i t z => VL₂ i t z.2.down, fun i t z => VR₂ i t z.2.down,
    fun t z => B₂ t z.2.down, fun z => ζ₂ z.2.down, fun t z => W₁ t z.2.down, fun i t z => VL₁ i t z.2.down,
    fun i t z => VR₁ i t z.2.down, fun t z => B₁ t z.2.down, fun z => ζ₁ z.2.down, hver,
    A1Dual.IsA2DualPairG3.comap hπ hs hsnd hpair, fun z => hreg z.2.down⟩

/-- **The glue keeps the regularity, (Eight).** -/
theorem a1DualCouplingEightRegVerStatement_of_regRef {κ : ℝ} (h : A1DualCouplingEightRegRefStatement κ) :
    A1DualCouplingEightRegVerStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair, hreg⟩ := h hκ8 x hx
  obtain ⟨K, hK, hsnd, hver⟩ := A1Dual.exists_glue_version.{u} (by linarith : (0 : ℝ) < κ)
    (A1Dual.isOrderedForceWord_largeEight hx) hE hpair.1
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ := P)
  have hπ : Measurable fun z : Ω × ULift.{u} Ω₀ => z.2.down := measurable_down.comp measurable_snd
  have hs : Function.Surjective fun z : Ω × ULift.{u} Ω₀ => z.2.down :=
    fun ω₀ => ⟨(Classical.arbitrary Ω, ⟨ω₀⟩), rfl⟩
  exact ⟨ULift.{u} Ω₀, inferInstance, K, hK, Coupling.filtrationComap 𝓕₂ hπ, Coupling.filtrationComap 𝓕₁ hπ,
    fun t z => W₂ t z.2.down, fun i t z => VL₂ i t z.2.down, fun i t z => VR₂ i t z.2.down,
    fun t z => B₂ t z.2.down, fun z => ζ₂ z.2.down, fun t z => W₁ t z.2.down, fun i t z => VL₁ i t z.2.down,
    fun i t z => VR₁ i t z.2.down, fun t z => B₁ t z.2.down, fun z => ζ₁ z.2.down, hver,
    A1Dual.IsA2DualPairEight.comap hπ hs hsnd hpair, fun z => hreg z.2.down⟩

/-- **A.2 (G3)** (`A34.FourForceCrosscutG3LifeStatement κ`) from A.1 over regular versions and A.2's three parts
(part 2 for regular pairs). -/
theorem fourForceCrosscutG3LifeStatement_of_dualRegVer {κ : ℝ} (hA1 : A1DualCouplingG3RegVerStatement.{u} κ)
    (h1 : A2SmallCrosscutG3Statement.{u} κ) (h2 : A2HullInsideG3RegStatement.{u} κ)
    (h3 : A2SmallInHullG3Statement.{u} κ) : A34.FourForceCrosscutG3LifeStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hver, hpair⟩ :=
    hA1 hκ4 hκ8 y x hyx hx P 𝓕 W VL VR B ζ hE
  have hS1 := h1 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.1.2.1
  have hS2 := h2 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hS3 := h3 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.1
  refine ae_of_ae_compProd_fst (K := K) (Q := fun ω => ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧
    0 < (γ 1).re ∧ outerBoundary (lifeHullClosure (W · ω) (VL 0 · ω) (ζ ω)) = γ '' Ioo 0 1) ?_
  filter_upwards [hS1, hS2, hS3, hver] with z hz1 hz2 hz3 hzv
  have e : lifeHullClosure (W₂ · z) (VL₂ 0 · z) (ζ₂ z) = lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1) :=
    A1Dual.lifeHullClosure_congr hzv.1 (fun t ht => (hzv.2 t ht).1) (fun t ht => (hzv.2 t ht).2.1 0)
  show ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧ 0 < (γ 1).re ∧
    outerBoundary (lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1)) = γ '' Ioo 0 1
  rw [← e]
  exact exists_outerBoundary_eq_of_parts hz1 hz2 hz3

/-- **A.2's three-force version (Eight)** (`A35.ThreeForceCrosscutEightStatement κ`) from A.1 over regular versions
and A.2's three parts. -/
theorem threeForceCrosscutEightStatement_of_dualRegVer {κ : ℝ} (hA1 : A1DualCouplingEightRegVerStatement.{u} κ)
    (h1 : A2SmallCrosscutEightStatement.{u} κ) (h2 : A2HullInsideEightRegStatement.{u} κ)
    (h3 : A2SmallInHullEightStatement.{u} κ) : A35.ThreeForceCrosscutEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hver, hpair⟩ :=
    hA1 hκ8 x hx P 𝓕 W VL VR B ζ hE
  have hS1 := h1 hκ8 x hx (P ⊗ₘ K) 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.1.2.1
  have hS2 := h2 hκ8 x hx (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hS3 := h3 hκ8 x hx (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.1
  refine ae_of_ae_compProd_fst (K := K) (Q := fun ω => ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x ∧
    0 < (γ 1).re ∧ outerBoundary (lifeHullClosure (W · ω) (VL 0 · ω) (ζ ω)) = γ '' Ioo 0 1) ?_
  filter_upwards [hS1, hS2, hS3, hver] with z hz1 hz2 hz3 hzv
  have e : lifeHullClosure (W₂ · z) (VL₂ 0 · z) (ζ₂ z) = lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1) :=
    A1Dual.lifeHullClosure_congr hzv.1 (fun t ht => (hzv.2 t ht).1) (fun t ht => (hzv.2 t ht).2.1 0)
  show ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x ∧ 0 < (γ 1).re ∧
    outerBoundary (lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1)) = γ '' Ioo 0 1
  rw [← e]
  exact exists_outerBoundary_eq_of_parts hz1 hz2 hz3

/-- **A.3** (`FirstSwallowCrosscutStatement κ`) from A.1 over regular versions and A.2's three parts in both
configurations. -/
theorem firstSwallowCrosscutStatement_of_dualRegVer {κ : ℝ} (hA1 : A1DualCouplingG3RegVerStatement.{0} κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (h2 : A2HullInsideG3RegStatement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightRegVerStatement.{u} κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (h2' : A2HullInsideEightRegStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  A35.firstSwallowCrosscutStatement_of_A2 (fourForceCrosscutG3LifeStatement_of_dualRegVer hA1 h1 h2 h3)
    (threeForceCrosscutEightStatement_of_dualRegVer hA1' h1' h2' h3')

/-- **A.2 (G3) from one regular reference coupling, the image endpoint theorem and A.2's parts 1 and 3.** -/
theorem fourForceCrosscutG3LifeStatement_of_regRef {κ : ℝ} (hA1 : A1DualCouplingG3RegRefStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{u} κ) (hI : ImageEndpointG3Statement.{u} κ)
    (h3 : A2SmallInHullG3Statement.{u} κ) : A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  fourForceCrosscutG3LifeStatement_of_dualRegVer (a1DualCouplingG3RegVerStatement_of_regRef hA1) h1
    (a2HullInsideG3RegStatement_of_imageEndpoint hI) h3

/-- **A.2 (Eight) from one regular reference coupling, the image endpoint theorem and A.2's parts 1 and 3.** -/
theorem threeForceCrosscutEightStatement_of_regRef {κ : ℝ} (hA1 : A1DualCouplingEightRegRefStatement κ)
    (h1 : A2SmallCrosscutEightStatement.{u} κ) (hI : ImageEndpointEightStatement.{u} κ)
    (h3 : A2SmallInHullEightStatement.{u} κ) : A35.ThreeForceCrosscutEightStatement.{u} κ :=
  threeForceCrosscutEightStatement_of_dualRegVer (a1DualCouplingEightRegVerStatement_of_regRef hA1) h1
    (a2HullInsideEightRegStatement_of_imageEndpoint hI) h3

/-- **A.3 from the two regular reference couplings, the image endpoint theorems and A.2's parts 1 and 3.** -/
theorem firstSwallowCrosscutStatement_of_regRef {κ : ℝ} (hA1 : A1DualCouplingG3RegRefStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (hI : ImageEndpointG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightRegRefStatement κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (hI' : ImageEndpointEightStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  A35.firstSwallowCrosscutStatement_of_A2 (fourForceCrosscutG3LifeStatement_of_regRef hA1 h1 hI h3)
    (threeForceCrosscutEightStatement_of_regRef hA1' h1' hI' h3')

/-- `hA2` of the Theorem 1.3 wiring (G3, all `κ`) from regular reference couplings and the image endpoint theorem. -/
theorem forall_fourForceCrosscutG3LifeStatement_of_regRef (hA1 : ∀ κ : ℝ, A1DualCouplingG3RegRefStatement κ)
    (h1 : ∀ κ : ℝ, A2SmallCrosscutG3Statement.{u} κ) (hI : ∀ κ : ℝ, ImageEndpointG3Statement.{u} κ)
    (h3 : ∀ κ : ℝ, A2SmallInHullG3Statement.{u} κ) : ∀ κ : ℝ, A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  fun κ => fourForceCrosscutG3LifeStatement_of_regRef (hA1 κ) (h1 κ) (hI κ) (h3 κ)

/-- `hA2'` of the Theorem 1.3 wiring (Eight, all `κ`). -/
theorem forall_threeForceCrosscutEightStatement_of_regRef (hA1 : ∀ κ : ℝ, A1DualCouplingEightRegRefStatement κ)
    (h1 : ∀ κ : ℝ, A2SmallCrosscutEightStatement.{u} κ) (hI : ∀ κ : ℝ, ImageEndpointEightStatement.{u} κ)
    (h3 : ∀ κ : ℝ, A2SmallInHullEightStatement.{u} κ) : ∀ κ : ℝ, A35.ThreeForceCrosscutEightStatement.{u} κ :=
  fun κ => threeForceCrosscutEightStatement_of_regRef (hA1 κ) (h1 κ) (hI κ) (h3 κ)

end InteractingSLE.ZhanGT4.A2TipSep
