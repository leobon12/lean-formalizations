/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2TipSepImage
import InteractingSLE.Spec.ZhanGT4.A1RefStatement

/-!
# A.2 and A.3 from A.1's reference form with usual-augmentation filtrations (R72)

Packet PROVE-ZHAN-A2TIPSEP. R70, R72: the A.1 line's reference target `A1Ref.A1DualCoupling{G3,Eight}RefUAStatement`
supplies, on a standard Borel space, a dual pair whose filtrations are their own usual augmentations — so its image law
holds at every usual-augmentation stopping time, and it is an augmented pair (`IsA2DualPairG3Aug`) there. A.2 part 2 is
proved **on the reference space** (`a2HullInside…AugStatement_of_imageEndpoint`) and its almost sure, pathwise conclusion
is transported to the glued version over any given large curve (A1DUAL's glue: the version is the composition with the
projection, which carries the glued measure to the reference law). No augmentation of a pulled-back filtration is
needed.

* `fourForceCrosscutG3LifeStatement_of_refUA`, `threeForceCrosscutEightStatement_of_refUA`,
  `firstSwallowCrosscutStatement_of_refUA` and the `∀ κ` forms: A.2 (G3, Eight) and A.3 from the RefUA statements,
  A.2 part 1 (A2P1, proved), the image endpoint theorems and A.2 part 3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

/-- A RefUA (G3) pair is an augmented pair. -/
theorem isA2DualPairG3Aug_of_ua {Ω : Type*} [mΩ : MeasurableSpace Ω] {κ y x : ℝ} {P : Measure Ω}
    {𝓕₂ 𝓕₁ : Filtration ℝ≥0 mΩ} {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {W₁ : ℝ≥0 → Ω → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ} {B₁ : ℝ≥0 → Ω → ℝ} {ζ₁ : Ω → ℝ≥0∞}
    (h : IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁) (hUA : usualAugmentation 𝓕₂ P = 𝓕₂) :
    IsA2DualPairG3Aug κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ :=
  ⟨h, by rw [hUA]; exact h.2.2.1⟩

/-- A RefUA (Eight) pair is an augmented pair. -/
theorem isA2DualPairEightAug_of_ua {Ω : Type*} [mΩ : MeasurableSpace Ω] {κ x : ℝ} {P : Measure Ω}
    {𝓕₂ 𝓕₁ : Filtration ℝ≥0 mΩ} {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {W₁ : ℝ≥0 → Ω → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ} {B₁ : ℝ≥0 → Ω → ℝ} {ζ₁ : Ω → ℝ≥0∞}
    (h : IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁) (hUA : usualAugmentation 𝓕₂ P = 𝓕₂) :
    IsA2DualPairEightAug κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ :=
  ⟨h, by rw [hUA]; exact h.2.2.1⟩

/-- **A.2 (G3)** (`A34.FourForceCrosscutG3LifeStatement κ`) from A.1's RefUA form (R72), A.2 part 1, the image
endpoint theorem (on the reference space, universe `0`) and A.2 part 3. -/
theorem fourForceCrosscutG3LifeStatement_of_refUA {κ : ℝ} (hA1 : A1Ref.A1DualCouplingG3RefUAStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{u} κ) (hI : ImageEndpointG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{u} κ) : A34.FourForceCrosscutG3LifeStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair, hUA₂, -⟩ :=
    hA1 hκ4 hκ8 y x hyx hx
  have hIn₀ := a2HullInsideG3AugStatement_of_imageEndpoint hI hκ4 hκ8 y x hyx hx μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁
    VL₁ VR₁ B₁ ζ₁ (isA2DualPairG3Aug_of_ua hpair hUA₂)
  obtain ⟨K, hK, hsnd, hver⟩ := A1Dual.exists_glue_version.{u} (by linarith : (0 : ℝ) < κ)
    (A1Dual.isOrderedForceWord_largeG3 hyx hx) hE hpair.1
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ := P)
  have hπ : Measurable fun z : Ω × ULift.{u} Ω₀ => z.2.down := measurable_down.comp measurable_snd
  have hs : Function.Surjective fun z : Ω × ULift.{u} Ω₀ => z.2.down :=
    fun ω₀ => ⟨(Classical.arbitrary Ω, ⟨ω₀⟩), rfl⟩
  have hpairQ := A1Dual.IsA2DualPairG3.comap hπ hs hsnd hpair
  have hS1 := h1 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) _ _ _ _ _ _ hpairQ.2.1
  have hS2 := A1Dual.ae_comp_of_map_eq hπ hsnd hIn₀
  have hS3 := h3 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) _ _ _ _ _ _ _ _ _ _ _ _ hpairQ
  refine ae_of_ae_compProd_fst (K := K) (Q := fun ω => ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧
    0 < (γ 1).re ∧ outerBoundary (lifeHullClosure (W · ω) (VL 0 · ω) (ζ ω)) = γ '' Ioo 0 1) ?_
  filter_upwards [hS1, hS2, hS3, hver] with z hz1 hz2 hz3 hzv
  have e : lifeHullClosure (W₂ · z.2.down) (VL₂ 0 · z.2.down) (ζ₂ z.2.down) =
      lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1) :=
    A1Dual.lifeHullClosure_congr hzv.1 (fun t ht => (hzv.2 t ht).1) (fun t ht => (hzv.2 t ht).2.1 0)
  show ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧ 0 < (γ 1).re ∧
    outerBoundary (lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1)) = γ '' Ioo 0 1
  rw [← e]
  exact exists_outerBoundary_eq_of_parts hz1 hz2 hz3

/-- **A.2's three-force version (Eight)** (`A35.ThreeForceCrosscutEightStatement κ`) from A.1's RefUA form (R72). -/
theorem threeForceCrosscutEightStatement_of_refUA {κ : ℝ} (hA1 : A1Ref.A1DualCouplingEightRefUAStatement κ)
    (h1 : A2SmallCrosscutEightStatement.{u} κ) (hI : ImageEndpointEightStatement.{0} κ)
    (h3 : A2SmallInHullEightStatement.{u} κ) : A35.ThreeForceCrosscutEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair, hUA₂, -⟩ :=
    hA1 hκ8 x hx
  have hIn₀ := a2HullInsideEightAugStatement_of_imageEndpoint hI hκ8 x hx μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁
    VL₁ VR₁ B₁ ζ₁ (isA2DualPairEightAug_of_ua hpair hUA₂)
  obtain ⟨K, hK, hsnd, hver⟩ := A1Dual.exists_glue_version.{u} (by linarith : (0 : ℝ) < κ)
    (A1Dual.isOrderedForceWord_largeEight hx) hE hpair.1
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ := P)
  have hπ : Measurable fun z : Ω × ULift.{u} Ω₀ => z.2.down := measurable_down.comp measurable_snd
  have hs : Function.Surjective fun z : Ω × ULift.{u} Ω₀ => z.2.down :=
    fun ω₀ => ⟨(Classical.arbitrary Ω, ⟨ω₀⟩), rfl⟩
  have hpairQ := A1Dual.IsA2DualPairEight.comap hπ hs hsnd hpair
  have hS1 := h1 hκ8 x hx (P ⊗ₘ K) _ _ _ _ _ _ hpairQ.2.1
  have hS2 := A1Dual.ae_comp_of_map_eq hπ hsnd hIn₀
  have hS3 := h3 hκ8 x hx (P ⊗ₘ K) _ _ _ _ _ _ _ _ _ _ _ _ hpairQ
  refine ae_of_ae_compProd_fst (K := K) (Q := fun ω => ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x ∧
    0 < (γ 1).re ∧ outerBoundary (lifeHullClosure (W · ω) (VL 0 · ω) (ζ ω)) = γ '' Ioo 0 1) ?_
  filter_upwards [hS1, hS2, hS3, hver] with z hz1 hz2 hz3 hzv
  have e : lifeHullClosure (W₂ · z.2.down) (VL₂ 0 · z.2.down) (ζ₂ z.2.down) =
      lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1) :=
    A1Dual.lifeHullClosure_congr hzv.1 (fun t ht => (hzv.2 t ht).1) (fun t ht => (hzv.2 t ht).2.1 0)
  show ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x ∧ 0 < (γ 1).re ∧
    outerBoundary (lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1)) = γ '' Ioo 0 1
  rw [← e]
  exact exists_outerBoundary_eq_of_parts hz1 hz2 hz3

/-- **A.3** (`FirstSwallowCrosscutStatement κ`) from A.1's RefUA forms (R72), A.2 part 1, the image endpoint theorems
and A.2 part 3. -/
theorem firstSwallowCrosscutStatement_of_refUA {κ : ℝ} (hA1 : A1Ref.A1DualCouplingG3RefUAStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (hI : ImageEndpointG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1Ref.A1DualCouplingEightRefUAStatement κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (hI' : ImageEndpointEightStatement.{0} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  A35.firstSwallowCrosscutStatement_of_A2 (fourForceCrosscutG3LifeStatement_of_refUA hA1 h1 hI h3)
    (threeForceCrosscutEightStatement_of_refUA hA1' h1' hI' h3')

/-- `hA2` of the Theorem 1.3 wiring (G3, all `κ`) from the RefUA statements and the image endpoint theorem. -/
theorem forall_fourForceCrosscutG3LifeStatement_of_refUA (hA1 : ∀ κ : ℝ, A1Ref.A1DualCouplingG3RefUAStatement κ)
    (h1 : ∀ κ : ℝ, A2SmallCrosscutG3Statement.{u} κ) (hI : ∀ κ : ℝ, ImageEndpointG3Statement.{0} κ)
    (h3 : ∀ κ : ℝ, A2SmallInHullG3Statement.{u} κ) : ∀ κ : ℝ, A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  fun κ => fourForceCrosscutG3LifeStatement_of_refUA (hA1 κ) (h1 κ) (hI κ) (h3 κ)

/-- `hA2'` of the Theorem 1.3 wiring (Eight, all `κ`) from the RefUA statements and the image endpoint theorem. -/
theorem forall_threeForceCrosscutEightStatement_of_refUA
    (hA1 : ∀ κ : ℝ, A1Ref.A1DualCouplingEightRefUAStatement κ) (h1 : ∀ κ : ℝ, A2SmallCrosscutEightStatement.{u} κ)
    (hI : ∀ κ : ℝ, ImageEndpointEightStatement.{0} κ) (h3 : ∀ κ : ℝ, A2SmallInHullEightStatement.{u} κ) :
    ∀ κ : ℝ, A35.ThreeForceCrosscutEightStatement.{u} κ :=
  fun κ => threeForceCrosscutEightStatement_of_refUA (hA1 κ) (h1 κ) (hI κ) (h3 κ)

end InteractingSLE.ZhanGT4.A2TipSep
