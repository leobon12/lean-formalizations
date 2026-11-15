/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA2Pair
import InteractingSLE.Spec.Coupling.Assembly11BCoord

/-!
# A.1's dual pair pulls back along surjective measure-preserving maps

Packet PROVE-ZHAN-A1DUAL. Source: Astra, *Follow-up proofs*, §A.1 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L160–L189; R38): the dual coupling is a statement about two curves and the conditional laws of each given stopping-time
prefixes of the other. This file proves that the Lean form of that coupling (`A2X.IsA2DualPair`, PROVE-ZHAN-GT4-A2X)
is stable under pullback along a measurable, **surjective** map `π : Z → Ω₀` carrying the law `P` on `Z` to the law
`μ` on `Ω₀`, with every filtration pulled back (`Coupling.filtrationComap`). Surjectivity is what lets every stopping
time of a pulled-back filtration factor through `π` (`exists_isStoppingTime_comp_of_surjective`), so the quantifier
"for every stopping time of curve `k`" of `A2X.IsCondImageLaw` transfers.

This is the transport step of the glue over a given large curve (`A1DualGlue`): the reference coupling lives on a
standard Borel space `Ω₀`, the glued space is `Ω × ULift Ω₀`, and `π` is the second projection.

## Main results

* `isFilteredBrownianReal_comap`, `adaptedBefore_comap`: the Brownian and adaptedness clauses pull back;
* `exists_isStoppingTime_comp_of_surjective`: a stopping time of the pulled-back filtration is `τ₀ ∘ π`;
* `measurableSpace_comp_eq`: its stopped σ-algebra is the pullback of `τ₀`'s;
* `isRandomWordEvolutionUpTo_comap`, `isCondImageLaw_comap`;
* **`IsA2DualPair.comap`**, `IsA2DualPairG3.comap`, `IsA2DualPairEight.comap`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Dual

open A2X Coupling

variable {Ω₀ Z : Type*} {m₀ : MeasurableSpace Ω₀} [mZ : MeasurableSpace Z] {π : Z → Ω₀}

/-! ### Brownian motion and adaptedness -/

/-- **A filtered Brownian motion pulls back** along a measurable map carrying the law to the law. -/
theorem isFilteredBrownianReal_comap (hπ : Measurable π) {μ : Measure Ω₀} {P : Measure Z} (hP : P.map π = μ)
    {𝓖 : Filtration ℝ≥0 m₀} {B : ℝ≥0 → Ω₀ → ℝ} (hB : IsFilteredBrownianReal 𝓖 B μ) :
    IsFilteredBrownianReal (filtrationComap 𝓖 hπ) (fun t z => B t (π z)) P := by
  obtain ⟨hBB, hBa, hBi⟩ := hB
  have hlaw : HasLaw π μ P := ⟨hπ.aemeasurable, hP⟩
  have hBm : ∀ t, Measurable (B t) := fun t => (hBa t).mono (𝓖.le t) le_rfl
  refine ⟨⟨⟨fun I => (hBB.hasLaw I).comp hlaw⟩, ?_⟩, fun t => ?_, fun s t hst => ?_⟩
  · rw [← hP] at hBB
    exact ae_of_ae_map hπ.aemeasurable hBB.cont
  · exact @Measurable.comp _ _ _ ((𝓖 t).comap π) (𝓖 t) _ _ _ (hBa t) (comap_measurable π)
  · rw [Indep_iff]
    intro t1 t2 ht1 ht2
    obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht1
    obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht2
    have hS' : MeasurableSet ((fun ω => B t ω - B s ω) ⁻¹' S) := ((hBm t).sub (hBm s)) hS
    have hT' : MeasurableSet T := 𝓖.le s _ hT
    have hind := (Indep_iff _ _ _).1 (hBi s t hst) _ T
      (MeasurableSpace.measurableSet_comap.2 ⟨S, hS, rfl⟩) hT
    have e : (fun z : Z => B t (π z) - B s (π z)) ⁻¹' S = π ⁻¹' ((fun ω => B t ω - B s ω) ⁻¹' S) := rfl
    rw [e, ← preimage_inter, ← Measure.map_apply hπ (hS'.inter hT'), ← Measure.map_apply hπ hS',
      ← Measure.map_apply hπ hT', hP]
    exact hind

/-- Adaptedness before the lifetime pulls back. -/
theorem adaptedBefore_comap (hπ : Measurable π) {𝓖 : Filtration ℝ≥0 m₀} {ζ : Ω₀ → ℝ≥0∞}
    {X : ℝ≥0 → Ω₀ → ℝ} (hX : AdaptedBefore 𝓖 ζ X) :
    AdaptedBefore (filtrationComap 𝓖 hπ) (fun z => ζ (π z)) (fun t z => X t (π z)) :=
  fun t A hA => ⟨_, hX t A hA, rfl⟩

/-! ### Stopping times of a pulled-back filtration -/

/-- **A stopping time of a filtration pulled back along a surjective map factors through the map**: `τ = τ₀ ∘ π` with
`τ₀` a stopping time of the original filtration (`τ₀ = τ ∘ σ` for a right inverse `σ`). -/
theorem exists_isStoppingTime_comp_of_surjective (hπ : Measurable π) (hs : Function.Surjective π)
    {𝓕 : Filtration ℝ≥0 m₀} {τ : Z → ℝ≥0}
    (hτ : IsStoppingTime (filtrationComap 𝓕 hπ) fun z => (τ z : WithTop ℝ≥0)) :
    ∃ τ₀ : Ω₀ → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (τ₀ ω : WithTop ℝ≥0)) ∧ τ = τ₀ ∘ π := by
  have hC : ∀ i : ℝ≥0, ∃ C : Set Ω₀, MeasurableSet[𝓕 i] C ∧ ∀ z, τ z ≤ i ↔ π z ∈ C := fun i => by
    obtain ⟨C, hC, hCe⟩ := hτ i
    refine ⟨C, hC, fun z => ?_⟩
    have := congrArg (z ∈ ·) hCe
    simp only [mem_preimage, mem_ofPred_eq, WithTop.coe_le_coe, eq_iff_iff] at this
    exact this.symm
  choose C hCm hCτ using hC
  obtain ⟨σ, hσ⟩ := hs.hasRightInverse
  have key : ∀ z i, τ z ≤ i ↔ τ (σ (π z)) ≤ i := fun z i => by
    rw [hCτ i z, hCτ i (σ (π z)), hσ (π z)]
  refine ⟨fun ω => τ (σ ω), fun i => ?_, ?_⟩
  · have e : {ω | ((τ (σ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ i} = C i := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
      rw [hCτ i (σ ω), hσ ω]
    rw [e]; exact hCm i
  · funext z
    exact le_antisymm ((key z _).2 le_rfl) ((key z _).1 le_rfl)

/-- **The stopped σ-algebra of `τ₀ ∘ π`** (pulled-back filtration, `π` surjective) is the pullback of that of `τ₀`. -/
theorem measurableSpace_comp_eq (hπ : Measurable π) (hs : Function.Surjective π) {𝓕 : Filtration ℝ≥0 m₀}
    {τ₀ : Ω₀ → ℝ≥0} (hτ₀ : IsStoppingTime 𝓕 fun ω => (τ₀ ω : WithTop ℝ≥0))
    (hτ : IsStoppingTime (filtrationComap 𝓕 hπ) fun z => ((τ₀ ∘ π) z : WithTop ℝ≥0)) :
    hτ.measurableSpace = hτ₀.measurableSpace.comap π := by
  have e : (⨆ t, filtrationComap 𝓕 hπ t) = (⨆ t, 𝓕 t).comap π := by
    rw [MeasurableSpace.comap_iSup]; rfl
  apply le_antisymm
  · intro s hs'
    obtain ⟨hs1, hs2⟩ := hs'
    rw [e] at hs1
    obtain ⟨s₀, hs₀, rfl⟩ := hs1
    refine ⟨s₀, ⟨hs₀, fun i => ?_⟩, rfl⟩
    obtain ⟨c, hc, hce⟩ := hs2 i
    have hce' : π ⁻¹' c = π ⁻¹' (s₀ ∩ {ω | (τ₀ ω : WithTop ℝ≥0) ≤ i}) := hce
    rw [← hs.preimage_injective hce']
    exact hc
  · rintro _ ⟨s, hs₁, rfl⟩
    refine ⟨?_, fun i => ⟨_, hs₁.2 i, rfl⟩⟩
    rw [e]; exact ⟨s, hs₁.1, rfl⟩

/-! ### The random-word evolution and the conditional image law -/

variable {μ : Measure Ω₀} {P : Measure Z}

/-- An almost sure property pulls back along a measurable map carrying the law to the law. -/
theorem ae_comp_of_map_eq (hπ : Measurable π) (hP : P.map π = μ) {p : Ω₀ → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∀ᵐ z ∂P, p (π z) := by
  rw [← hP] at h
  exact ae_of_ae_map hπ.aemeasurable h

/-- **The random-word local evolution pulls back** (with the conditioning σ-algebra pulled back). -/
theorem isRandomWordEvolutionUpTo_comap (hπ : Measurable π) (hP : P.map π = μ) {a : ℝ} {nL nR : ℕ}
    {𝓔 : MeasurableSpace Ω₀} {F : Set Ω₀} {ΘL : Ω₀ → Fin nL → ℝ} {ΘR : Ω₀ → Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {𝓖 : Filtration ℝ≥0 m₀} {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}
    (h : @Restart.StoppedK2.IsRandomWordEvolutionUpTo Ω₀ m₀ a nL nR μ 𝓔 F ΘL ΘR ρL ρR 𝓖 W VL VR B ζ) :
    Restart.StoppedK2.IsRandomWordEvolutionUpTo a P (𝓔.comap π) (π ⁻¹' F) (ΘL ∘ π) (ΘR ∘ π) ρL ρR
      (filtrationComap 𝓖 hπ) (fun t z => W t (π z)) (fun i t z => VL i t (π z)) (fun j t z => VR j t (π z))
      (fun t z => B t (π z)) (fun z => ζ (π z)) := by
  obtain ⟨h0, hF, hΘL, hΘR, hB, hW, hVL, hVR, hpath⟩ := h
  refine ⟨MeasurableSpace.comap_mono h0, ⟨F, hF, rfl⟩,
    @Measurable.comp _ _ _ (𝓔.comap π) 𝓔 _ _ _ hΘL (comap_measurable π),
    @Measurable.comp _ _ _ (𝓔.comap π) 𝓔 _ _ _ hΘR (comap_measurable π),
    isFilteredBrownianReal_comap hπ hP hB, adaptedBefore_comap hπ hW, fun i => adaptedBefore_comap hπ (hVL i),
    fun j => adaptedBefore_comap hπ (hVR j), ae_comp_of_map_eq hπ hP hpath⟩

/-- **The conditional image law pulls back along a surjective measure-preserving map** (every filtration pulled back;
the stopping time is factored through `π`). -/
theorem isCondImageLaw_comap (hπ : Measurable π) (hs : Function.Surjective π) (hP : P.map π = μ) {a : ℝ}
    {nL nR : ℕ} {𝓕k : Filtration ℝ≥0 m₀} {live : ℝ≥0 → Ω₀ → Prop} {xj : ℝ} {wj : ℝ≥0 → Ω₀ → ℝ}
    {ζj : Ω₀ → ℝ≥0∞} {xk : ℝ} {wk : ℝ≥0 → Ω₀ → ℝ} {src : ℝ≥0 → Ω₀ → ℝ} {ΘL : ℝ≥0 → Ω₀ → Fin nL → ℝ}
    {ΘR : ℝ≥0 → Ω₀ → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h : IsCondImageLaw a μ 𝓕k live xj wj ζj xk wk src ΘL ΘR ρL ρR) :
    IsCondImageLaw a P (filtrationComap 𝓕k hπ) (fun t z => live t (π z)) xj (fun t z => wj t (π z))
      (fun z => ζj (π z)) xk (fun t z => wk t (π z)) (fun t z => src t (π z)) (fun t z => ΘL t (π z))
      (fun t z => ΘR t (π z)) ρL ρR := by
  intro τ hτ
  obtain ⟨τ₀, hτ₀, rfl⟩ := exists_isStoppingTime_comp_of_surjective hπ hs hτ
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hev, hchain⟩ := h τ₀ hτ₀
  refine ⟨filtrationComap 𝓖 hπ, fun t z => W' t (π z), fun i t z => VL' i t (π z), fun j t z => VR' j t (π z),
    fun t z => B' t (π z), fun z => ζ' (π z), fun z => clk (π z), ?_, ?_⟩
  · rw [measurableSpace_comp_eq hπ hs hτ₀ hτ]
    exact isRandomWordEvolutionUpTo_comap hπ hP hev
  · exact ae_comp_of_map_eq hπ hP hchain

/-! ### The dual pair -/

/-- **A.1's dual pair pulls back along a surjective measure-preserving map.** -/
theorem IsA2DualPair.comap (hπ : Measurable π) (hs : Function.Surjective π) (hP : P.map π = μ) {κ : ℝ}
    {nL₂ nL₁ nR₁ mL₂ : ℕ} {xL₂ ρL₂ : Fin nL₂ → ℝ} {x₁ : ℝ} {xL₁ : Fin nL₁ → ℝ} {xR₁ : Fin nR₁ → ℝ}
    {ρL₁ : Fin nL₁ → ℝ} {ρR₁ : Fin nR₁ → ℝ} {ρL₂' : Fin mL₂ → ℝ} {src₁ : ℝ≥0 → Ω₀ → ℝ}
    {ΘL₁ : ℝ≥0 → Ω₀ → Fin nL₁ → ℝ} {ΘR₁ : ℝ≥0 → Ω₀ → Fin nR₁ → ℝ} {src₂ : ℝ≥0 → Ω₀ → ℝ}
    {ΘL₂ : ℝ≥0 → Ω₀ → Fin mL₂ → ℝ} {𝓕₂ : Filtration ℝ≥0 m₀} {W₂ : ℝ≥0 → Ω₀ → ℝ}
    {VL₂ : Fin nL₂ → ℝ≥0 → Ω₀ → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ} {B₂ : ℝ≥0 → Ω₀ → ℝ} {ζ₂ : Ω₀ → ℝ≥0∞}
    {𝓕₁ : Filtration ℝ≥0 m₀} {W₁ : ℝ≥0 → Ω₀ → ℝ} {VL₁ : Fin nL₁ → ℝ≥0 → Ω₀ → ℝ}
    {VR₁ : Fin nR₁ → ℝ≥0 → Ω₀ → ℝ} {B₁ : ℝ≥0 → Ω₀ → ℝ} {ζ₁ : Ω₀ → ℝ≥0∞} {i₀ : Fin nL₂}
    (h : IsA2DualPair κ xL₂ ρL₂ x₁ xL₁ xR₁ ρL₁ ρR₁ ρL₂' src₁ ΘL₁ ΘR₁ src₂ ΘL₂ μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁
      VR₁ B₁ ζ₁ i₀) :
    IsA2DualPair κ xL₂ ρL₂ x₁ xL₁ xR₁ ρL₁ ρR₁ ρL₂' (fun t z => src₁ t (π z)) (fun t z => ΘL₁ t (π z))
      (fun t z => ΘR₁ t (π z)) (fun t z => src₂ t (π z)) (fun t z => ΘL₂ t (π z)) P (filtrationComap 𝓕₂ hπ)
      (fun t z => W₂ t (π z)) (fun i t z => VL₂ i t (π z)) (fun i t z => VR₂ i t (π z)) (fun t z => B₂ t (π z))
      (fun z => ζ₂ (π z)) (filtrationComap 𝓕₁ hπ) (fun t z => W₁ t (π z)) (fun i t z => VL₁ i t (π z))
      (fun i t z => VR₁ i t (π z)) (fun t z => B₁ t (π z)) (fun z => ζ₁ (π z)) i₀ :=
  ⟨Coupling.IsIntegratedSLEEvolution.comap hπ hP h.1, Coupling.IsIntegratedSLEEvolution.comap hπ hP h.2.1,
    isCondImageLaw_comap hπ hs hP h.2.2.1, isCondImageLaw_comap hπ hs hP h.2.2.2⟩

/-- The (G3) dual pair pulls back. -/
theorem IsA2DualPairG3.comap (hπ : Measurable π) (hs : Function.Surjective π) (hP : P.map π = μ) {κ y x : ℝ}
    {𝓕₂ : Filtration ℝ≥0 m₀} {W₂ : ℝ≥0 → Ω₀ → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Ω₀ → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ}
    {B₂ : ℝ≥0 → Ω₀ → ℝ} {ζ₂ : Ω₀ → ℝ≥0∞} {𝓕₁ : Filtration ℝ≥0 m₀} {W₁ : ℝ≥0 → Ω₀ → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ} {VR₁ : Fin 3 → ℝ≥0 → Ω₀ → ℝ} {B₁ : ℝ≥0 → Ω₀ → ℝ} {ζ₁ : Ω₀ → ℝ≥0∞}
    (h : IsA2DualPairG3 κ y x μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁) :
    IsA2DualPairG3 κ y x P (filtrationComap 𝓕₂ hπ) (fun t z => W₂ t (π z)) (fun i t z => VL₂ i t (π z))
      (fun i t z => VR₂ i t (π z)) (fun t z => B₂ t (π z)) (fun z => ζ₂ (π z)) (filtrationComap 𝓕₁ hπ)
      (fun t z => W₁ t (π z)) (fun i t z => VL₁ i t (π z)) (fun i t z => VR₁ i t (π z)) (fun t z => B₁ t (π z))
      (fun z => ζ₁ (π z)) :=
  IsA2DualPair.comap hπ hs hP h

/-- The (Eight) dual pair pulls back. -/
theorem IsA2DualPairEight.comap (hπ : Measurable π) (hs : Function.Surjective π) (hP : P.map π = μ) {κ x : ℝ}
    {𝓕₂ : Filtration ℝ≥0 m₀} {W₂ : ℝ≥0 → Ω₀ → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω₀ → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ}
    {B₂ : ℝ≥0 → Ω₀ → ℝ} {ζ₂ : Ω₀ → ℝ≥0∞} {𝓕₁ : Filtration ℝ≥0 m₀} {W₁ : ℝ≥0 → Ω₀ → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ} {VR₁ : Fin 2 → ℝ≥0 → Ω₀ → ℝ} {B₁ : ℝ≥0 → Ω₀ → ℝ} {ζ₁ : Ω₀ → ℝ≥0∞}
    (h : IsA2DualPairEight κ x μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁) :
    IsA2DualPairEight κ x P (filtrationComap 𝓕₂ hπ) (fun t z => W₂ t (π z)) (fun i t z => VL₂ i t (π z))
      (fun i t z => VR₂ i t (π z)) (fun t z => B₂ t (π z)) (fun z => ζ₂ (π z)) (filtrationComap 𝓕₁ hπ)
      (fun t z => W₁ t (π z)) (fun i t z => VL₁ i t (π z)) (fun i t z => VR₁ i t (π z)) (fun t z => B₁ t (π z))
      (fun z => ζ₁ (π z)) :=
  IsA2DualPair.comap hπ hs hP h

end InteractingSLE.ZhanGT4.A1Dual
