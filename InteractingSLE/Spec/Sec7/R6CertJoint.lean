/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CertGerm

/-!
# R.6's germ comparison for two pockets read at their own marked stops

PROVE-R6-CERT. A pocket read at its own deterministic relative time is described, for the comparison, by
`IsStopPocket`: its marked stop `T` (the left end `T⁰(q)` of ruling R67) with marks `ℳ`, a random set `E` (its active
complement) that is hitting-measurable for `ℳ`, covers the walls–hull set at `T` and is all of `ℍ` when `T = ⊤`.
Two such pockets (the outer pocket at `q` and a nested pocket at `q'`) satisfy the joint walls–hull law at `T₁ ∨ T₂`
for the joined marks, so their means have the physical germ comparison of R.6 at every locally shared boundary point
(`ae_r6Germ_of_stopPockets`). No common time, no stopping time of a pocket's own clock read at the other pocket's
time, and no R.5 at a random time are needed.

* `IsStopPocket`, `IsStopPocket.max_cover`;
* **`ae_r6Germ_of_stopPockets`**.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cert

open PocketStopWallsFin PocketStopWalls PocketStopSide LocalSets WholeField

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **A pocket read at its own marked stop**: the stop `T` is a marked stop with marks `ℳ ≤ σ(X) ∨ 𝓕_∞`, the random
set `E` is hitting-measurable for `ℳ`, contains the walls–hull set `ℍ ∩ (Γ ∪ K_T)` where `T < ⊤`, and is `ℍ`-filling
where `T = ⊤`. -/
structure IsStopPocket {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (X : Ω → 𝒳) (K : ℝ≥0 → Ω → Set ℂ)
    (Γ : Ω → Set ℂ) (ℳ : MeasurableSpace Ω) (T : Ω → ℝ≥0∞) (E : Ω → Set ℂ) : Prop where
  marked : IsMarkedStop ℳ 𝓕 X T
  marks_le : ∀ M, MeasurableSet[ℳ] M → MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, 𝓕 r] M
  meas : Measurable[ℳ, hittingSigma] E
  cover : ∀ ω, T ω < ⊤ → H ∩ (Γ ω ∪ K (T ω).toNNReal ω) ⊆ E ω
  top : ∀ ω, T ω = ⊤ → H ⊆ E ω

/-- **Coverage at the later stop**: the walls–hull set of the joined walls at `T₁ ∨ T₂` lies in `E₁ ∪ E₂`. -/
theorem IsStopPocket.max_cover {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳}
    {K : ℝ≥0 → Ω → Set ℂ} {Γ₁ Γ₂ : Ω → Set ℂ} {ℳ₁ ℳ₂ : MeasurableSpace Ω} {T₁ T₂ : Ω → ℝ≥0∞}
    {E₁ E₂ : Ω → Set ℂ} (h₁ : IsStopPocket 𝓕 X K Γ₁ ℳ₁ T₁ E₁) (h₂ : IsStopPocket 𝓕 X K Γ₂ ℳ₂ T₂ E₂) (ω : Ω) :
    wallsHullAt (fun ω => Γ₁ ω ∪ Γ₂ ω) K (fun ω => max (T₁ ω) (T₂ ω)) ω ⊆ E₁ ω ∪ E₂ ω := by
  intro z hz
  by_cases hT : max (T₁ ω) (T₂ ω) < ⊤
  · rw [wallsHullAt, ite_eq_left hT] at hz
    have hT₁ : T₁ ω < ⊤ := lt_of_le_of_lt (le_max_left _ _) hT
    have hT₂ : T₂ ω < ⊤ := lt_of_le_of_lt (le_max_right _ _) hT
    obtain ⟨hzH, (hzΓ₁ | hzΓ₂) | hzK⟩ := hz
    · exact Or.inl (h₁.cover ω hT₁ ⟨hzH, Or.inl hzΓ₁⟩)
    · exact Or.inr (h₂.cover ω hT₂ ⟨hzH, Or.inl hzΓ₂⟩)
    · rcases le_total (T₁ ω) (T₂ ω) with h12 | h21
      · rw [max_eq_right h12] at hzK
        exact Or.inr (h₂.cover ω hT₂ ⟨hzH, Or.inr hzK⟩)
      · rw [max_eq_left h21] at hzK
        exact Or.inl (h₁.cover ω hT₁ ⟨hzH, Or.inr hzK⟩)
  · rw [wallsHullAt, ite_eq_right hT] at hz
    have htop : max (T₁ ω) (T₂ ω) = ⊤ := not_lt_top_iff.1 hT
    rcases max_eq_iff.1 htop with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact Or.inl (h₁.top ω h1 hz)
    · exact Or.inr (h₂.top ω h2 hz)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **R.6's germ comparison for two pockets at their own marked stops** (item 5 of `R6Rel.R6Cert`): the regularized
hull of a frozen coupling with almost surely infinite lifetime, the joined walls `Γ₁ ∪ Γ₂` satisfying the
determined-locality criterion for the information `X`, two pockets read at their own marked stops (`IsStopPocket`),
whose sets are local with unbounded lower-union components, and their local-set means. Almost surely, uniformly over
representatives, nested conformal charts on the two complements, collars and landings, local agreement of the two
sets at the landing point gives `R6Rel.R6Germ`. -/
theorem ae_r6Germ_of_stopPockets {ℳ₁ ℳ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {X : Ω → 𝒳} (hXm : Measurable X) {Γ₁ Γ₂ : Ω → Set ℂ}
    (hΓ : Measurable[mΩ, hittingSigma] (fun ω => Γ₁ ω ∪ Γ₂ ω))
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens (centredField h u₀) (fun ω => G (centredField h u₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ₁ ω ∪ Γ₂ ω) U} ∩ X ⁻¹' B =ᵐ[P]
          (fun ω => LocalSets.markovCompl G (centredField h u₀ ω)) ⁻¹' B')
    {T₁ T₂ : Ω → ℝ≥0∞} {EC EU : Ω → Set ℂ}
    (hP₁ : IsStopPocket (drivingFiltration P hX) X (regHull W ζ) Γ₁ ℳ₁ T₁ EC)
    (hP₂ : IsStopPocket (drivingFiltration P hX) X (regHull W ζ) Γ₂ ℳ₂ T₂ EU)
    (hCm : Measurable[mΩ, hittingSigma] EC) (hUm : Measurable[mΩ, hittingSigma] EU)
    (hCloc : IsLocalSet EC (centredField h u₀) P) (hUloc : IsLocalSet EU (centredField h u₀) P)
    (hCunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (EC ω), ¬ IsBounded (connectedComponentIn (lowerUnion (EC ω)) z))
    (hUunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (EU ω), ¬ IsBounded (connectedComponentIn (lowerUnion (EU ω)) z))
    {gC gU : Ω → DistOn upperHalfPlaneOpens} (hgC : IsLocalSetMean EC (centredField h u₀) P gC)
    (hgU : IsLocalSetMean EU (centredField h u₀) P gU) :
    ∀ᵐ ω ∂P, ∀ v vI : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ EC ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω → gC ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vI (H \ EU ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU ω → gU ω φ = ∫ z, vI z * φ z) →
      ∀ outer inner : Chart, outer.IsConformal → inner.IsConformal → (inner.dom : Set ℂ) ⊆ outer.dom →
        (outer.dom : Set ℂ) = H \ EC ω → (inner.dom : Set ℂ) = H \ EU ω →
        ∀ (p : ℂ) (ξ r : ℝ), p ∈ EC ω ∪ {z : ℂ | z.im = 0} → p ∈ EU ω ∪ {z : ℂ | z.im = 0} →
          (∃ ε > 0, EU ω ∩ ball p ε ⊆ EC ω) → (∃ ε > 0, EC ω ∩ ball p ε ⊆ EU ω) → 0 < r →
          H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) →
          Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → R6Rel.R6Germ outer v vI ξ := by
  have hS0 : ∀ M, MeasurableSet[ℳ₁ ⊔ ℳ₂] M →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, drivingFiltration P hX r] M :=
    fun M hM => (sup_le (show ℳ₁ ≤ _ from fun N hN => hP₁.marks_le N hN)
      (show ℳ₂ ≤ _ from fun N hN => hP₂.marks_le N hN)) M hM
  have hJoint := isHistoryAvoidanceLocal_walls_regHull_markedStop hC hκ hu₀ hX hζ hXm hΓ hW
    (isMarkedStop_max hP₁.marked hP₂.marked) hS0
  exact ae_r6Germ_of_joint (isZeroBoundaryGFF_centredField hC hu₀) hJoint
    (hP₁.meas.mono le_sup_left le_rfl) (hP₂.meas.mono le_sup_right le_rfl)
    (Eventually.of_forall (IsStopPocket.max_cover hP₁ hP₂)) hCm hUm hCloc hUloc hCunb hUunb hgC hgU

end InteractingSLE.Sec7.R6Cert
