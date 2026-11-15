/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsHull
import InteractingSLE.Spec.Sec7.PocketStopWallsWalls
import InteractingSLE.Spec.Sec7.PocketStopFieldUnion
import InteractingSLE.Spec.Coupling.WholeField2Hull

/-!
# `PocketStopWallsLaw` from the determination-free union law

Packet PROVE-STRIPSYS37. PROVE-STRIPSYS35's named input `PocketStopField.PocketStopWallsLaw` (Aux. lemma 35's marked
law of the walls with the counterflow hull at the ambient stop `T(q)`, marks `locPrefixSigma 𝓦 A γ q`) asks for some
hitting-measurable random set equal to `ℍ ∩ (Γ ∪ F)` on the live event and satisfying the history-marked avoidance
criterion. Here:

* `pocketStopWallsLaw_of_wallsHullAt`: it is the criterion for `wallsHullAt Γ K T` (`ℍ ∩ (Γ ∪ K_T)` where `T < ∞`,
  `ℍ` elsewhere) for any stop `T` that is finite on the live event with `F = K_T` there;
* **`pocketStopWallsLaw_of_filtration`**: hence `PocketStopWallsLaw` from the hypotheses of
  `isHistoryAvoidanceLocal_walls_hull_filtration` (walls determined local; hull process adapted to a right-continuous
  filtration and marked local at its bounded stopping times — no determination of the counterflow, ruling R48), the
  raw stopping properties of `T` with the marks `locPrefixSigma 𝓦 A γ q`, and the hitting measurability of
  `wallsHullAt Γ K T`;
* `isHistoryAvoidanceLocal_hull_of_coupling`, **`pocketStopWallsLaw_of_coupling`**: the hull hypothesis `hloc` for the
  hull of a frozen optional hull coupling with almost surely infinite lifetime (the capacity coding theorem,
  `WholeField.isHistoryAvoidanceLocal_hull`), for its centred field and its driving filtration; the remaining hull
  hypotheses are the measurability of the raw hull's avoidance events.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopWalls

open QuantumZipper (H)
open LQGMetric (DistOn)
open PocketCoupling PocketStopField Lemma71C LocalSets

section Law

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **`PocketStopWallsLaw` is the marked criterion of `wallsHullAt`** for a stop `T` that is finite on the live event,
where the counterflow hull `F` is `K_T`. -/
theorem pocketStopWallsLaw_of_wallsHullAt {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {Γ F : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {q : ℝ≥0}
    {K : ℝ≥0 → Ω → Set ℂ} {T : Ω → ℝ≥0∞}
    (hT : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → T ω < ⊤ ∧ F ω = K (T ω).toNNReal ω)
    (hE : Measurable[mΩ, hittingSigma] (wallsHullAt Γ K T))
    (hloc : WholeField.IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ q) (wallsHullAt Γ K T) h₀ P) :
    PocketStopWallsLaw 𝓦 P A γ Γ F h₀ q := by
  refine ⟨wallsHullAt Γ K T, hE, hloc, fun ω hω hlive => ?_⟩
  obtain ⟨hTω, hF⟩ := hT ω hω hlive
  simp only [wallsHullAt, hTω, ↓reduceIte, hF]

/-- **`PocketStopWallsLaw` from the determination-free union law.** The walls `Γ` with information `X` are
determined local for `h₀` (`hW`: Lemma 6.2 for the walls fully explored, `walls_determinedLocal`); the hull process
`K` is monotone, adapted to a right-continuous filtration `𝓕` and marked local at every bounded stopping time with
marks `𝓕_τ` (`hKad`, `hKst`, `hloc`: the frozen optional hull coupling through the capacity coding theorem); the
stop `T` is finite on the live event with `F = K_T` there (`hT`) and has the raw stopping properties with the marks
`locPrefixSigma 𝓦 A γ q` (`hS0`, `hS1`, `hS2`); and `wallsHullAt Γ K T` is hitting-measurable (`hE`). -/
theorem pocketStopWallsLaw_of_filtration {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Set Ω} {γ : Ω → ℝ → ℂ} {Γ F : Ω → Set ℂ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {q : ℝ≥0} (hh : Measurable h₀)
    {X : Ω → 𝒳} (hX : Measurable X) (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens h₀ (fun ω => G (h₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => markovCompl G (h₀ ω)) ⁻¹' B')
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous] {K : ℝ≥0 → Ω → Set ℂ}
    (hKmono : ∀ ω, Monotone fun t => K t ω)
    (hKad : ∀ (t : ℝ≥0) (U : Set ℂ), IsOpen U → U ⊆ H → MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) U})
    (hKst : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) → ∀ U : Set ℂ, IsOpen U →
      U ⊆ H → MeasurableSet[hτ.measurableSpace] {ω | Disjoint (K ((τ ω).untopD 0) ω) U})
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) →
      WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace (fun ω => K ((τ ω).untopD 0) ω) h₀ P)
    {T : Ω → ℝ≥0∞} (hT : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → T ω < ⊤ ∧ F ω = K (T ω).toNNReal ω)
    (hE : Measurable[mΩ, hittingSigma] (wallsHullAt Γ K T))
    (hS1 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A γ q] M → ∀ r : ℝ≥0,
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 r] ({ω | T ω < r} ∩ M))
    (hS2 : ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) (N : ℕ),
      ∀ M, MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
        MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
          ({ω | T ω = (σ ω : ℝ≥0∞)} ∩ ({ω | T ω < N} ∩ M)))
    (hS0 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, 𝓕 r] M) :
    PocketStopWallsLaw 𝓦 P A γ Γ F h₀ q :=
  pocketStopWallsLaw_of_wallsHullAt hT hE
    (isHistoryAvoidanceLocal_walls_hull_filtration hh hX hΓ hW hKmono hKad hKst hloc hS1 hS2 hS0)

end Law

/-! ### The hull of a frozen optional hull coupling -/

section Coupling

open WholeField
open QuantumZipper (fwdHull)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*}

/-- **The hull of a frozen coupling with infinite lifetime is marked local at every bounded stopping time** of its
driving filtration, with the stopped σ-algebra as marks, for its centred field (Aux. lemmas 18–19 through the capacity
coding theorem, `WholeField.isHistoryAvoidanceLocal_hull`), as soon as the raw hull at such times is
hitting-measurable. No field determination of the curve is used. -/
theorem isHistoryAvoidanceLocal_hull_of_coupling [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕₀ : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hKm : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (drivingFiltration P hX) τ → (∀ ω, τ ω ≠ ⊤) →
      Measurable[mΩ, hittingSigma] fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hfin : ∀ ω, τ ω ≠ ⊤) :
    IsHistoryAvoidanceLocal hτ.measurableSpace
      (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) (centredField h u₀) P := by
  refine isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hτ ?_ (hKm τ hτ hfin) (Eventually.of_forall fun _ => rfl)
  filter_upwards [hζ] with ω hω
  rw [hω]
  exact lt_top_iff_ne_top.2 (hfin ω)

/-- **`PocketStopWallsLaw` for the hull of a frozen optional hull coupling** (`K_t` the hull of its driver,
`h₀` its centred field, `𝓕` its driving filtration): the hull's marked locality is discharged by
`isHistoryAvoidanceLocal_hull_of_coupling`. The remaining hypotheses are the raw hull's measurability (`hKm`, `hKad`,
`hKst`), the walls' determined locality for the centred field (`hW`), and the stop's hypotheses (`hT`, `hE`, `hS0`,
`hS1`, `hS2`). -/
theorem pocketStopWallsLaw_of_coupling {𝒳 : Type*} [MeasurableSpace 𝒳] {𝓦 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕₀ : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {Γ F : Ω → Set ℂ} {q : ℝ≥0}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hKm : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (drivingFiltration P hX) τ → (∀ ω, τ ω ≠ ⊤) →
      Measurable[mΩ, hittingSigma] fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (hKad : ∀ (t : ℝ≥0) (U : Set ℂ), IsOpen U → U ⊆ H →
      MeasurableSet[drivingFiltration P hX t] {ω | Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) U})
    (hKst : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) τ), (∀ ω, τ ω ≠ ⊤) →
      ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[hτ.measurableSpace]
        {ω | Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) U})
    {X : Ω → 𝒳} (hXm : Measurable X) (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens (centredField h u₀) (fun ω => G (centredField h u₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => markovCompl G (centredField h u₀ ω)) ⁻¹' B')
    {T : Ω → ℝ≥0∞}
    (hT : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → T ω < ⊤ ∧
      F ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (((T ω).toNNReal : ℝ≥0) : ℝ))
    (hE : Measurable[mΩ, hittingSigma]
      (wallsHullAt Γ (fun t ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) T))
    (hS1 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A γ q] M → ∀ r : ℝ≥0,
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ drivingFiltration P hX r] ({ω | T ω < r} ∩ M))
    (hS2 : ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0))
      (N : ℕ), ∀ M, MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
        MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
          ({ω | T ω = (σ ω : ℝ≥0∞)} ∩ ({ω | T ω < N} ∩ M)))
    (hS0 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, drivingFiltration P hX r] M) :
    PocketStopWallsLaw 𝓦 P A γ Γ F (centredField h u₀) q := by
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  exact pocketStopWallsLaw_of_filtration (K := fun t ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))
    (measurable_centredField hC.2.1 u₀) hXm hΓ hW
    (fun ω a b hab => WangWu.fwdHull_mono (by exact_mod_cast hab)) hKad hKst
    (fun τ hτ hfin => isHistoryAvoidanceLocal_hull_of_coupling hC hκ hu₀ hX hζ hKm τ hτ hfin) hT hE hS1 hS2 hS0

end Coupling

end InteractingSLE.Sec7.PocketStopWalls
