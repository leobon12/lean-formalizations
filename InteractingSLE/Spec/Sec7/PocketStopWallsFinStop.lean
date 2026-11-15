/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsFinHull
import InteractingSLE.Spec.Sec7.PocketStopWallsFinReflect
import InteractingSLE.Spec.Sec7.PocketStopWallsFinField

/-!
# `PocketStopWallsLaw` at the left end `T⁰(q)`: the stop in Galmarino form and the assembly

Packet PROVE-STRIPSYS41 (PROVE-STRIPSYS37 §5.3–§5.4). PROVE-STRIPSYS37's core
`isHistoryAvoidanceLocal_walls_hull_filtration` needs two raw properties of the stop `T` with the marks `ℳ`: on
`{T < r}` the marks are events of `σ(X) ∨ 𝓕_r` (`hS1`), and on `{T = σ} ∩ {T < N}` events of `σ(X) ∨ 𝓕_σ` for every
`𝓕`-stopping time `σ` (`hS2`). Both follow from one statement:

* `IsMarkedStop 𝓕 X ℳ T` — for every `ℝ≥0`-valued `𝓕`-stopping time `σ` and every mark `M`,
  `{T ≤ σ} ∩ M ∈ σ(X) ∨ 𝓕_σ` (the stop is a stopping time of the initially enlarged filtration `σ(X) ∨ 𝓕_t` with the
  marks in its stopped σ-algebra, read at the stopping times of `𝓕`; for the left end `T⁰(q) = inf{t : Q(t) ≥ q}` of
  ruling R67 this is the Galmarino property of the walls and the stopped hull process);
* `measurableSet_lt_inter_of_isMarkedStop` (`hS1`), `measurableSet_eq_inter_of_isMarkedStop` (`hS2`),
  `measurable_of_isMarkedStop` (the stop is measurable).

The assembly:

* **`pocketStopWallsLaw_regHull`**: `PocketStopWallsLaw` for any random set `F` equal on the live event to the
  regularized hull `K̃_T` of a frozen coupling with infinite lifetime, from the walls' criterion `hW`, `IsMarkedStop`
  and `hS0` — the raw hull hypotheses `hKm`, `hKad`, `hKst`, `hE` of `pocketStopWallsLaw_of_coupling` are discharged
  (`PocketStopWallsFinHull.lean`);
* `stopHull0_eq_regHull`: on a configuration with a continuous driver and infinite lifetime, `stopHull0 = K̃_{T⁰(q)}`
  (the hypothesis `hT`, §5.4);
* **`pocketStopWallsLaw_stopHull0`**: Theorem 1.3's `PocketStopWallsLaw` at `T⁰(q)` for the strip system's change
  pocket, the walls `m(range R ∪ range L)` and the centred field of the counterflow chart, with the walls' input
  transported through `R` (`PocketStopWallsFinReflect.lean`); the remaining inputs are `IsMarkedStop` and `hS0` for
  `T⁰(q)`.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopWallsFin

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

/-! ### The stop in Galmarino form -/

section Galmarino

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The marked stop** (Galmarino form): for every `ℝ≥0`-valued stopping time `σ` of `𝓕` and every mark `M ∈ ℳ`, the
event `{T ≤ σ} ∩ M` is in `σ(X) ∨ 𝓕_σ`. -/
def IsMarkedStop (ℳ : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (X : Ω → 𝒳)
    (T : Ω → ℝ≥0∞) : Prop :=
  ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) (M : Set Ω), MeasurableSet[ℳ] M →
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace] ({ω | T ω ≤ (σ ω : ℝ≥0∞)} ∩ M)

/-- At a constant time `c`, the marked stop gives `{T ≤ c} ∩ M ∈ σ(X) ∨ 𝓕_c`. -/
theorem measurableSet_le_inter_of_isMarkedStop {ℳ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳} {T : Ω → ℝ≥0∞} (hG : IsMarkedStop ℳ 𝓕 X T) (c : ℝ≥0) {M : Set Ω}
    (hM : MeasurableSet[ℳ] M) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 c] ({ω | T ω ≤ (c : ℝ≥0∞)} ∩ M) := by
  have h := hG (fun _ => c) (isStoppingTime_const 𝓕 c) M hM
  rwa [IsStoppingTime.measurableSpace_const] at h

/-- **`hS1` from the marked stop**: `{T < r} ∩ M ∈ σ(X) ∨ 𝓕_r`. -/
theorem measurableSet_lt_inter_of_isMarkedStop {ℳ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳} {T : Ω → ℝ≥0∞} (hG : IsMarkedStop ℳ 𝓕 X T) {M : Set Ω}
    (hM : MeasurableSet[ℳ] M) (r : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 r] ({ω | T ω < r} ∩ M) := by
  have e : {ω | T ω < r} ∩ M = ⋃ q : ℚ, ⋃ (_ : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < r),
      ({ω | T ω ≤ ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)} ∩ M) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hlt, hM⟩
      obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
      exact ⟨q, h2, h1.le, hM⟩
    · rintro ⟨q, hq, h1, hM⟩
      exact ⟨h1.trans_lt hq, hM⟩
  rw [e]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hle : Real.toNNReal q ≤ r := by exact_mod_cast hq.le
  exact (sup_le_sup_left (𝓕.mono hle) _) _ (measurableSet_le_inter_of_isMarkedStop hG _ hM)

/-- **The marked stop is measurable** (for measurable information `X`). -/
theorem measurable_of_isMarkedStop {ℳ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {X : Ω → 𝒳} (hX : Measurable X) {T : Ω → ℝ≥0∞} (hG : IsMarkedStop ℳ 𝓕 X T) : Measurable T := by
  have hlt : ∀ r : ℝ≥0, MeasurableSet {ω | T ω < r} := fun r => by
    have h := measurableSet_lt_inter_of_isMarkedStop hG (@MeasurableSet.univ _ ℳ) r
    rw [inter_univ] at h
    exact (sup_le hX.comap_le (𝓕.le r)) _ h
  refine measurable_of_Iio fun x => ?_
  rcases x with _ | r
  · have e : T ⁻¹' Iio ⊤ = ⋃ n : ℕ, {ω | T ω < ((n : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h.ne
        exact ⟨n, by rwa [ENNReal.coe_natCast]⟩
      · rintro ⟨n, hn⟩
        exact hn.trans ENNReal.coe_lt_top
    rw [ENNReal.none_eq_top, e]
    exact MeasurableSet.iUnion fun n => hlt n
  · exact hlt r

/-- **`hS2` from the marked stop**: `{T = σ} ∩ {T < N} ∩ M ∈ σ(X) ∨ 𝓕_σ` for every `ℝ≥0`-valued stopping time
`σ`. -/
theorem measurableSet_eq_inter_of_isMarkedStop {ℳ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳} {T : Ω → ℝ≥0∞} (hG : IsMarkedStop ℳ 𝓕 X T) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) (N : ℕ) {M : Set Ω} (hM : MeasurableSet[ℳ] M) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      ({ω | T ω = (σ ω : ℝ≥0∞)} ∩ ({ω | T ω < N} ∩ M)) := by
  set 𝒮 : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace with h𝒮
  have hσ𝒮 : hσ.measurableSpace ≤ 𝒮 := le_sup_right
  have hX𝒮 : ∀ B : Set 𝒳, MeasurableSet B → MeasurableSet[𝒮] (X ⁻¹' B) := fun B hB =>
    le_sup_left (a := MeasurableSpace.comap X inferInstance) _ (MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩)
  -- `{σ < N}`
  have hN : MeasurableSet[𝒮] {ω | σ ω < (N : ℝ≥0)} := by
    have h := hσ.measurableSet_lt' (N : ℝ≥0)
    simp only [WithTop.coe_lt_coe] at h
    exact hσ𝒮 _ h
  -- `{T < σ}`
  have hlt : MeasurableSet[𝒮] {ω | T ω < (σ ω : ℝ≥0∞)} := by
    have e : {ω | T ω < (σ ω : ℝ≥0∞)} = ⋃ q : ℚ,
        ({ω | Real.toNNReal q < σ ω} ∩ {ω | T ω ≤ ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · intro h
        obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
        exact ⟨q, by exact_mod_cast h2, h1.le⟩
      · rintro ⟨q, h1, h2⟩
        exact h2.trans_lt (by exact_mod_cast h1)
    rw [e]
    refine MeasurableSet.iUnion fun q => ?_
    set c : ℝ≥0 := Real.toNNReal q with hc
    have hD : MeasurableSet[hσ.measurableSpace] {ω | c < σ ω} := by
      have h := hσ.measurableSet_gt' c
      simpa only [WithTop.coe_lt_coe] using h
    refine PocketStopWalls.measurableSet_inter_of_sup (𝒜 := 𝓕 c) (hσ𝒮 _ hD)
      (fun B hB => (hσ𝒮 _ hD).inter (hX𝒮 B hB)) (fun F hF => ?_) ?_
    · have hc' := isStoppingTime_const 𝓕 c
      have hF' : MeasurableSet[hc'.measurableSpace] F := by rwa [IsStoppingTime.measurableSpace_const]
      have h1 : MeasurableSet[hσ.measurableSpace] (F ∩ {ω | (c : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0)}) :=
        IsStoppingTime.measurableSpace_mono (hc'.min hσ) hσ (fun ω => min_le_right _ _) _
          (IsStoppingTime.measurableSet_inter_le hc' hσ F hF')
      have e' : {ω | c < σ ω} ∩ F =
          (F ∩ {ω | (c : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0)}) ∩ {ω | c < σ ω} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
        exact ⟨fun h => ⟨⟨h.2, h.1.le⟩, h.1⟩, fun h => ⟨h.2, h.1.1⟩⟩
      rw [e']
      exact hσ𝒮 _ (h1.inter hD)
    · have h := measurableSet_le_inter_of_isMarkedStop hG c (@MeasurableSet.univ _ ℳ)
      rwa [inter_univ] at h
  have hA : MeasurableSet[𝒮] ({ω | T ω ≤ (σ ω : ℝ≥0∞)} ∩ M) := hG σ hσ M hM
  have e : {ω | T ω = (σ ω : ℝ≥0∞)} ∩ ({ω | T ω < N} ∩ M) =
      ({ω | T ω ≤ (σ ω : ℝ≥0∞)} ∩ M) ∩ ({ω | σ ω < (N : ℝ≥0)} ∩ {ω | T ω < (σ ω : ℝ≥0∞)}ᶜ) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, not_lt]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1.le, h3⟩, ?_, h1.ge⟩
      have : (σ ω : ℝ≥0∞) < ((N : ℝ≥0) : ℝ≥0∞) := by rw [← h1, ENNReal.coe_natCast]; exact h2
      exact_mod_cast this
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      have heq : T ω = (σ ω : ℝ≥0∞) := le_antisymm h1 h4
      refine ⟨heq, ?_, h3⟩
      rw [heq, ← ENNReal.coe_natCast]
      exact_mod_cast h2
  rw [e]
  exact hA.inter (hN.inter hlt.compl)

end Galmarino

/-! ### `PocketStopWallsLaw` for the regularized hull of a frozen coupling -/

section Assembly

open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **`PocketStopWallsLaw` for the regularized hull of a frozen coupling** (`pocketStopWallsLaw_of_coupling` with the
raw hull hypotheses discharged): the coupling has infinite lifetime almost surely, the walls `Γ` with information `X`
satisfy the determined-locality criterion for the centred field (`hW`), `F` is the regularized hull `K̃_T` on the live
event (`hT`), and the stop is a marked stop with marks in `σ(X) ∨ 𝓕_∞` (`hG`, `hS0`). -/
theorem pocketStopWallsLaw_regHull {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {Γ F : Ω → Set ℂ} {q : ℝ≥0}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {X : Ω → 𝒳} (hXm : Measurable X) (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens (centredField h u₀) (fun ω => G (centredField h u₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => LocalSets.markovCompl G (centredField h u₀ ω)) ⁻¹' B')
    {T : Ω → ℝ≥0∞}
    (hT : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → T ω < ⊤ ∧ F ω = regHull W ζ (T ω).toNNReal ω)
    (hG : IsMarkedStop (locPrefixSigma 𝓦 A γ q) (drivingFiltration P hX) X T)
    (hS0 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, drivingFiltration P hX r] M) :
    PocketStopWallsLaw 𝓦 P A γ Γ F (centredField h u₀) q := by
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  exact pocketStopWallsLaw_of_filtration (K := regHull W ζ) (measurable_centredField hC.2.1 u₀) hXm hΓ hW
    (regHull_mono W ζ) (fun t U hUo hUH => measurableSet_disjoint_regHull hC hκ hX hζ t U hUo hUH)
    (fun τ hτ hfin U hUo hUH => measurableSet_disjoint_regHull_stopping hC hκ hX hζ τ hτ hfin U hUo hUH)
    (fun τ hτ hfin => isHistoryAvoidanceLocal_regHull hC hκ hu₀ hX hζ τ hτ hfin) hT
    (measurable_wallsHullAt_regHull hX hΓ (measurable_of_isMarkedStop hXm hG))
    (fun M hM r => measurableSet_lt_inter_of_isMarkedStop hG hM r)
    (fun σ hσ N M hM => measurableSet_eq_inter_of_isMarkedStop hG σ hσ N hM) hS0

/-- **The walls–hull union law at an arbitrary stopping time for the regularized hull of a frozen coupling**
(PROVE-STRIPSYS37's `isHistoryAvoidanceLocal_walls_hull_stoppingTime`, Aux. lemma 37's flat-clock locality, with the
hull hypotheses discharged): marks `σ(X) ∨ 𝓕_τ`. -/
theorem isHistoryAvoidanceLocal_walls_regHull_stoppingTime [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {X : Ω → 𝒳} (hXm : Measurable X) {Γ : Ω → Set ℂ} (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens (centredField h u₀) (fun ω => G (centredField h u₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => LocalSets.markovCompl G (centredField h u₀ ω)) ⁻¹' B')
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ) :
    IsHistoryAvoidanceLocal (MeasurableSpace.comap X inferInstance ⊔ hτ.measurableSpace)
      (wallsHullAt Γ (regHull W ζ) fun ω => (τ ω : ℝ≥0∞)) (centredField h u₀) P := by
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  exact isHistoryAvoidanceLocal_walls_hull_stoppingTime (measurable_centredField hC.2.1 u₀) hXm hΓ hW
    (regHull_mono W ζ) (fun t U hUo hUH => measurableSet_disjoint_regHull hC hκ hX hζ t U hUo hUH)
    (fun τ hτ hfin U hUo hUH => measurableSet_disjoint_regHull_stopping hC hκ hX hζ τ hτ hfin U hUo hUH)
    (fun τ hτ hfin => isHistoryAvoidanceLocal_regHull hC hκ hu₀ hX hζ τ hτ hfin) hτ

end Assembly

/-! ### The strip system's change pocket -/

section Strip

open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketSeedOpen PocketUnionPt
open WangWu (negInv)

variable {Ω : Type*}

/-- **The stop `T⁰(q)`** as a random time (bounded change pocket; ruling R67). -/
def stopTime0 (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q)

/-- **The stop `T⁰(q)`** as a random time (change pocket opening at the flow seed; ruling R67). -/
def stopTime0Inf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q)

theorem continuous_nnreal_of_continuous_real {W' : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous fun s : ℝ => W' s.toNNReal ω) : Continuous fun s : ℝ≥0 => W' s ω := by
  have h := hc.comp NNReal.continuous_coe
  simpa only [Function.comp_def, Real.toNNReal_coe] using h

/-- **`hT` for `T⁰(q)`** (bounded change pocket): on a configuration whose driver is continuous with infinite lifetime,
`stopHull0 = K̃_{T⁰(q)}`. -/
theorem stopHull0_eq_regHull {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}
    (hc : IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) (hζ : ζ' ω = ⊤) (q : ℝ≥0) :
    stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω =
      regHull W' ζ' (stopTime0 R L r η ψ q ω).toNNReal ω := by
  have hP := IsCfPocketConfig.isReversePocket' hc
  have h0 : 0 ≤ ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q := hP.nonneg.trans (ambTime0_mem hP (ψ ω) q).1
  rw [regHull_eq (continuous_nnreal_of_continuous_real hc.continuous_W) hζ, stopTime0,
    ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal h0]
  rfl

/-- **`hT` for `T⁰(q)`** (change pocket opening at the flow seed). -/
theorem stopHull0Inf_eq_regHull {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}
    (hc : IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) (hζ : ζ' ω = ⊤) (q : ℝ≥0) :
    stopHull0Inf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω =
      regHull W' ζ' (stopTime0Inf R L r η ψ q ω).toNNReal ω := by
  have hP := hc.isReversePocketInf
  have h0 : 0 ≤ ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q :=
    hP.nonneg.trans (le_ambTime0Inf hP hc.attach (ψ ω) q)
  rw [regHull_eq (continuous_nnreal_of_continuous_real hc.continuous_W) hζ, stopTime0Inf,
    ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal h0]
  rfl

/-- The reflected walls are hitting-measurable. -/
theorem measurable_negInv_walls [mΩ : MeasurableSpace Ω] {n : ℕ} {η : Fin n → Ω → ℝ≥0 → ℂ}
    (hc : ∀ i ω, Continuous (η i ω)) (hηm : ∀ i t, Measurable fun ω => η i ω t) :
    Measurable[mΩ, hittingSigma] fun ω => negInv '' ⋃ i, range (η i ω) := by
  refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have hU' : negInv '' U ⊆ H := by
    rintro _ ⟨w, hw, rfl⟩
    exact WangWu.negInv_mem_H (hUH hw)
  have e : (fun ω => negInv '' ⋃ i, range (η i ω)) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      (fun ω => (⋃ i, range (η i ω)) ∩ H) ⁻¹' {S : Set ℂ | (S ∩ negInv '' U).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, ← Set.not_disjoint_iff_nonempty_inter, disjoint_image_negInv_iff hUH]
  rw [e]
  exact measurable_wallsRange hc hηm (LocalSets.measurableSet_hitting (WangWu.isOpen_image_negInv hUo hUH) hU')

theorem iUnion_range_fin_two {α : Type*} (f g : Ω → α → ℂ) (ω : Ω) :
    (⋃ i, range ((![f, g] : Fin 2 → Ω → α → ℂ) i ω)) = range (f ω) ∪ range (g ω) := by
  ext z
  simp only [mem_iUnion, mem_union, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]

end Strip

/-! ### Theorem 1.3's `PocketStopWallsLaw` at `T⁰(q)` -/

section StripLaw

open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop
open WangWu (negInv)

variable {Ω : Type*}

/-- **`PocketStopWallsLaw` at the left end `T⁰(q)` for the bounded change pocket** (Aux. lemma 35's marked union law
of the walls with the counterflow hull, PROVE-STRIPSYS37 §5, ruling R67): the walls `R`, `L` (determined by and
entrance-history local for the centred flow-chart field `centredField h u₀`, a zero-boundary GFF — Lemma 6.2's input
`StripWall.lemma62_walls`), read in the counterflow chart `m = R`; the counterflow a frozen coupling of the field `h''`
(the translate by `0` of the infinity-source transport `h'` of `h`: the data of `IsCenteredCounterflowDriver` and
`IsFlowLineDriver`) with almost surely infinite lifetime; on `A` the configuration holds with lifetime `∞`. The
remaining inputs are the stop's: `IsMarkedStop` for `T⁰(q)` with the walls' full histories as information, and
`hS0`. No determination of the counterflow is used (ruling R48). -/
theorem pocketStopWallsLaw_stopHull0
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {q : ℝ≥0}
    (hG : IsMarkedStop (locPrefixSigma 𝓦 A (travAll R L r η ψ) q) (drivingFiltration P hX) (fullHist ![R, L])
      (stopTime0 R L r η ψ q))
    (hS0 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A (travAll R L r η ψ) q] M →
      MeasurableSet[MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ ⨆ t, drivingFiltration P hX t] M) :
    PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q := by
  have hc2 : ∀ i ω, Continuous ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := Fin.forall_fin_two.2 ⟨hRc, hLc⟩
  have h02 : ∀ i ω, (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 2 → ℂ) i :=
    Fin.forall_fin_two.2 ⟨hR0, hL0⟩
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hdet2 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω) :=
    Fin.forall_fin_two.2 ⟨hdetR, hdetL⟩
  have hloc2 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i) (centredField h u₀) P :=
    Fin.forall_fin_two.2 ⟨hlocR, hlocL⟩
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  rw [hΓe]
  refine pocketStopWallsLaw_regHull hC hκ' hu₀' hX hζ (measurable_fullHist hm2) (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    (fun ω hω _ => ⟨ENNReal.ofReal_lt_top, ?_⟩) hG hS0
  exact stopHull0_eq_regHull (hcfg ω hω) (hζA ω hω) q

/-- **`PocketStopWallsLaw` at the left end `T⁰(q)` for the change pocket opening at the flow seed** (as
`pocketStopWallsLaw_stopHull0`). -/
theorem pocketStopWallsLaw_stopHull0Inf
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {q : ℝ≥0}
    (hG : IsMarkedStop (locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q) (drivingFiltration P hX) (fullHist ![R, L])
      (stopTime0Inf R L r η ψ q))
    (hS0 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q] M →
      MeasurableSet[MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ ⨆ t, drivingFiltration P hX t] M) :
    PocketStopWallsLaw 𝓦 P A (travAllInf R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0Inf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q := by
  have hc2 : ∀ i ω, Continuous ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := Fin.forall_fin_two.2 ⟨hRc, hLc⟩
  have h02 : ∀ i ω, (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 2 → ℂ) i :=
    Fin.forall_fin_two.2 ⟨hR0, hL0⟩
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hdet2 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω) :=
    Fin.forall_fin_two.2 ⟨hdetR, hdetL⟩
  have hloc2 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i) (centredField h u₀) P :=
    Fin.forall_fin_two.2 ⟨hlocR, hlocL⟩
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  rw [hΓe]
  refine pocketStopWallsLaw_regHull hC hκ' hu₀' hX hζ (measurable_fullHist hm2) (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    (fun ω hω _ => ⟨ENNReal.ofReal_lt_top, ?_⟩) hG hS0
  exact stopHull0Inf_eq_regHull (hcfg ω hω) (hζA ω hω) q

/-- **Theorem 1.3's `PocketStopUnionLaw` at the right end `T(q)`** (bounded change pocket; Aux. lemma 124 from Aux.
lemma 35): `pocketStopWallsLaw_stopHull0`, then STRIPSYS35's passage to `B ∪ R_{T⁰(q)}`
(`pocketStopUnionLaw_cfPocket`), then ruling R67's transfer `B ∪ R_{T⁰(q)} = B ∪ R_{T(q)}`. -/
theorem pocketStopUnionLaw_stopHull_strip
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
    (h𝓦 : 𝓦 ≤ mΩ) (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ)
    (hG : IsMarkedStop (locPrefixSigma 𝓦 A (travAll R L r η ψ) q) (drivingFiltration P hX) (fullHist ![R, L])
      (stopTime0 R L r η ψ q))
    (hS0 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A (travAll R L r η ψ) q] M →
      MeasurableSet[MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ ⨆ t, drivingFiltration P hX t] M) :
    PocketStopUnionLaw 𝓦 P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (stopHull R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q :=
  pocketStopUnionLaw_stopHull_of_stopHull0 hcfg hAG
    (pocketStopUnionLaw_cfPocket h𝓦 hRm' hLm' hGm (fun ω hω => (hcfg ω hω).conf) hA hAG hpre
      (pocketStopWallsLaw_stopHull0 hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
        (fun ω hω => hcfg ω (hAG hω)) hζA hG hS0))

/-- **Theorem 1.3's `PocketStopUnionLaw` at the right end `T(q)`** (change pocket opening at the flow seed). -/
theorem pocketStopUnionLaw_stopHullInf_strip
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
    (h𝓦 : 𝓦 ≤ mΩ) (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ)
    (hG : IsMarkedStop (locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q) (drivingFiltration P hX) (fullHist ![R, L])
      (stopTime0Inf R L r η ψ q))
    (hS0 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q] M →
      MeasurableSet[MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ ⨆ t, drivingFiltration P hX t] M) :
    PocketStopUnionLaw 𝓦 P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (stopHullInf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q :=
  pocketStopUnionLaw_stopHullInf_of_stopHull0Inf hcfg hAG
    (pocketStopUnionLaw_cfPocket h𝓦 hRm' hLm' hGm (fun ω hω => (hcfg ω hω).conf) hA hAG hpre
      (pocketStopWallsLaw_stopHull0Inf hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
        (fun ω hω => hcfg ω (hAG hω)) hζA hG hS0))

end StripLaw

end InteractingSLE.Sec7.PocketStopWallsFin
