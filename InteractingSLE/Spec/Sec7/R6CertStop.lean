/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedMeas
import InteractingSLE.Spec.Sec7.Lemma72CLocal
import InteractingSLE.WangWu.ReverseContactMartFilt2Markov

/-!
# R.6 at two relative times: the joint walls–hull law at the later of two marked stops

PROVE-R6-CERT. Supplement §5.5–§5.6 (`source/spec/p433-480.md` L1000–L1050, pp. 474–477): R.6 compares the outer
pocket's mean with the inner pocket's mean through the nested marked local-set law ("apply the nested marked
local-set law to the enlarged stop `T ∨ s`, exactly as in Aux. 35"). Here the two pockets are read at their **own
deterministic relative times**, i.e. at two marked stops `T₁ = T_C(q)` and `T₂ = T_U(q')` of the walls-enlarged
driving filtration, and the comparison goes through the walls–hull set at the later stop `T₁ ∨ T₂`:

* **`isMarkedStop_max`**: the maximum of two marked stops is a marked stop for the joined marks (the Galmarino
  property of `T₁ ∨ T₂`);
* **`isHistoryAvoidanceLocal_walls_regHull_markedStop`**: Aux. 35's walls–hull law for the regularized hull of a
  frozen coupling at **any** marked stop, with arbitrary marks (`PocketStopWallsFin.pocketStopWallsLaw_regHull`
  without the prefix-σ-algebra packaging);
* **`isHistoryAvoidanceLocal_pair_of_joint`**, **`isHistoryAvoidanceLocal_of_joint`**: two random sets that are
  hitting-measurable for the joint marks and cover the joint walls–hull set have the pair-marked union law of
  `PocketStopSide.ae_tendsto_sub_of_marked_union`; one such set alone is history-marked local.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cert

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open PocketStopWallsFin PocketStopWalls WholeField

/-! ### The later of two marked stops -/

section Max

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The maximum of two marked stops is a marked stop for the joined marks** (Galmarino form): on
`{T₁ ∨ T₂ ≤ σ} = {T₁ ≤ σ} ∩ {T₂ ≤ σ}` every mark of either stop is an event of `σ(X) ∨ 𝓕_σ`. -/
theorem isMarkedStop_max {ℳ₁ ℳ₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {X : Ω → 𝒳} {T₁ T₂ : Ω → ℝ≥0∞} (h₁ : IsMarkedStop ℳ₁ 𝓕 X T₁) (h₂ : IsMarkedStop ℳ₂ 𝓕 X T₂) :
    IsMarkedStop (ℳ₁ ⊔ ℳ₂) 𝓕 X (fun ω => max (T₁ ω) (T₂ ω)) := by
  intro σ hσ M hM
  set 𝒮 : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace with h𝒮
  have hD₁ : MeasurableSet[𝒮] {ω | T₁ ω ≤ (σ ω : ℝ≥0∞)} := by
    simpa only [inter_univ] using h₁ σ hσ univ (@MeasurableSet.univ _ ℳ₁)
  have hD₂ : MeasurableSet[𝒮] {ω | T₂ ω ≤ (σ ω : ℝ≥0∞)} := by
    simpa only [inter_univ] using h₂ σ hσ univ (@MeasurableSet.univ _ ℳ₂)
  have eD : {ω | max (T₁ ω) (T₂ ω) ≤ (σ ω : ℝ≥0∞)} =
      {ω | T₁ ω ≤ (σ ω : ℝ≥0∞)} ∩ {ω | T₂ ω ≤ (σ ω : ℝ≥0∞)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, max_le_iff]
  have hD : MeasurableSet[𝒮] {ω | max (T₁ ω) (T₂ ω) ≤ (σ ω : ℝ≥0∞)} := by
    rw [eD]; exact hD₁.inter hD₂
  have hle : ℳ₁ ⊔ ℳ₂ ≤ PocketStopMarked.traceSigma 𝒮 _ hD := by
    refine sup_le (fun N hN => ?_) (fun N hN => ?_)
    · show MeasurableSet[𝒮] ({ω | max (T₁ ω) (T₂ ω) ≤ (σ ω : ℝ≥0∞)} ∩ N)
      have e : {ω | max (T₁ ω) (T₂ ω) ≤ (σ ω : ℝ≥0∞)} ∩ N =
          ({ω | T₁ ω ≤ (σ ω : ℝ≥0∞)} ∩ N) ∩ {ω | T₂ ω ≤ (σ ω : ℝ≥0∞)} := by
        rw [eD]; ext ω; simp only [mem_inter_iff]; tauto
      rw [e]; exact (h₁ σ hσ N hN).inter hD₂
    · show MeasurableSet[𝒮] ({ω | max (T₁ ω) (T₂ ω) ≤ (σ ω : ℝ≥0∞)} ∩ N)
      have e : {ω | max (T₁ ω) (T₂ ω) ≤ (σ ω : ℝ≥0∞)} ∩ N =
          ({ω | T₂ ω ≤ (σ ω : ℝ≥0∞)} ∩ N) ∩ {ω | T₁ ω ≤ (σ ω : ℝ≥0∞)} := by
        rw [eD]; ext ω; simp only [mem_inter_iff]; tauto
      rw [e]; exact (h₂ σ hσ N hN).inter hD₁
  exact hle M hM

end Max

/-! ### The walls–hull law of a frozen coupling at an arbitrary marked stop -/

section Law

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **Aux. 35's walls–hull law at an arbitrary marked stop, arbitrary marks** (the content of
`PocketStopWallsFin.pocketStopWallsLaw_regHull` before its packaging with the prefix σ-algebra): the regularized hull
of a frozen coupling with almost surely infinite lifetime, walls `Γ` satisfying the determined-locality criterion for
the information `X`, a marked stop `T` with marks `ℳ ≤ σ(X) ∨ 𝓕_∞`. -/
theorem isHistoryAvoidanceLocal_walls_regHull_markedStop {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
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
    {T : Ω → ℝ≥0∞} (hG : IsMarkedStop ℳ (drivingFiltration P hX) X T)
    (hS0 : ∀ M, MeasurableSet[ℳ] M →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, drivingFiltration P hX r] M) :
    IsHistoryAvoidanceLocal ℳ (wallsHullAt Γ (regHull W ζ) T) (centredField h u₀) P := by
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  exact isHistoryAvoidanceLocal_walls_hull_filtration (measurable_centredField hC.2.1 u₀) hXm hΓ hW
    (regHull_mono W ζ) (fun t U hUo hUH => measurableSet_disjoint_regHull hC hκ hX hζ t U hUo hUH)
    (fun τ hτ hfin U hUo hUH => measurableSet_disjoint_regHull_stopping hC hκ hX hζ τ hτ hfin U hUo hUH)
    (fun τ hτ hfin => isHistoryAvoidanceLocal_regHull hC hκ hu₀ hX hζ τ hτ hfin)
    (fun M hM r => measurableSet_lt_inter_of_isMarkedStop hG hM r)
    (fun σ hσ N M hM => measurableSet_eq_inter_of_isMarkedStop hG σ hσ N hM) hS0

end Law

/-! ### Pair-marked union laws from a joint law -/

section Pair

variable {Ω : Type*} {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The pair-marked union law from a joint law**: two random sets, hitting-measurable for the marks `ℳ` of a
history-marked local set `E₀` that they cover almost surely, have the pair-marked union law (marks: their own two
hitting σ-algebras) required by `PocketStopSide.ae_tendsto_sub_of_marked_union`. -/
theorem isHistoryAvoidanceLocal_pair_of_joint {E₀ E₁ E₂ : Ω → Set ℂ}
    (hJoint : IsHistoryAvoidanceLocal ℳ E₀ h P) (h₁ : Measurable[ℳ, hittingSigma] E₁)
    (h₂ : Measurable[ℳ, hittingSigma] E₂) (hcov : ∀ᵐ ω ∂P, E₀ ω ⊆ E₁ ω ∪ E₂ ω) :
    IsHistoryAvoidanceLocal
      (MeasurableSpace.comap E₁ hittingSigma ⊔ MeasurableSpace.comap E₂ hittingSigma)
      (fun ω => E₁ ω ∪ E₂ ω) h P :=
  WangWu.IsHistoryAvoidanceLocal.mono_marks
    (Lemma72C.isHistoryAvoidanceLocal_mono_set hJoint (@LocalSets.measurable_union_hitting Ω ℳ _ _ h₁ h₂) hcov)
    (sup_le h₁.comap_le h₂.comap_le)

/-- **One covering set of a joint law is history-marked local** for the joint marks. -/
theorem isHistoryAvoidanceLocal_of_joint {E₀ E₁ : Ω → Set ℂ}
    (hJoint : IsHistoryAvoidanceLocal ℳ E₀ h P) (h₁ : Measurable[ℳ, hittingSigma] E₁)
    (hcov : ∀ᵐ ω ∂P, E₀ ω ⊆ E₁ ω) : IsHistoryAvoidanceLocal ℳ E₁ h P :=
  Lemma72C.isHistoryAvoidanceLocal_mono_set hJoint h₁ hcov

end Pair

end InteractingSLE.Sec7.R6Cert
