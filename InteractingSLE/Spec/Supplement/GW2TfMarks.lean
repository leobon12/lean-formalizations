/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TdIncl

/-!
# Marks of the capped schedule: the retained past on the success event, and trace σ-algebras

Packet PROVE-GW2-RELDET (`GW2TcCurve.SchedPhysCurveStatement`, its time-ordered case). The explored marks contain the
history records and the explored path. On `oldSuccess` both are read off the retained past of the capped program.

* **`pastMap_of_allSucc_pred`**: if all pieces before the last succeeded, the retained past of the first `k`
  instructions is the sequence of their records. This is `GW2Schedule.pastMap_of_allSucc` with the last piece allowed to
  die, since a piece's record only needs the earlier pieces' success.
* `comap_centredField`: centring by a deterministic distribution does not change the field σ-algebra.
* **`traceSigma P E ℋ₀`**: the events that agree almost surely on `E` with an event of `ℋ₀`. It is a σ-algebra
  containing `ℋ₀` and the null sets. **`comap_le_traceSigma`**: it contains `σ(g)` when, almost surely on `E`, `g` is
  a Borel function of an `ℋ₀`-measurable map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw GW2Schedule

/-- **The retained past is the sequence of records when all pieces before the last succeeded.** -/
theorem pastMap_of_allSucc_pred {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec} {θ : ℕ → ℝ}
    {Δ : ℕ → ℝ≥0∞} {Ω : Type*} (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k ≤ spec.2.2.length) {ω : Ω}
    (hs : AllSucc Δ (fun j => E j ω) (k - 1)) :
    pastMap κ b jumps spec E k ω = fun i : Fin k => recOf (Δ i) (E i ω) := by
  funext i
  change readRec ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.1 i) = _
  rw [retained_run_of_lt spec _ i.2,
    retained_run_gw2 hgw hprog hΔ _ (lt_of_lt_of_le i.2 hk) (hs.mono (Nat.le_sub_one_of_lt i.2))]
  rfl

/-- Centring by a deterministic distribution does not change the field σ-algebra. -/
theorem comap_centredField {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) :
    MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance = MeasurableSpace.comap h inferInstance :=
  WholeField.comap_sub_dist h _

section Trace

variable {Ω : Type*} {ℋ₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **The trace σ-algebra**: events agreeing almost surely on `E` with an event of `ℋ₀`. -/
@[instance_reducible]
def traceSigma (P : Measure Ω) (E : Set Ω) (ℋ₀ : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' F := ∃ F₀, MeasurableSet[ℋ₀] F₀ ∧ E ∩ F =ᵐ[P] E ∩ F₀
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ ℋ₀, EventuallyEq.rfl⟩
  measurableSet_compl F := by
    rintro ⟨F₀, hF₀, hEF⟩
    refine ⟨F₀ᶜ, hF₀.compl, ?_⟩
    filter_upwards [hEF] with ω hω
    have hω' : (ω ∈ E ∩ F) = (ω ∈ E ∩ F₀) := hω
    change (ω ∈ E ∩ Fᶜ) = (ω ∈ E ∩ F₀ᶜ)
    simp only [mem_inter_iff, mem_compl_iff] at hω' ⊢
    by_cases hE : ω ∈ E
    · simp only [hE, true_and] at hω' ⊢
      rw [hω']
    · simp only [hE, false_and]
  measurableSet_iUnion f hf := by
    choose F₀ hF₀ hEF using hf
    refine ⟨⋃ i, F₀ i, MeasurableSet.iUnion hF₀, ?_⟩
    rw [inter_iUnion, inter_iUnion]
    exact EventuallyEqSet.countable_iUnion hEF

theorem le_traceSigma (P : Measure Ω) (E : Set Ω) : ℋ₀ ≤ traceSigma P E ℋ₀ :=
  fun F hF => ⟨F, hF, EventuallyEq.rfl⟩

theorem nullSets_le_traceSigma (P : Measure Ω) (E : Set Ω) :
    Ito.nullSets P ≤ traceSigma P E ℋ₀ := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨-, hs⟩
  refine ⟨∅, @MeasurableSet.empty _ ℋ₀, ?_⟩
  have h0 : ∀ᵐ ω ∂P, ω ∉ s := measure_eq_zero_iff_ae_notMem.1 hs
  filter_upwards [h0] with ω hω
  simp only [mem_inter_iff, hω, and_false, mem_empty_iff_false]

/-- **A map that is, almost surely on `E`, a Borel function of an `ℋ₀`-measurable map generates trace events.** -/
theorem comap_le_traceSigma {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (P : Measure Ω) (E : Set Ω)
    {g : Ω → X} {ψ : Ω → Y} {φ : Y → X} (hψ : Measurable[ℋ₀] ψ) (hφ : Measurable φ)
    (hg : ∀ᵐ ω ∂P, ω ∈ E → g ω = φ (ψ ω)) :
    MeasurableSpace.comap g inferInstance ≤ traceSigma P E ℋ₀ := by
  rintro _ ⟨B, hB, rfl⟩
  refine ⟨ψ ⁻¹' (φ ⁻¹' B), hψ (hφ hB), ?_⟩
  filter_upwards [hg] with ω hω
  by_cases hE : ω ∈ E
  · simp only [mem_inter_iff, hE, true_and, mem_preimage, hω hE]
  · simp only [mem_inter_iff, hE, false_and]

end Trace

end InteractingSLE.Theorem14.GW2Rd
