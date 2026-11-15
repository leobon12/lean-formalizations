/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1PropConfig
import InteractingSLE.Spec.Supplement.GW4LeafClock

/-!
# Proposition BW1: the contact time `T` is the first contact with the completed piece

Packet PROVE-BW1-PROP. Proposition BW1 puts `T = inf{t : η(t) ∈ A}`, in the frozen statement
`firstTipTime infinitySourceChart W' (SB.prefixPhysSet … 1)` (the first time the physical tip of the counterflow lies
in the root or the piece). The relative configuration (`BW1PropConfig`, GB6's machinery) is stated before
`T_c = firstContactTime (sphereInv ∘ γ) (α([0, ζ]))`. They agree:

* `prefixPhysSet_one_eq`: on the threshold event the physical set of BW1's program after its first instruction is the
  trace range `α([0, ζ])` of the piece (the root `0 = α(0)` is in it);
* `firstTipTime_eq_firstContactTime`: for a counterflow driver with a complete generating trace `γ`, the first time its
  physical tip (through the inversion) lies in a set `A ⊆ ℂ` is the first time `sphereInv ∘ γ` lies in `A`;
* **`firstTipTime_prefixPhysSet_eq`**: hence `T = T_c` for BW1's first piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Prop

open Exist Exist.Staged Exist.StagedLaw
open Supp8.GB6 (firstContactTime sphereInv)

/-- **The physical set of BW1's first piece** (lifetime at most the instruction time): the trace range `α([0, ζ])`. -/
theorem prefixPhysSet_one_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {gw2 : Bool} {θ : ℝ} {t : ℝ≥0∞}
    {rest : List Instr} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hle : (D 0).2 ≤ t) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (D 0).1 (D 0).2 α) (hW : ContinuousOn (D 0).1 {s | (s : ℝ≥0∞) ≤ (D 0).2})
    (hW0 : (D 0).1 0 = 0) :
    SB.prefixPhysSet κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ D 1 = α '' {s | (s : ℝ≥0∞) ≤ (D 0).2} := by
  have e1 := BW1Term.pieces_launch (ExplState.init 0) 0 (D 0) θ t
  have e2 := BW1Term.arcs_launch (ExplState.init 0) 0 (D 0) θ t
  have hc : Continuous (Chart.id.recenter 0).2.1 := by
    simp only [Chart.id, Chart.recenter]
    fun_prop
  have htip := CounterflowRange.tipSet_stopped_eq hc hα hW hW0
  have hid : (Chart.id.recenter 0).2.1 = id := by
    funext z
    simp [Chart.id, Chart.recenter]
  rw [hid, image_id] at htip
  have hmin : min t (D 0).2 = (D 0).2 := min_eq_right hle
  have h0 : (0 : ℂ) ∈ α '' {s | (s : ℝ≥0∞) ≤ (D 0).2} := ⟨0, by simp, hα.1⟩
  simp only [SB.prefixPhysSet, run_one_eq_launch, e1, e2, hmin]
  have hpieces : (ExplState.init 0).1 = [] := rfl
  have harcs : (ExplState.init 0).2.1 = [] := rfl
  have hchart : (ExplState.init 0).2.2.2.2.1 = Chart.id.recenter 0 := rfl
  rw [hpieces, harcs, hchart]
  simp only [List.nil_append, List.mem_singleton, iUnion_iUnion_eq_left, List.not_mem_nil, iUnion_of_empty,
    iUnion_empty, union_empty, Complex.ofReal_zero]
  rw [htip]
  exact union_eq_right.2 (singleton_subset_iff.2 h0)

/-- **The first physical tip time through the inversion is the first contact time of `sphereInv ∘ γ`.** -/
theorem firstTipTime_eq_firstContactTime {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) (A : Set ℂ) :
    firstTipTime infinitySourceChart W A =
      firstContactTime (fun s => sphereInv (γ s : OnePoint ℂ)) ((fun z : ℂ => (z : OnePoint ℂ)) '' A) := by
  unfold firstTipTime firstContactTime
  refine iInf_congr fun s => iInf_congr_Prop ?_ fun _ => rfl
  constructor
  · rintro ⟨z, hzA, hz⟩
    obtain ⟨hne, rfl⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hγ hW hW0 s z).1 hz
    exact ⟨_, hzA, (Supp8.GB6.sphereInv_coe_of_ne hne).symm⟩
  · rintro ⟨z, hzA, hz⟩
    change ((z : ℂ) : OnePoint ℂ) = sphereInv (γ s : OnePoint ℂ) at hz
    by_cases hne : γ s = 0
    · simp only [hne, Supp8.GB6.sphereInv_coe, ↓reduceIte] at hz
      exact absurd hz (OnePoint.coe_ne_infty z)
    · rw [Supp8.GB6.sphereInv_coe_of_ne hne] at hz
      have hz' : z = -(γ s)⁻¹ := OnePoint.coe_injective hz
      exact ⟨z, hzA, (GW4Leaf.tipAt_infinitySourceChart_iff hγ hW hW0 s z).2 ⟨hne, hz'⟩⟩

/-- **BW1's contact time is the first contact with the completed piece**: on the threshold event (lifetime at most
the instruction time, finite), for a regular piece with trace `α` and a counterflow driver with complete generating
trace `γ`, `firstTipTime infinitySourceChart W (prefixPhysSet … 1) = firstContactTime (sphereInv ∘ γ) (α([0, ζ]))`. -/
theorem firstTipTime_prefixPhysSet_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {gw2 : Bool} {θ : ℝ} {t : ℝ≥0∞}
    {rest : List Instr} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hle : (D 0).2 ≤ t) (hfin : (D 0).2 ≠ ⊤) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (D 0).1 (D 0).2 α) (hWα : ContinuousOn (D 0).1 {s | (s : ℝ≥0∞) ≤ (D 0).2})
    (hWα0 : (D 0).1 0 = 0) {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W)
    (hW0 : W 0 = 0) :
    firstTipTime infinitySourceChart W (SB.prefixPhysSet κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ D 1) =
      firstContactTime (fun s => sphereInv (γ s : OnePoint ℂ))
        ((fun s => (α s : OnePoint ℂ)) '' Icc 0 (D 0).2.toNNReal) := by
  rw [prefixPhysSet_one_eq hle hα hWα hWα0, firstTipTime_eq_firstContactTime hγ hW hW0, image_image]
  congr 2
  ext s
  simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and]
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]

end InteractingSLE.Theorem14.BW1Prop
