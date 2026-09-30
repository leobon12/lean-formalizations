import QuantumZipper.Proofs.Thm18.G1ZoomNodes
import QuantumZipper.Proofs.Thm18.G4WedgeRightInf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-BDRY (1): node B0 from the boundary transport of the side map

Theorem 1.8, node G1, zoom half, node **B0** `G1SideBdryRegStmt` (G1ZoomNodes.lean), decision D48.

## Route (sources)

The side field is `Z = Y ∘ ψ + Q log|ψ'|`, `ψ` the inverse uniformizer of the side component.
Its boundary measure on the real side half-line `S` (`(−∞,0)` left, `(0,∞)` right) is the
pullback of the wedge boundary measure `ν_Y|_S` under the boundary homeomorphism `Φ = ψ|_S`,
which fixes `0` and maps `S` onto `S`: conformal coordinate change of the boundary measure,
Duplantier–Sheffield arXiv:0808.1560 Prop. 3.1 and §6 (M4-T4 here) and, because `ψ` is random,
Sheffield–Wang arXiv:1605.06171 **Theorem 4.3** (p. 19; all maps at once), and Sheffield
arXiv:1012.4797 §1.4 (quantum length is intrinsic to the surface). This transport is the named
node `G1SideTransportStmt` below (reduced further in `G1ZBdryTransp.lean`).

Given the transport, B0 is deterministic measure theory (own elementary argument) plus the
proved wedge facts for `α = γ − 2/γ`:
* atomless and positive on open intervals: `ae_atomless_pos_wedge` (G4.lean);
* `ν_Y[0,∞) = ∞`: `wedgeRightInfStmt_holds`; `ν_Y(−∞,0] = ∞`: `Wire4.wedgeLeftInfStmt`
  (Sheffield §1.6);
* local finiteness of `ν_Y` (`S5.isLocallyFiniteMeasure_qBoundaryMeasure`, `ν_Y ≠ 0`).

Main results: `G1SideTransportStmt`, `g1SideBdryReg_det`, **`g1SideBdryRegStmt_of_transport`**.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-- **Boundary transport along the side map** (node, see the module docstring for sources):
a.s. there is an order isomorphism `Φ` of `ℝ` fixing `0` (the boundary values of `ψ` on the
side half-line `S`) such that the side boundary measure is the pullback of `ν_Y|_S` by `Φ`. -/
def G1SideTransportStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ᵐ ω ∂P, ∃ Φ : ℝ ≃o ℝ, Φ 0 = 0 ∧ g1SideNu γ left (g1SideField γ B Y left ω) =
      ((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf left)).map Φ.symm

theorem measurableSet_g1SideHalf (left : Bool) : MeasurableSet (g1SideHalf left) := by
  cases left <;> simp [g1SideHalf, measurableSet_Iio, measurableSet_Ioi]

theorem image_g1SideHalf {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) (left : Bool) :
    Φ '' g1SideHalf left = g1SideHalf left := by
  cases left <;> simp [g1SideHalf, OrderIso.image_Iio, OrderIso.image_Ioi, h0]

/-- Evaluation of the pulled-back measure. -/
theorem pull_apply {μ : Measure ℝ} {S A : Set ℝ} (Φ : ℝ ≃o ℝ)
    (hA : MeasurableSet A) : ((μ.restrict S).map Φ.symm) A = μ (Φ '' A ∩ S) := by
  rw [Measure.map_apply Φ.symm.continuous.measurable hA, Measure.restrict_apply
    (Φ.symm.continuous.measurable hA)]
  congr 2
  ext x
  constructor
  · intro hx
    exact ⟨Φ.symm x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/-- **Deterministic B0**: the four clauses for the pullback of a measure that is atomless,
positive on open intervals, locally finite, and infinite on `(−∞,0]` and `[0,∞)`. -/
theorem g1SideBdryReg_det {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (hatom : ∀ t : ℝ, μ {t} = 0) (hpos : ∀ u v : ℝ, u < v → 0 < μ (Ioo u v))
    (hL : μ (Iic 0) = ⊤) (hR : μ (Ici 0) = ⊤) {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) (left : Bool) :
    let ν := (μ.restrict (g1SideHalf left)).map Φ.symm
    (∀ t : ℝ, ν {t} = 0) ∧
      (∀ u v : ℝ, u < v → Ioo u v ⊆ g1SideHalf left → 0 < ν (Ioo u v)) ∧
      (∀ b ∈ g1SideHalf left, ν (g1SideSeg left b) < ⊤) ∧ ν (g1SideHalf left) = ⊤ := by
  intro ν
  have hS := measurableSet_g1SideHalf left
  have hIm := image_g1SideHalf h0 left
  refine ⟨fun t => ?_, fun u v huv hsub => ?_, fun b _ => ?_, ?_⟩
  · rw [pull_apply Φ (measurableSet_singleton t), image_singleton]
    exact measure_mono_null inter_subset_left (hatom _)
  · rw [pull_apply Φ measurableSet_Ioo, OrderIso.image_Ioo,
      inter_eq_left.2 ((OrderIso.image_Ioo Φ u v) ▸ hIm ▸ image_mono hsub)]
    exact hpos _ _ (Φ.strictMono huv)
  · have hseg : MeasurableSet (g1SideSeg left b) := by
      cases left <;> simp [g1SideSeg, measurableSet_Icc]
    rw [pull_apply Φ hseg]
    refine (measure_mono inter_subset_left).trans_lt ?_
    cases left
    · show μ (Φ '' Icc 0 b) < ⊤
      rw [OrderIso.image_Icc]; exact measure_Icc_lt_top
    · show μ (Φ '' Icc b 0) < ⊤
      rw [OrderIso.image_Icc]; exact measure_Icc_lt_top
  · rw [pull_apply Φ hS, hIm, inter_self]
    cases left
    · show μ (Ioi 0) = ⊤
      have hsub : Ici (0 : ℝ) ⊆ Ioi 0 ∪ {0} := fun x hx => by
        rcases (mem_Ici.1 hx).lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h.symm
      have := (measure_mono (μ := μ) hsub).trans (measure_union_le _ _)
      rw [hR, hatom, add_zero] at this
      exact top_le_iff.1 this
    · show μ (Iio 0) = ⊤
      have := measure_union_le (μ := μ) (Iio (0 : ℝ)) {0}
      rw [Iio_union_right, hL, hatom, add_zero] at this
      exact top_le_iff.1 this

/-- **Node B0 from the side boundary transport.** -/
theorem g1SideBdryRegStmt_of_transport (hT : G1SideTransportStmt) : G1SideBdryRegStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  have ⟨hγ, hγ2, _, hW, _⟩ := hS
  filter_upwards [hT γ P B Y hS hIn left, ae_atomless_pos_wedge hS hIn,
    Wire4.wedgeLeftInfStmt γ P Y hγ hγ2 hW, wedgeRightInfStmt_holds γ P Y hγ hγ2 hW]
    with ω ⟨Φ, h0, hν⟩ ⟨hatom, hpos⟩ hL hR
  have hne : qBoundaryMeasure γ (Y ω) ≠ 0 := by
    intro h
    have h1 := hpos 0 1 one_pos
    rw [h] at h1
    simp at h1
  have := S5.isLocallyFiniteMeasure_qBoundaryMeasure hne
  rw [hν]
  exact g1SideBdryReg_det hatom hpos hL hR h0 left

end Thm18Asm
end QuantumZipper
