import QuantumZipper.Proofs.Section5.Prop17PalmZoomFree
import QuantumZipper.Proofs.LQG.AtomlessUncond
import QuantumZipper.Proofs.LQG.Positivity
import QuantumZipper.Proofs.LQG.AreaOffsets
import QuantumZipper.Proofs.LQG.WedgeBdryInfA

/-!
# Proposition 1.7, node D4⁺ (Palm zoom): boundary regularity of the normalized free field (PALMZOOM)

Part of node 1 (`Prop17FreeRegStmt`): almost surely the normalized free field `N_ϖ X` is good,
and its boundary measure is atomless, charges every open interval and has infinite mass to the
right of every point. Assembled from the project's M4 results (M4-T1 constants
`GoodSample.qBoundaryMeasure_addConst`, M4-P2 `Positivity.ae_forall_pos_qBoundaryMeasure_Ioo`,
M4-P5 `AtomlessUncond.ae_noAtoms_free'`, `AreaOffsets.ae_isLQGGood`) and the free-field boundary
infinite mass `WedgeBdry.wedgeBdryFreeInfStmt_holds` (with `α'' = 0`) plus local finiteness
(`S5.isLocallyFiniteMeasure_qBoundaryMeasure`). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open PalmNorm

/-- `N_ϖ X = X − X(ϖ)`, as an `addConst`. -/
theorem freeFieldN_eq_addConst (ϖ : Measure ℂ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) :
    freeFieldN ϖ X ω = addConst (X ω) (-(X ω ϖ)) := by
  have h0 : ofFun (0 : ℂ → ℝ) + X ω = X ω := AreaCircles.ofFun_zero_add' (X ω)
  simp only [freeFieldN, normAt, h0]

/-- A locally finite measure on `ℝ` with infinite mass on `[1, ∞)` has infinite mass on every
`[x, ∞)`. -/
theorem measure_Ici_eq_top_of_Ici_one {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (h1 : ν (Ici 1) = ⊤) (x : ℝ) : ν (Ici x) = ⊤ := by
  by_contra hx
  have hsub : Ici (1 : ℝ) ⊆ Icc 1 (max x 1) ∪ Ici x := by
    intro t ht
    by_cases htx : x ≤ t
    · exact Or.inr htx
    · exact Or.inl ⟨ht, (lt_of_not_ge htx).le.trans (le_max_left _ _)⟩
  have hc : ν (Icc 1 (max x 1)) < ⊤ := isCompact_Icc.measure_lt_top
  have := (measure_mono (μ := ν) hsub).trans (measure_union_le _ _)
  rw [h1, top_le_iff] at this
  exact (ENNReal.add_ne_top.2 ⟨hc.ne, hx⟩) this

/-- **Boundary regularity of the normalized free field.** -/
theorem ae_freeFieldN_bdry {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (ϖ : Measure ℂ) :
    ∀ᵐ ω ∂P, IsLQGGood γ (freeFieldN ϖ X ω) ∧
      (∀ t : ℝ, qBoundaryMeasure γ (freeFieldN ϖ X ω) {t} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ (freeFieldN ϖ X ω) (Ioo u v)) ∧
      ∀ x : ℝ, qBoundaryMeasure γ (freeFieldN ϖ X ω) (Ici x) = ⊤ := by
  have hQ : (0 : ℝ) < Qc γ := by unfold Qc; positivity
  filter_upwards [AreaOffsets.ae_isLQGGood hX hγ hγ2, AtomlessUncond.ae_noAtoms_free' hX hγ hγ2,
    Positivity.ae_forall_pos_qBoundaryMeasure_Ioo hX hγ hγ2,
    WedgeBdry.wedgeBdryFreeInfStmt_holds P X hX γ hγ hγ2 0 hQ] with ω hg hat hpos hinf
  set ν := qBoundaryMeasure γ (X ω) with hν
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * -(X ω ϖ) / 2)) with hk
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hmeas : qBoundaryMeasure γ (freeFieldN ϖ X ω) = k • ν := by
    rw [freeFieldN_eq_addConst, GoodSample.qBoundaryMeasure_addConst hg]
  have hν1 : ν (Ici 1) = ⊤ := by
    rw [← hinf, ← setLIntegral_one]
    refine setLIntegral_congr_fun measurableSet_Ici fun t _ => ?_
    simp
  have hne : ν ≠ 0 := by
    intro h0
    have := hpos 0 1 one_pos
    rw [h0] at this
    simp at this
  have : IsLocallyFiniteMeasure ν := S5.isLocallyFiniteMeasure_qBoundaryMeasure hne
  refine ⟨freeFieldN_eq_addConst ϖ X ω ▸ hg.addConst _, fun t => ?_, fun u v huv => ?_, fun x => ?_⟩
  · rw [hmeas, Measure.smul_apply, measure_singleton, smul_zero]
  · rw [hmeas, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hk0 (hpos u v huv).ne'
  · rw [hmeas, Measure.smul_apply, smul_eq_mul, measure_Ici_eq_top_of_Ici_one hν1 x,
      ENNReal.mul_top hk0]

end Raw
end FieldLaw
end S5
end QuantumZipper
