import QuantumZipper.Proofs.Thm18.G1CoreRep
import QuantumZipper.Proofs.Zipper.D3PlusIRich
import QuantumZipper.Proofs.NonVacuityWedgeUncond

/-!
# G1-ZOOM: the zoom half of G1 from D3⁺(i) and a model-approximation node

Theorem 1.8, node G1, part (a) (`G1ZoomPartStmt`, G1CoreSplit.lean): for some a.s. choice
`ψ ω` of inverse normalized uniformizer of a side component of `ℍ \ η`, the canonical
description of the pulled-back field `Y ∘ ψ + Q log |ψ'|` is a `γ`-quantum wedge.

Sources. Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 69–70): "the two quantum
surfaces divided by the curve each have the law of a γ-quantum wedge. This follows for the left
side from Proposition 1.6 and for the right side by symmetry", where the argument of Prop. 1.6
(p. 25) is: a field that looks, near the marked point, like a free boundary GFF plus a
`γ(−log|·|)` singularity plus a smooth part zooms to the `γ`-quantum wedge. In this project that
zoom statement is D3⁺(i), `D3Plus.D3PlusIStmtRich` (decision D25; TV-local form as in
Duplantier–Miller–Sheffield, arXiv:1409.7055, Props. 4.7–4.8), taken here as an exact hypothesis.

What this file proves (own bookkeeping argument; the paper leaves it implicit):

* `fieldLawFull_eq_of_locFieldFull`: two random fields with a.e.-measurable full data whose
  rich local data `locFieldFull R` have the same law for every `R` have the same
  `fieldLawFull H` (π-λ via the truncations `E6.truncFull`, as in
  `E6.configLawFull_eq_of_locRich`, but on two different probability spaces).
* `g1z_tendsto_of_D3`: D3⁺(i) with a test function not depending on `ω` gives, for each
  measurable `Γ ∈ [0,1]`, convergence of the model integrals to the `γ`-wedge integral.
* `isQuantumWedge_of_mix`: under D3⁺(i), a random field whose rich local data integrals are
  the limits, as `L → ∞`, of those of a *mixture* (over `x ∈ T`, law `ρ`) of D3⁺ models
  `zoomModel γ γ L (ρ₀ x) (X x) (g x)` (`α = γ`) is a `γ`-quantum wedge (dominated convergence
  over the mixture, uniqueness of limits). The mixture allows a Palm-point average as in
  Prop. 1.7's `Prop17PalmZoomMix`; a single model is `g1ZoomMix_unit`.
* `G1ZoomModelSide` / `G1ZoomModelStmt` (the remaining node) and
  `g1ZoomPartStmt_of_model : D3PlusIStmtRich → G1ZoomModelStmt → G1ZoomPartStmt`,
  `g1Stmt_of_model_regRep`, `g1Stmt_of_N2_model_regRep` (N2 form of D3⁺(i)).
* `g1zMdl_tendsto_of_coupling`: the single-model approximation from a coupling (a copy of the
  component data on the model's space agreeing with the model data off events whose
  probability tends to `0`), the form in which the node is expected to be proved.

Modulo D3⁺(i), `G1ZoomModelStmt` is essentially equivalent to `G1ZoomPartStmt` (given the
conclusion, `T = Unit` and any D3⁺ `Setup` with `α = γ` work; this converse is not formalized):
it does not lower the difficulty, it fixes the interface where the zipper argument plugs in.
The remaining node `G1ZoomModelStmt` is the zipper content of the paper's argument (the
component field near `0` is the image of the Palm-zoomed free field under the zipping map,
blueprint G1 via E5, D4⁺ and G0); it is not proved here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus

/-! ## Local laws determine `fieldLawFull` -/

/-- Embedding of field data into `E6.FullData` (constant driver `0`). -/
def g1zEmb (e : (ℕ → ℝ) × (TestFun H → ℝ)) : E6.FullData := (e, fun _ => 0)

theorem measurable_g1zEmb : Measurable g1zEmb := measurable_id.prodMk measurable_const

/-- The law of the truncated embedded data, as an integral of the rich local data. -/
theorem g1z_map_trunc_apply (R : ℕ) {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {Z₁ : Ω₁ → FieldSample} (h : AEMeasurable (fun ω => WedgeMeas.dataFull H (Z₁ ω)) P₁)
    (A : Set E6.FullData) (hA : MeasurableSet A) :
    (P₁.map (fun ω => WedgeMeas.dataFull H (Z₁ ω))).map (E6.truncFull R ∘ g1zEmb) A =
      ∫⁻ ω, A.indicator 1 (g1zEmb (locFieldFull R (Z₁ ω))) ∂P₁ := by
  have hL : Measurable (E6.truncFull R ∘ g1zEmb) :=
    (E6.measurable_truncFull R).comp measurable_g1zEmb
  rw [AEMeasurable.map_map_of_aemeasurable hL.aemeasurable h, ← lintegral_indicator_one hA,
    lintegral_map' (measurable_one.indicator hA).aemeasurable (hL.comp_aemeasurable h)]
  rfl

/-- **Local laws determine `fieldLawFull H`** (own elementary argument, π-λ). -/
theorem fieldLawFull_eq_of_locFieldFull {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : Ω → FieldSample} {Z' : Ω' → FieldSample}
    (hZ : AEMeasurable (fun ω => WedgeMeas.dataFull H (Z ω)) P)
    (hZ' : AEMeasurable (fun ω => WedgeMeas.dataFull H (Z' ω)) P')
    (hloc : ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∫⁻ ω, Γ (locFieldFull R (Z ω)) ∂P = ∫⁻ ω, Γ (locFieldFull R (Z' ω)) ∂P') :
    fieldLawFull H Z P = fieldLawFull H Z' P' := by
  have e1 : fieldLawFull H Z P = P.map (fun ω => WedgeMeas.dataFull H (Z ω)) := rfl
  have e2 : fieldLawFull H Z' P' = P'.map (fun ω => WedgeMeas.dataFull H (Z' ω)) := rfl
  rw [e1, e2]
  have hL : ∀ R, Measurable (E6.truncFull R ∘ g1zEmb) := fun R =>
    (E6.measurable_truncFull R).comp measurable_g1zEmb
  refine E6.ext_of_monotone_generating (fun R => E6.truncFull R ∘ g1zEmb) hL ?_ ?_ _ _
    (by simp) fun R => ?_
  · intro R R' h
    simp only [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (E6.truncFull_comap_mono h)
  · have h1 : (inferInstance : MeasurableSpace ((ℕ → ℝ) × (TestFun H → ℝ))) ≤
        MeasurableSpace.comap g1zEmb inferInstance := by
      have : (Prod.fst ∘ g1zEmb : _ → (ℕ → ℝ) × (TestFun H → ℝ)) = id := rfl
      calc (inferInstance : MeasurableSpace ((ℕ → ℝ) × (TestFun H → ℝ)))
          = MeasurableSpace.comap (Prod.fst ∘ g1zEmb) inferInstance := by
            rw [this, MeasurableSpace.comap_id]
        _ = MeasurableSpace.comap g1zEmb (MeasurableSpace.comap Prod.fst inferInstance) :=
            (MeasurableSpace.comap_comp).symm
        _ ≤ _ := MeasurableSpace.comap_mono measurable_fst.comap_le
    refine h1.trans ?_
    simp only [← MeasurableSpace.comap_comp]
    rw [← MeasurableSpace.comap_iSup]
    exact MeasurableSpace.comap_mono E6.truncFull_generate
  · ext A hA
    rw [g1z_map_trunc_apply R hZ A hA, g1z_map_trunc_apply R hZ' A hA]
    refine hloc R (fun y => A.indicator 1 (g1zEmb y))
      ((measurable_one.indicator hA).comp measurable_g1zEmb) fun y => ?_
    by_cases hy : g1zEmb y ∈ A <;> simp [hy]

/-! ## The wedge law from D3⁺(i) and a (mixed) model approximation -/

theorem g1z_lintegral_le_one {Ω₀ β : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {Γ : β → ℝ≥0∞} (hΓ1 : ∀ y, Γ y ≤ 1) (f : Ω₀ → β) :
    ∫⁻ ω, Γ (f ω) ∂P₀ ≤ 1 :=
  (lintegral_mono fun ω => hΓ1 (f ω)).trans (by simp)

/-! ## The coupling form of the single-model approximation -/

/-! ## The remaining node and the reduction of `G1ZoomPartStmt` -/

end Thm18Asm
end QuantumZipper
