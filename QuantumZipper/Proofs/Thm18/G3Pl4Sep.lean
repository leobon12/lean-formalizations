import QuantumZipper.Proofs.Thm18.G3Pl4Z
import QuantumZipper.Proofs.Thm18.G3PlMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): the boundary-length inputs (I3), (I4) and the node

The inputs (I3), (I4) of `g3pl4_unscaled_of_sep` are events about the boundary measure of the
unscaled wedge on `[−1/2, 1/2]`, where it equals that of the coupled field `V + log`
(`g3pl4_restrict_eq_of_agree`); their probabilities are transferred to `h_C` through the law of the
circle coordinates (`g3pl4_lintegral_bdry_eq`), where they follow from a.s. positivity of `ν_C` on
intervals, no atom at `0` (`ae_g3plV_Ioo_pos`, `ae_g3pField_good`) and `g3pl_exists_U₀` (Sheffield,
arXiv:1012.4797, §5.1 p. 61). This closes `G3PlPhiUnscaledStmt` (`g3PlPhiUnscaledStmt_holds`).
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

theorem g3pl4_bdryM_eq_of_good {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) :
    bdryM γ (E1.fromC (CoordsFull.coordsFull y)) = qBoundaryMeasure γ y := by
  rw [bdryM_congr (CoordsFull.avgReg_congr_full (E1.coordsFull_fromC y))]
  unfold bdryM
  rw [if_pos (G4Core.bCert_of_isLQGGood hy)]

/-- **Law transfer of boundary-measure functionals through the circle coordinates.** -/
theorem g3pl4_lintegral_bdry_eq {γ : ℝ} {Ψ : Measure ℝ → ℝ≥0∞} (hΨ : Measurable Ψ)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {Y : Ω → FieldSample} {Y' : Ω' → FieldSample}
    (hg : ∀ᵐ ω ∂P, IsLQGGood γ (Y ω)) (hg' : ∀ᵐ ω ∂P', IsLQGGood γ (Y' ω))
    (hm : AEMeasurable (fun ω => CoordsFull.coordsFull (Y ω)) P)
    (hm' : AEMeasurable (fun ω => CoordsFull.coordsFull (Y' ω)) P')
    (hlaw : P.map (fun ω => CoordsFull.coordsFull (Y ω)) =
      P'.map (fun ω => CoordsFull.coordsFull (Y' ω))) :
    ∫⁻ ω, Ψ (qBoundaryMeasure γ (Y ω)) ∂P = ∫⁻ ω, Ψ (qBoundaryMeasure γ (Y' ω)) ∂P' := by
  have hF : Measurable fun c : ℕ → ℝ => Ψ (bdryM γ (E1.fromC c)) :=
    hΨ.comp ((measurable_bdryM γ).comp Cor15Group.measurable_fromC)
  have e1 : ∫⁻ ω, Ψ (qBoundaryMeasure γ (Y ω)) ∂P =
      ∫⁻ c, Ψ (bdryM γ (E1.fromC c)) ∂(P.map fun ω => CoordsFull.coordsFull (Y ω)) := by
    rw [lintegral_map' hF.aemeasurable hm]
    exact lintegral_congr_ae (hg.mono fun ω h => by simp only [g3pl4_bdryM_eq_of_good h])
  have e2 : ∫⁻ ω, Ψ (qBoundaryMeasure γ (Y' ω)) ∂P' =
      ∫⁻ c, Ψ (bdryM γ (E1.fromC c)) ∂(P'.map fun ω => CoordsFull.coordsFull (Y' ω)) := by
    rw [lintegral_map' hF.aemeasurable hm']
    exact lintegral_congr_ae (hg'.mono fun ω h => by simp only [g3pl4_bdryM_eq_of_good h])
  rw [e1, e2, hlaw]

/-- **A measurable good event from a `{0,1}`-valued bad indicator.** -/
theorem g3pl4_event_of_bad {γ : ℝ} {Ψ : Measure ℝ → ℝ≥0∞} (hΨ : Measurable Ψ)
    (hΨ01 : ∀ ν, Ψ ν = 0 ∨ Ψ ν = 1) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → FieldSample} (hg : ∀ᵐ ω ∂P, IsLQGGood γ (Y ω))
    (hm : Measurable fun ω => CoordsFull.coordsFull (Y ω)) {Q : Ω → Prop}
    (hQ : ∀ᵐ ω ∂P, Ψ (qBoundaryMeasure γ (Y ω)) = 0 → Q ω) :
    ∃ E : Set Ω, MeasurableSet E ∧ (∀ ω ∈ E, Q ω) ∧
      P Eᶜ ≤ ∫⁻ ω, Ψ (qBoundaryMeasure γ (Y ω)) ∂P := by
  set g : Ω → ℝ≥0∞ := fun ω => Ψ (bdryM γ (E1.fromC (CoordsFull.coordsFull (Y ω)))) with hgdef
  have hgm : Measurable g := (hΨ.comp ((measurable_bdryM γ).comp Cor15Group.measurable_fromC)).comp hm
  obtain ⟨S, hSm, hS, hS0⟩ := g3pl4_exists_measurable_ae (P := P)
    (Q := fun ω => g ω = Ψ (qBoundaryMeasure γ (Y ω)) ∧ (Ψ (qBoundaryMeasure γ (Y ω)) = 0 → Q ω))
    (by
      filter_upwards [hg, hQ] with ω h1 h2
      exact ⟨by simp only [hgdef]; rw [g3pl4_bdryM_eq_of_good h1], h2⟩)
  have hZm : MeasurableSet (g ⁻¹' {0}) := hgm (measurableSet_singleton 0)
  refine ⟨S ∩ g ⁻¹' {0}, hSm.inter hZm, fun ω hω => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hS ω hω.1
    exact h2 (h1 ▸ hω.2)
  · rw [compl_inter]
    refine (measure_union_le _ _).trans ?_
    rw [hS0, zero_add]
    calc P (g ⁻¹' {0})ᶜ = ∫⁻ ω, (g ⁻¹' {0})ᶜ.indicator 1 ω ∂P :=
          (lintegral_indicator_one hZm.compl).symm
      _ ≤ ∫⁻ ω, g ω ∂P := lintegral_mono fun ω => by
          by_cases h : ω ∈ (g ⁻¹' {0})ᶜ
          · rw [indicator_of_mem h]
            rcases hΨ01 (bdryM γ (E1.fromC (CoordsFull.coordsFull (Y ω)))) with h0 | h1
            · exact absurd h0 h
            · exact le_of_eq (by simp only [Pi.one_apply, hgdef]; exact h1.symm)
          · rw [indicator_of_notMem h]; exact bot_le
      _ = ∫⁻ ω, Ψ (qBoundaryMeasure γ (Y ω)) ∂P :=
          lintegral_congr_ae ((ae_iff.2 hS0).mono fun ω h => (hS ω h).1)

end R18
end QuantumZipper
