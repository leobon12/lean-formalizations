/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6SourceCFlow

/-!
# GB6 versions reduced only to causal read-back of the constructed driver

The zero-prefix case is vacuous on the interior-tip event. For positive
prefixes all measurable relative coordinates have been constructed from the
original hypotheses. The named remaining input asks only for the physical
separation gauge read from those specific coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Supp8.GB6.SourceC

open RelDrv RelDrv.Version

/-- At a zero flow prefix the interior-tip event is null, so constant-zero
drivers with the already proved gauge construction give the required versions. -/
theorem exists_versions_at_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hα0 : ∀ᵐ ω ∂P, α ω 0 = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGB6RelVersion 0 P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, ((0 : ℝ≥0) : ℝ≥0∞) < ζα ω → α ω 0 ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc 0 γ α ω →
          ∃ m, ENNReal.ofReal (gb6Clock 0 W Wα ω t) < V m ω := by
  apply exists_versions_of_coordinates
    (D := fun _ _ => 0) (L := fun _ => ⊤) (g := fun _ _ => 1) (G := fun _ _ => 1)
  refine ⟨?_, fun _ => continuous_const.continuousOn, fun _ => rfl,
    fun _ => measurable_const, fun _ => continuous_const, fun _ => zero_lt_one,
    fun _ _ _ => zero_lt_one, ?_, fun _ => measurable_const, ?_, fun _ => rfl, fun _ _ _ => rfl, ?_⟩
  · intro t B hB
    have hLive : MeasurableSet {ω : Ω | (t : ℝ≥0∞) < ⊤} :=
      measurableSet_lt measurable_const measurable_const
    have hm : Measurable fun _ : Ω => (0 : ℝ) := measurable_const
    exact hLive.inter (hm hB)
  · intro ω t ht
    exact (ENNReal.coe_lt_top.ne ht).elim
  · intro t r w w' _
    rfl
  · filter_upwards [hα0] with ω hω _ hH
    rw [hω] at hH
    exact (show False from (lt_irrefl (0 : ℝ)) hH).elim

/-- **Remaining input, unproved here.** Under the original unchanged GB6
hypotheses, the particular measurable relative driver constructed in
`GB6SourceCFlow` admits a causal physical separation readout. This premise
contains no relative-driver choice, clock identification, prefix cover,
stopping rule, stopped version or exhaustion assertion. -/
def GB6SourceReadoutStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    ∀ (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
      (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
        Tendsto (fun t => ‖γ ω t‖) atTop atTop)
      (hflow : IsFlowLineDriver κ b J θ P h Wα ζα)
      (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
      (s : ℝ≥0) (hs : 0 < s),
      HasSourceReadout hcf hflow (hγ.mono fun _ hω => ⟨hω.1, hω.2.1⟩) hα s hs

/-- Conditional only on the remaining physical read-back input. The
original full version statement, including zero prefixes, is unchanged. -/
theorem gb6RelVersionStatement_of_sourceReadout (hread : GB6SourceReadoutStatement.{u}) :
    GB6RelVersionStatement.{u} := by
  intro κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
    hb hG hb' hchart hcf hγ hflow hα s
  by_cases hs : s = 0
  · subst s
    exact exists_versions_at_zero (hα.mono fun _ hω => hω.1)
  · have hsp : 0 < s := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ s) (Ne.symm hs)
    exact exists_versions_of_sourceReadout hcf hflow (hγ.mono fun _ hω => ⟨hω.1, hω.2.1⟩) hα s hsp
      (hread κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
        hb hG hb' hchart hcf hγ hflow hα s hsp)

end InteractingSLE.Supp8.GB6.SourceC
