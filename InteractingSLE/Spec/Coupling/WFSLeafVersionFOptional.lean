/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafVersionFReader
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Optional sampling of an ordinary closed process

Fixed-time conditional expectations suffice for the bounded-stopping-time
identity. Almost sure continuity is repaired on one null event before using
the existing continuous-time optional sampling theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.FlowStopIdentG

/-- Optional sampling for a continuous martingale closed by `Z`, with the
terminal deterministic horizon removed using the tower property. -/
theorem ae_closed_martingale_at_bounded_stop
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {𝓓 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}
    (hX : Martingale X 𝓓 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hclosed : ∀ t, X t =ᵐ[P] P[Z | 𝓓 t])
    {T : Ω → ℝ≥0∞} (hT : IsStoppingTime 𝓓 fun ω => (T ω : WithTop ℝ≥0))
    (hbound : ∃ N : ℝ≥0, ∀ ω, T ω ≤ N) :
    P[Z | hT.measurableSpace] =ᵐ[P] fun ω => X (T ω).toNNReal ω := by
  obtain ⟨N, hN⟩ := hbound
  have hos := InteractingSLE.Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hX
    (fun ω t => (hc ω).continuousAt.continuousWithinAt) hT (isStoppingTime_const 𝓓 N)
    hN (fun _ => le_rfl)
  have hpost := (condExp_congr_ae (m := hT.measurableSpace) (hclosed N)).trans
    (condExp_condExp_of_le (hT.measurableSpace_le_of_le_const hN) (𝓓.le N))
  have he : stoppedValue X (fun ω => (T ω : WithTop ℝ≥0)) =
      fun ω => X (T ω).toNNReal ω := by
    funext ω
    have hfin : T ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hN ω)
    change X (T ω).untopA ω = X (T ω).toNNReal ω
    rw [← ENNReal.coe_toNNReal hfin]
    rfl
  rw [stoppedValue_const, he] at hos
  exact hpost.symm.trans hos.symm

/-- A continuous version on a conull event can be made continuous everywhere
without changing adaptedness or the fixed-time closing identities. -/
theorem exists_continuous_closed_version
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓓 : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ} (hX : StronglyAdapted 𝓓 X)
    (hn : ∀ t, nullSigma P ≤ 𝓓 t)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hclosed : ∀ t, X t =ᵐ[P] P[Z | 𝓓 t]) :
    ∃ X' : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 X' ∧
      (∀ ω, Continuous (fun t => X' t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t, X' t ω = X t ω) ∧
      ∀ t, X' t =ᵐ[P] P[Z | 𝓓 t] := by
  obtain ⟨G, hGm, hG0, hGc⟩ := MathFin.ItoLocalMartingale.exists_nullsAlg_of_ae hc
  let X' : ℝ≥0 → Ω → ℝ := fun t => G.indicator (X t)
  have he : ∀ᵐ ω ∂P, ∀ t, X' t ω = X t ω := by
    filter_upwards [(ae_iff.2 hG0 : ∀ᵐ ω ∂P, ω ∈ G)] with ω hω
    exact fun _ => indicator_of_mem hω _
  refine ⟨X', fun t => (hX t).indicator (hn t _ hGm), fun ω => ?_, he, fun t => ?_⟩
  · by_cases hω : ω ∈ G
    · simpa only [X', indicator_of_mem hω] using hGc ω hω
    · simpa only [X', indicator_of_notMem hω] using (continuous_const : Continuous fun _ : ℝ≥0 => (0 : ℝ))
  · have het : X' t =ᵐ[P] X t := he.mono fun ω hω => hω t
    exact het.trans (hclosed t)

end InteractingSLE.WFS
