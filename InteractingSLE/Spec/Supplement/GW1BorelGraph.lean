/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1BorelWitness

/-!
# Borel recognition of the exact retargeting graph

Continuation of PROVE-GW1-DET. The clock is unique by half-plane capacity.
Thus forgetting the clock is an injective measurable projection of the Borel
witness relation. Lusin--Souslin gives the Borel graph used in `GW1DetCode`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Theorem14.GW1Borel

/-- Continuous nonnegative clocks starting at zero are recovered from their rational codes. -/
theorem clock_restrict {ℓ : ℝ≥0 → ℝ≥0} (hc : Continuous ℓ) (h0 : ℓ 0 = 0) :
    clock (fun q : ℚ≥0 => (ℓ q : ℝ)) = ℓ := by
  have h := GW1Det.regQ_restrict (continuous_subtype_val.comp hc)
    (show (ℓ 0 : ℝ) = 0 by rw [h0]; rfl)
  funext t
  change (Sec7.Coding.regQ t (fun q : ℚ≥0 => (ℓ q : ℝ))).toNNReal = ℓ t
  have ht : Sec7.Coding.regQ t (fun q : ℚ≥0 => (ℓ q : ℝ)) = (ℓ t : ℝ) := congrFun h t
  rw [ht, Real.toNNReal_coe]

/-- Visiting the physical target is the finite first-visit condition used in the witness graph. -/
theorem visited_iff (p : Base) (hv : p.1.2 ≠ 0) :
    (p.1.2 : ℂ) ∈ infinitySourceChart.tipSet (driver p.1.1.1) ⊤ ↔ targetTime p < ⊤ := by
  rw [targetTime_eq p hv]
  constructor
  · rintro ⟨t, _, ht⟩
    exact lt_of_le_of_lt (iInf₂_le t ⟨(p.1.2 : ℂ), rfl, ht⟩) ENNReal.coe_lt_top
  · intro hT
    rw [GW1Det.firstTipTime_singleton_eq_firstVisit (trace_properties p.1.1).1
      (continuous_driver _) (driver_zero _)] at hT
    obtain ⟨t, _, hne, he⟩ := GW4Reg.exists_eq_firstVisit (continuous_trace p.1.1) hT
    exact ⟨t, le_top, (GW4Leaf.tipAt_infinitySourceChart_iff (trace_properties p.1.1).1
      (continuous_driver _) (driver_zero _) _ _).2 ⟨hne, he.symm⟩⟩

/-- Forget the regular-code proofs and the clock, retaining the exact original graph coordinates. -/
def projection (p : Witness) : ((Code × ℝ) × Code) := ((p.1.1.1.1, p.1.1.2), p.1.2.1)

theorem measurable_projection : Measurable projection :=
  ((measurable_subtype_coe.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
    (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))

theorem projection_injective : Function.Injective (fun x : witnessGraph => projection x.1) := by
  intro x y hxy
  have hbase : x.1.1 = y.1.1 := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun p : ((Code × ℝ) × Code) => p.1.1) hxy
      · exact congrArg (fun p : ((Code × ℝ) × Code) => p.1.2) hxy
    · apply Subtype.ext
      exact congrArg (fun p : ((Code × ℝ) × Code) => p.2) hxy
  have hy := witness_prefix y.2
  rw [← hbase] at hy
  have hc := GW1Det.prefixClock_unique (trace_properties x.1.1.1.1).1
    (continuous_driver _) (witness_prefix x.2) hy
  apply Subtype.ext
  apply Prod.ext hbase
  funext q
  exact (x.2.2.2.2.1 q).trans ((congrArg (fun ℓ : ℝ≥0 → ℝ≥0 => (ℓ q : ℝ)) hc).trans
    (y.2.2.2.2.1 q).symm)

theorem range_projection : range (fun x : witnessGraph => projection x.1) = GW1Det.retargetGraph := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    have hp := witness_prefix x.2
    refine ⟨x.2.1, x.1.1.1.1.2, x.2.2.1,
      (visited_iff x.1.1 x.2.2.1).2 x.2.2.2.1, ?_⟩
    exact ⟨⟨trace x.1.1.2, trace_properties x.1.1.2⟩, clock x.1.2, hp⟩
  · intro hp
    have hQ : GW1Path.IsRegCf (driver p.1.1) := hp.2.1
    have hU : GW1Path.IsRegCf (driver p.2) :=
      ⟨continuous_driver _, driver_zero _, hp.2.2.2.2.1⟩
    let b : Base := ((⟨p.1.1, hQ⟩, p.1.2), ⟨p.2, hU⟩)
    obtain ⟨ℓ, hc, hm, hr, ht⟩ := hp.2.2.2.2.2
    have h0 := GW1Det.clock_zero_of_range hm hr
    let f : Code := fun q : ℚ≥0 => (ℓ q : ℝ)
    have hf : clock f = ℓ := clock_restrict hc h0
    have hprefix : GW1LaunchClock.IsPrefixClock (Chart.id.recenter b.1.2)
        (driver b.1.1.1) (driver b.2.1) {(b.1.2 : ℂ)} (clock f) := by
      rw [hf]
      exact ⟨hc, hm, hr, ht⟩
    have hx : (b, f) ∈ witnessGraph := by
      refine ⟨hp.1, hp.2.2.1, (visited_iff b hp.2.2.1).1 hp.2.2.2.1, ?_,
        (prefixClock_iff b hp.2.2.1 f).1 hprefix⟩
      intro q
      exact (congrArg (fun ℓ : ℝ≥0 → ℝ≥0 => (ℓ q : ℝ)) hf).symm
    exact ⟨⟨(b, f), hx⟩, rfl⟩

/-- The exact graph from the original deterministic reduction is Borel. -/
theorem measurableSet_retargetGraph : MeasurableSet GW1Det.retargetGraph := by
  let : StandardBorelSpace witnessGraph := measurableSet_witnessGraph.standardBorel
  have hm : Measurable (fun x : witnessGraph => projection x.1) :=
    measurable_projection.comp measurable_subtype_coe
  rw [← range_projection]
  exact (hm.measurableEmbedding projection_injective).measurableSet_range

end InteractingSLE.Theorem14.GW1Borel
