import HigherDimLQGMetric.Determ.Limit
import HigherDimLQGMetric.Determ.CondLaw
import HigherDimLQGMetric.Determ.CopyMeas

/-! Passing the comparison with a conditionally independent copy to a fiber law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem determ_fiber_copy_bound {d : ℕ} [Nonempty (ContMetric d)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (D D' : Ω → ContMetric d) (C : ℝ)
    (hh : Measurable h) (hD : Measurable D) (hD' : Measurable D')
    (hci : LQGMetric.CondIndepEv (fullSigmaRd h)
      (MeasurableSpace.comap D inferInstance)
      (MeasurableSpace.comap D' inferInstance) P)
    (hlaw : P.map (fun ω => (h ω, D ω)) = P.map (fun ω => (h ω, D' ω)))
    (hbound : ∀ᵐ ω ∂P, ∀ x y : Rd d,
      (D' ω).1 (x, y) ≤ C * (D ω).1 (x, y)) :
    ∀ᵐ g ∂P.map h, ∀ᵐ p ∂(condDistrib D h P g).prod (condDistrib D h P g),
      ∀ x y : Rd d, p.2.1 (x, y) ≤ C * p.1.1 (x, y) := by
  -- The conclusion is first established on a countable dense set, then extended by continuity.
  let p : ℕ → Rd d × Rd d := TopologicalSpace.denseSeq (Rd d × Rd d)
  let B : Set (ContMetric d × ContMetric d) :=
    {q | ∀ k, q.2.1 (p k) ≤ C * q.1.1 (p k)}
  have hm : ∀ k, Measurable fun E : ContMetric d => E.1 (p k) := fun k =>
    (continuous_eval_const (p k)).measurable.comp measurable_subtype_coe
  have hB : MeasurableSet B := by
    dsimp [B]
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_le
      ((hm k).comp measurable_snd)
      (((hm k).comp measurable_fst).const_mul C)
  let π : Ω → DistRd d × (ContMetric d × ContMetric d) :=
    fun ω => (h ω, D ω, D' ω)
  have hπ : Measurable π := hh.prodMk (hD.prodMk hD')
  have hBπ : ∀ᵐ t ∂P.map π, t.2 ∈ B :=
    (ae_map_iff hπ.aemeasurable (hB.preimage measurable_snd)).2
      (hbound.mono fun ω hω k => hω (p k).1 (p k).2)
  have htrip := determ_ci_triple_law P h D D' hh hD hD' hci
  have hcond : condDistrib D' h P = condDistrib D h P := by
    simp only [condDistrib, ← hlaw]
  rw [htrip, hcond] at hBπ
  have hprod := (Measure.ae_compProd_iff (hB.preimage measurable_snd)).1 hBπ
  filter_upwards [hprod] with g hg
  simpa only [Kernel.prod_apply] using hg.mono (fun q hq =>
    determ_le_of_dense (D := q.1) (D' := q.2) (c := C) hq)

end HigherDimLQGMetric
