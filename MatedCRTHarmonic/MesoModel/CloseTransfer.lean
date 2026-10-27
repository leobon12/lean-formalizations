import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTPath2

/-!
# Almost-sure transfer through a standard-Borel coupling, without event measurability

For a measurable map `f : Ω → β` on a standard Borel space and an *arbitrary* path property `Q`,
`∀ᵐ ω ∂P, Q (f ω)` implies `∀ᵐ x ∂(P.map f), Q x` as soon as the graph `{(x, ω) | x = f ω}` is
measurable. The proof disintegrates the joint law of `(f ω, ω)` along its first marginal
(Mathlib's `Measure.condKernel`, which needs `Ω` standard Borel): a measurable null superset of the
exceptional set gives a measurable full-measure subset of the graph, so almost every fibre measure
charges it, and any point of it witnesses `Q x`. No measurability of `{x | Q x}` is used. This
replaces the Borel-event fields of the unit-mesh interfaces for the events of the cell-model construction
(recurrence, existence of a mesoscopic cellular embedding), whose measurability is not available.

The graph of a measurable map into `MatedCRT.Path2` is measurable: two continuous paths agreeing at
every rational time are equal.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MatedCRTHarmonic.MesoModel

/-- **A.e. transfer to the push-forward without measurability of the event.** On a standard Borel
space, if the graph of the measurable map `f` is measurable, every property holding at `f ω` for
`P`-a.e. `ω` holds `P.map f`-a.e. The proof uses the disintegration of the joint law of `(f ω, ω)`. -/
theorem closeAe_map_of_ae_comp
    {Ω β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → β} (hf : Measurable f)
    (hgraph : MeasurableSet {p : β × Ω | p.1 = f p.2})
    {Q : β → Prop} (hQ : ∀ᵐ ω ∂P, Q (f ω)) : ∀ᵐ x ∂(P.map f), Q x := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · rw [Measure.eq_zero_of_isEmpty P, Measure.map_zero]
    exact ae_zero.le (by simp)
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null hQ
  let g : Ω → β × Ω := fun ω => (f ω, ω)
  have hg : Measurable g := hf.prodMk measurable_id
  let ρ : Measure (β × Ω) := P.map g
  have : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map P g
  let S : Set (β × Ω) := {p | p.1 = f p.2} ∩ Prod.snd ⁻¹' Nᶜ
  have hS : MeasurableSet S := hgraph.inter (measurable_snd hNmeas.compl)
  have hρS : ∀ᵐ p ∂ρ, p ∈ S := by
    refine (ae_map_iff hg.aemeasurable hS).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    exact ⟨rfl, hω⟩
  have hfst : ρ.fst = P.map f := by
    rw [Measure.fst, Measure.map_map measurable_fst hg]
    rfl
  rw [← ρ.disintegrate ρ.condKernel] at hρS
  have hfib := Measure.ae_ae_of_ae_compProd hρS
  rw [hfst] at hfib
  filter_upwards [hfib] with x hx
  have : (ae (ρ.condKernel x)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨ω, hxω, hωN⟩ := hx.exists
  change x = f ω at hxω
  rw [hxω]
  by_contra hnot
  exact hωN (hNsub hnot)

/-- The graph of a measurable map into the path space is measurable: equality of two continuous
paths is equality at every rational time. -/
theorem closeMeasurableSet_graph_path2 {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → MatedCRT.Path2} (hf : Measurable f) :
    MeasurableSet {p : MatedCRT.Path2 × Ω | p.1 = f p.2} := by
  have hset : {p : MatedCRT.Path2 × Ω | p.1 = f p.2} =
      ⋂ q : ℚ, {p : MatedCRT.Path2 × Ω | p.1 (q : ℝ) = f p.2 (q : ℝ)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h q
      rw [h]
    · intro h
      apply ContinuousMap.ext
      intro t
      have heq : (p.1 : ℝ → ℝ × ℝ) = f p.2 :=
        Continuous.ext_on Rat.denseRange_cast p.1.continuous (f p.2).continuous
          (by rintro _ ⟨q, rfl⟩; exact h q)
      exact congrFun heq t
  rw [hset]
  refine MeasurableSet.iInter fun q => ?_
  have h1 : Measurable fun p : MatedCRT.Path2 × Ω => p.1 (q : ℝ) :=
    (ContinuousMap.measurable_eval (q : ℝ)).comp measurable_fst
  have h2 : Measurable fun p : MatedCRT.Path2 × Ω => f p.2 (q : ℝ) :=
    (ContinuousMap.measurable_eval (q : ℝ)).comp (hf.comp measurable_snd)
  exact measurableSet_eq_fun h1 h2

/-- The standard-Borel a.e. transfer for maps into the mated-CRT path space. -/
theorem closeAe_map_path2_of_ae_comp
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → MatedCRT.Path2} (hf : Measurable f)
    {Q : MatedCRT.Path2 → Prop} (hQ : ∀ᵐ ω ∂P, Q (f ω)) : ∀ᵐ x ∂(P.map f), Q x :=
  closeAe_map_of_ae_comp hf (closeMeasurableSet_graph_path2 hf) hQ

end MatedCRTHarmonic.MesoModel
