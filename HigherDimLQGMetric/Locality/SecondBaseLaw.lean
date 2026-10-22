import HigherDimLQGMetric.Locality.SecondCoupling
import HigherDimLQGMetric.Locality.JointMarginal

/-! The marked field and full metric marginal of the second coupling is
the prescribed stable limit law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

theorem l7a_second_base_limit_law
    {S C T Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    [BorelSpace S] [PolishSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [OpensMeasurableSpace C]
    [BorelSpace C] [PolishSpace C]
    [TopologicalSpace T] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (X : Ω → S) (Y : ℕ → Ω → C) (Ylim : Ω → C)
    (A : ℕ → Ω → T)
    (hX : Measurable X) (hY : ∀ n, AEMeasurable (Y n) P)
    (hA : ∀ n, AEMeasurable (A n) P)
    (hstable : Tendsto (β := ProbabilityMeasure (S × C))
      (fun n => (⟨P.map (fun ω => (X ω, Y n ω)), inferInstance⟩ :
        ProbabilityMeasure (S × C))) atTop
      (𝓝 (⟨P.map (fun ω => (X ω, Ylim ω)), inferInstance⟩ :
        ProbabilityMeasure (S × C))))
    (ns : ℕ → ℕ) (hns : StrictMono ns)
    (Z : ℕ → E → (S × C) × T)
    (Zlim : E → (S × C) × T)
    (hZm : ∀ n, Measurable (Z n)) (hZlimm : Measurable Zlim)
    (hZlaw : ∀ n, Q.map (Z n) =
      P.map (fun ω => ((X ω, Y (ns n) ω), A (ns n) ω)))
    (hZconv : ∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e))) :
    Q.map (fun e => (Zlim e).1) = P.map (fun ω => (X ω, Ylim ω)) := by
  let νQ : ProbabilityMeasure (S × C) :=
    ⟨Q.map (fun e => (Zlim e).1), inferInstance⟩
  let νn : ℕ → ProbabilityMeasure (S × C) := fun n =>
    ⟨Q.map (fun e => (Z n e).1), inferInstance⟩
  let νP : ProbabilityMeasure (S × C) :=
    ⟨P.map (fun ω => (X ω, Ylim ω)), inferInstance⟩
  letI : TopologicalSpace (ProbabilityMeasure (S × C)) := inferInstance
  have hq : Tendsto νn atTop (𝓝 νQ) :=
    LQGMetric.DFGPS.L217.tendsto_map_of_forall_tendsto
      (fun n => measurable_fst.comp (hZm n))
      (measurable_fst.comp hZlimm)
      (fun e => (continuous_fst.tendsto (Zlim e)).comp (hZconv e))
  have hp : Tendsto (β := ProbabilityMeasure (S × C))
      (fun n => (⟨P.map (fun ω => (X ω, Y (ns n) ω)), inferInstance⟩ :
        ProbabilityMeasure (S × C))) atTop (𝓝 νP) :=
    hstable.comp hns.tendsto_atTop
  have heq (n : ℕ) : (νn n : Measure (S × C)) =
      P.map (fun ω => (X ω, Y (ns n) ω)) := by
    calc
      Q.map (fun e => (Z n e).1) = (Q.map (Z n)).map Prod.fst :=
        (Measure.map_map measurable_fst (hZm n)).symm
      _ = (P.map (fun ω =>
        ((X ω, Y (ns n) ω), A (ns n) ω))).map Prod.fst := by
          rw [hZlaw n]
      _ = P.map (fun ω => (X ω, Y (ns n) ω)) := by
        simpa only [Function.comp_def] using
          (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
            ((hX.aemeasurable.prodMk (hY (ns n))).prodMk
              (hA (ns n))))
  have heq' (n : ℕ) : νn n =
      (⟨P.map (fun ω => (X ω, Y (ns n) ω)), inferInstance⟩ :
        ProbabilityMeasure (S × C)) := Subtype.ext (heq n)
  have hp' : Tendsto νn atTop (𝓝 νP) := by
    have hfun : νn = fun n =>
        (⟨P.map (fun ω => (X ω, Y (ns n) ω)), inferInstance⟩ :
          ProbabilityMeasure (S × C)) := funext heq'
    rw [hfun]
    exact hp
  have hν : νQ = νP :=
    tendsto_nhds_unique (X := ProbabilityMeasure (S × C)) hq hp'
  exact congrArg Subtype.val hν

end HigherDimLQGMetric
