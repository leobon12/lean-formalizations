import HigherDimLQGMetric.Locality.JointSkorokhod
import LQGMetric.Papers.DFGPS.L2_17Core3D

/-! The first marginal of a joint Skorokhod limit retains a known
samplewise limit law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

theorem l7a_joint_limit_fst_law
    {A B Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]
    [BorelSpace A] [PolishSpace A]
    [TopologicalSpace B] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (X : ℕ → Ω → A) (Y : ℕ → Ω → B) (Xlim : Ω → A)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hXlim : Measurable Xlim)
    (hXconv : ∀ ω, Tendsto (fun n => X n ω) atTop (𝓝 (Xlim ω)))
    (ns : ℕ → ℕ) (hns : StrictMono ns)
    (Z : ℕ → E → A × B) (Zlim : E → A × B)
    (hZ : ∀ n, Measurable (Z n)) (hZlim : Measurable Zlim)
    (hZlaw : ∀ n, Q.map (Z n) =
      P.map (fun ω => (X (ns n) ω, Y (ns n) ω)))
    (hZconv : ∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e))) :
    Q.map (fun e => (Zlim e).1) = P.map Xlim := by
  let νn : ℕ → ProbabilityMeasure A := fun n =>
    ⟨Q.map (fun e => (Z n e).1), inferInstance⟩
  let νQ : ProbabilityMeasure A :=
    ⟨Q.map (fun e => (Zlim e).1), inferInstance⟩
  let νP : ProbabilityMeasure A := ⟨P.map Xlim, inferInstance⟩
  letI : TopologicalSpace (ProbabilityMeasure A) := inferInstance
  have hq : Tendsto νn atTop (𝓝 νQ) :=
    LQGMetric.DFGPS.L217.tendsto_map_of_forall_tendsto
      (fun n => measurable_fst.comp (hZ n))
      (measurable_fst.comp hZlim)
      (fun e => (continuous_fst.tendsto (Zlim e)).comp (hZconv e))
  have hp : Tendsto (β := ProbabilityMeasure A)
      (fun n => (⟨P.map (X (ns n)), inferInstance⟩ : ProbabilityMeasure A))
      atTop (𝓝 νP) :=
    LQGMetric.DFGPS.L217.tendsto_map_of_forall_tendsto
      (fun n => hX (ns n)) hXlim
      (fun ω => (hXconv ω).comp hns.tendsto_atTop)
  have heq (n : ℕ) : (νn n : Measure A) = P.map (X (ns n)) := by
    calc
      Q.map (fun e => (Z n e).1) = (Q.map (Z n)).map Prod.fst :=
        (Measure.map_map measurable_fst (hZ n)).symm
      _ = (P.map (fun ω => (X (ns n) ω, Y (ns n) ω))).map Prod.fst := by
        rw [hZlaw n]
      _ = P.map (X (ns n)) := by
        simpa only [Function.comp_def] using
          (Measure.map_map measurable_fst ((hX (ns n)).prodMk (hY (ns n))))
  have heq' (n : ℕ) : νn n =
      (⟨P.map (X (ns n)), inferInstance⟩ : ProbabilityMeasure A) :=
    Subtype.ext (heq n)
  have hp' : Tendsto νn atTop (𝓝 νP) := by
    have hfun : νn = fun n =>
        (⟨P.map (X (ns n)), inferInstance⟩ : ProbabilityMeasure A) :=
      funext heq'
    rw [hfun]
    exact hp
  have hν : νQ = νP := tendsto_nhds_unique hq hp'
  exact congrArg Subtype.val hν

end HigherDimLQGMetric
