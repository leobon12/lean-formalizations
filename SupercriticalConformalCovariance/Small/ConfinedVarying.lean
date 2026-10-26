import SupercriticalConformalCovariance.Small.ConfinedLaw
import SupercriticalConformalCovariance.Small.CommonFixed

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology

namespace SupercriticalConformalCovariance.Small
open LQGMetric (DistC CoordJ pairJ)
open SupercriticalLQGUniqueness (LSCMetric LSCFun)
open SupercriticalConformalCovariance.Tangent (SubseqLSC)

/-- Transfer a joint confined-metric limit from the common-field probability
space to a triangular array whose field marginal is fixed at every index. -/
theorem confined_joint_law_varying
    {Y Ω : Type} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → DistC) (mark : ℕ → Ω → Y)
    (hHm : ∀ n, Measurable (H n)) (hmarkm : ∀ n, Measurable (mark n))
    (μ : Measure DistC) [IsProbabilityMeasure μ] (y₀ : Y)
    (hlaw : ∀ n, P.map (H n) = μ)
    (D E : ℕ → DistC × Y → LSCMetric) (d : DistC → LSCMetric)
    (hDm : ∀ n, Measurable (D n)) (hEm : ∀ n, Measurable (E n))
    (hdm : Measurable d)
    (hD : SubseqLSC (commonFixedMeasure P H mark μ y₀)
      (fun n path q => (D n ((path 0).1, (path (n+1)).2) q : EReal))
      (fun path q => (d (path 0).1 q : EReal)))
    (hE : SubseqLSC (commonFixedMeasure P H mark μ y₀)
      (fun n path q => (E n ((path 0).1, (path (n+1)).2) q : EReal))
      (fun path q => (d (path 0).1 q : EReal)))
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (F : BoundedContinuousFunction ((CoordJ → ℝ) × LSCFun × LSCFun) ℝ) :
    Tendsto (fun n => ∫ ω,
      F (pairJ ⊤ (H n ω), (D n (H n ω, mark n ω)).toLSCFun,
        (E n (H n ω, mark n ω)).toLSCFun) ∂P) atTop
      (𝓝 (∫ ω, F (pairJ ⊤ (H 0 ω), (d (H 0 ω)).toLSCFun,
        (d (H 0 ω)).toLSCFun) ∂P)) := by
  classical
  let Pstar := commonFixedMeasure P H mark μ y₀
  haveI : IsProbabilityMeasure Pstar := by
    dsimp [Pstar, commonFixedMeasure]
    infer_instance
  let hstar : (ℕ → DistC × Y) → DistC := fun path => (path 0).1
  let pairStar : ℕ → (ℕ → DistC × Y) → DistC × Y :=
    fun n path => (hstar path, (path (n+1)).2)
  have hstarM : Measurable hstar := by fun_prop
  have pairStarM : ∀ n, Measurable (pairStar n) := fun n => by
    dsimp [pairStar, hstar]
    fun_prop
  have hDmStar : ∀ n, Measurable fun path => D n (pairStar n path) :=
    fun n => (hDm n).comp (pairStarM n)
  have hEmStar : ∀ n, Measurable fun path => E n (pairStar n path) :=
    fun n => (hEm n).comp (pairStarM n)
  have hlim := confined_joint_law_of_subseq Pstar hstar hstarM
    (fun n path => D n (pairStar n path))
    (fun n path => E n (pairStar n path))
    (fun path => d (hstar path)) hDmStar hEmStar (hdm.comp hstarM) hD hE F
  let Tn (n : ℕ) (p : DistC × Y) : ℝ :=
    F (pairJ ⊤ p.1, (D n p).toLSCFun, (E n p).toLSCFun)
  have hTn : ∀ n, Measurable (Tn n) := by
    intro n
    have hto : Measurable (LSCMetric.toLSCFun) :=
      SupercriticalLQGUniqueness.B2.LscTop.measurable_toLSCFun
    exact F.continuous.measurable.comp
      (((LQGMetric.measurable_pairJ ⊤).comp measurable_fst).prodMk
        (((hto.comp (hDm n)).prodMk (hto.comp (hEm n)))))
  have hidx : ∀ n, (∫ ω, Tn n (H n ω, mark n ω) ∂P) =
      ∫ path, Tn n (pairStar n path) ∂Pstar := by
    intro n
    have hmap := commonFixedMeasure_observable P H mark μ y₀ n
      (hHm n) (hmarkm n) (hlaw n) (Tn n) (hTn n)
    calc
      (∫ ω, Tn n (H n ω, mark n ω) ∂P) =
          ∫ x, x ∂(P.map (fun ω => Tn n (H n ω, mark n ω))) :=
        (integral_map ((hTn n).comp ((hHm n).prodMk (hmarkm n))).aemeasurable
          measurable_id.aestronglyMeasurable).symm
      _ = ∫ x, x ∂(Pstar.map (fun path => Tn n (pairStar n path))) := by
        rw [hmap]
      _ = ∫ path, Tn n (pairStar n path) ∂Pstar :=
        integral_map ((hTn n).comp (pairStarM n)).aemeasurable
          measurable_id.aestronglyMeasurable
  let T (x : DistC) : ℝ :=
    F (pairJ ⊤ x, (d x).toLSCFun, (d x).toLSCFun)
  have hT : Measurable T := by
    have hto : Measurable (LSCMetric.toLSCFun) :=
      SupercriticalLQGUniqueness.B2.LscTop.measurable_toLSCFun
    exact F.continuous.measurable.comp
      ((LQGMetric.measurable_pairJ ⊤).prodMk
        (((hto.comp hdm).prodMk (hto.comp hdm))))
  have hlimit : (∫ path, T (hstar path) ∂Pstar) = ∫ ω, T (H 0 ω) ∂P := by
    have hmap := commonFixedMeasure_field P H mark μ y₀
    calc
      (∫ path, T (hstar path) ∂Pstar) =
          ∫ x, T x ∂Pstar.map hstar :=
        (integral_map hstarM.aemeasurable hT.aestronglyMeasurable).symm
      _ = ∫ x, T x ∂P.map (H 0) := by rw [hmap, ← hlaw 0]
      _ = ∫ ω, T (H 0 ω) ∂P :=
        integral_map (hHm 0).aemeasurable hT.aestronglyMeasurable
  change Tendsto (fun n => ∫ ω, Tn n (H n ω, mark n ω) ∂P) atTop
    (𝓝 (∫ ω, T (H 0 ω) ∂P))
  have hidx' : (fun n => ∫ ω, Tn n (H n ω, mark n ω) ∂P) =
      (fun n => ∫ path, Tn n (pairStar n path) ∂Pstar) := by
    funext n
    exact hidx n
  rw [hidx', ← hlimit]
  exact hlim

end SupercriticalConformalCovariance.Small
