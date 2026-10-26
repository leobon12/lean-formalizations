import LQGMetric.Field.CircleAvgAffine
import LQGMetric.Field.GFFLaw
import LQGMetric.Field.CircleAvgProc

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open LQGMetric

/-- The discrepancy between the circle average and a smooth average has
one law at every centre and scale. The test has integral one. -/
theorem circle_smooth_gap_fixed_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWPGFF h P)
    (f : TestC) (hf : ∫ x, f x = 1)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    P.map (fun ω => circleAvg (h ω) r z - (affineComp r z (h ω)) f) =
      P.map (fun ω => -(h ω f)) := by
  let zoom : Ω → DistC :=
    fun ω => addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)
  let evalNeg : DistC → ℝ := fun g => -(g f)
  have hzoom : Measurable zoom := by
    apply GFFInv.measurable_distC_iff.mpr
    intro φ
    simp only [zoom, GFFInv.addConst_apply]
    exact ((GFFInv.measurable_pair φ).comp
      ((measurable_affineComp r z).comp hh.1.measurable)).add
      ((((measurable_circleAvg_left r z).comp hh.1.measurable).neg).const_mul _)
  have heval : Measurable evalNeg := (GFFInv.measurable_pair f).neg
  have hmap := CircleAvg.map_affine_sub_circleAvg hh hr z
  change P.map zoom = P.map h at hmap
  have hmap' := congrArg (Measure.map evalNeg) hmap
  rw [Measure.map_map heval hzoom, Measure.map_map heval hh.1.measurable] at hmap'
  have hpoint : (fun ω => circleAvg (h ω) r z - (affineComp r z (h ω)) f) =
      evalNeg ∘ zoom := by
    funext ω
    simp only [Function.comp_apply, evalNeg, zoom, GFFInv.addConst_apply, hf]
    ring
  rw [hpoint]
  exact hmap'

/-- A smooth test evaluation of a circle-normalized whole-plane GFF is
centered Gaussian. Its variance is finite but need not be computed here. -/
theorem smooth_eval_centered_gaussian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWPGFF h P)
    (f : TestC) (hf : ∫ x, f x = 1) :
    ∃ V : NNReal, P.map (fun ω => -(h ω f)) = ProbabilityTheory.gaussianReal 0 V := by
  have : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  let φ : ℕ → TestC0 := fun n =>
    ⟨CircleAvg.circBump n 0 1 - f, by
      show ∫ x, (CircleAvg.circBump n 0 1 x - f x) = 0
      rw [integral_sub (CircleAvg.integrable_testC _) (CircleAvg.integrable_testC _),
        CircleAvg.integral_circBump, hf, sub_self]⟩
  let Y : ℕ → Ω → ℝ := fun n ω => h ω (φ n).1
  let Z : Ω → ℝ := fun ω => -(h ω f)
  have hYm : ∀ n, AEMeasurable (Y n) P :=
    fun n => ((GFFInv.measurable_pair (φ n).1).comp hh.1.measurable).aemeasurable
  have hZm : AEMeasurable Z P :=
    (((GFFInv.measurable_pair f).comp hh.1.measurable).neg).aemeasurable
  have hYlaw : ∀ n, P.map (Y n) =
      ProbabilityTheory.gaussianReal 0
        (logCov (φ n).1 (φ n).1).toNNReal := by
    intro n
    have hG := hh.1.gaussian.hasGaussianLaw_eval (φ n)
    have hmean : P[Y n] = 0 := hh.1.centered (φ n)
    rw [hG.map_eq_gaussianReal, hmean]
    congr 1
    rw [← covariance_self hG.aemeasurable, hh.1.covariance_eq]
  have hYlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) Filter.atTop (nhds (Z ω)) := by
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hh.1 0 one_pos, hh.2] with ω ⟨a, ha⟩ hnorm
    have hca : circleAvg (h ω) 1 0 = a := CircleAvg.circleAvg_eq_of_tendsto ha
    have hlim : Tendsto (fun n => CircleAvg.mollAvg (h ω) n 0 1 - h ω f)
        Filter.atTop (nhds (a - h ω f)) := ha.sub tendsto_const_nhds
    have hYeq : (fun n => Y n ω) =
        (fun n => CircleAvg.mollAvg (h ω) n 0 1 - h ω f) := by
      funext n
      simp only [Y, φ, map_sub, CircleAvg.mollAvg_eq]
    rw [hYeq]
    simpa only [Z, ← hca, hnorm, zero_sub] using hlim
  obtain ⟨V, -, hV⟩ := exists_gaussianReal_of_ae_tendsto hYm hZm hYlaw hYlim
  exact ⟨V, hV⟩

/-- The exact normalization claim in the proof of Proposition 4.3. -/
theorem circle_smooth_gap_centered_gaussian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWPGFF h P)
    (f : TestC) (hf : ∫ x, f x = 1) :
    ∃ V : NNReal, ∀ {r : ℝ}, 0 < r → ∀ z : ℂ,
      P.map (fun ω => circleAvg (h ω) r z - (affineComp r z (h ω)) f) =
        ProbabilityTheory.gaussianReal 0 V := by
  obtain ⟨V, hV⟩ := smooth_eval_centered_gaussian P h hh f hf
  refine ⟨V, ?_⟩
  intro r hr z
  rw [circle_smooth_gap_fixed_law P h hh f hf hr z]
  exact hV

/-- A single deterministic upper cutoff controls the normalization gap at
every centre and scale. -/
theorem circle_smooth_gap_uniform_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWPGFF h P)
    (f : TestC) (hf : ∫ x, f x = 1)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ {r : ℝ}, 0 < r → ∀ z : ℂ,
      P {ω | T < circleAvg (h ω) r z - (affineComp r z (h ω)) f} < ε := by
  obtain ⟨V, hV⟩ := circle_smooth_gap_centered_gaussian P h hh f hf
  let μ : Measure ℝ := ProbabilityTheory.gaussianReal 0 V
  obtain ⟨K, hK, htail⟩ :=
    exists_isCompact_closure_measure_compl_lt μ ε hε
  obtain ⟨T, hT⟩ := hK.bddAbove
  refine ⟨T, ?_⟩
  intro r hr z
  let gap : Ω → ℝ :=
    fun ω => circleAvg (h ω) r z - (affineComp r z (h ω)) f
  have hgap : Measurable gap :=
    ((measurable_circleAvg_left r z).comp hh.1.measurable).sub
      ((GFFInv.measurable_pair f).comp
        ((measurable_affineComp r z).comp hh.1.measurable))
  have hsubset : Set.Ioi T ⊆ Kᶜ := by
    intro x hx hxK
    exact not_lt_of_ge (hT (subset_closure hxK)) hx
  calc
    P {ω | T < gap ω} = (P.map gap) (Set.Ioi T) := by
      rw [Measure.map_apply hgap (measurableSet_Ioi)]
      rfl
    _ = μ (Set.Ioi T) := by rw [hV hr z]
    _ ≤ μ Kᶜ := measure_mono hsubset
    _ < ε := htail

end SupercriticalConformalCovariance.Small
