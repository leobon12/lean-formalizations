import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.Boundary




 


set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.MovingEndpoints

abbrev WitnessCarrier := (LSCMetric × LSCMetric) × (ℂ × ℂ)

 


def GWitness (r κ C : ℝ) (p : WitnessCarrier) : Prop :=
  p.2.1 ∈ Metric.closedBall (0 : ℂ) r ∧
  p.2.2 ∈ Metric.closedBall (0 : ℂ) r ∧
  p.2.1 ≠ p.2.2 ∧
  0 < p.1.1 (p.2.1, p.2.2) ∧
  p.1.1 (p.2.1, p.2.2) < ∞ ∧
  ENNReal.ofReal C * p.1.1 (p.2.1, p.2.2) ≤
    movingOpenSetDist p.1.2 (κ * r) p.2.1 p.2.2

 

def GtildeWitness (r κ C : ℝ) (p : WitnessCarrier) : Prop :=
  p.2.1 ∈ Metric.closedBall (0 : ℂ) r ∧
  p.2.2 ∈ Metric.closedBall (0 : ℂ) r ∧
  p.2.1 ≠ p.2.2 ∧
  0 < p.1.2 (p.2.1, p.2.2) ∧
  p.1.2 (p.2.1, p.2.2) < ∞ ∧
  p.1.2 (p.2.1, p.2.2) ≤
    ENNReal.ofReal C * movingOpenSetDist p.1.1 (κ * r) p.2.1 p.2.2

private theorem witness_firstDist_borel :
    @Measurable WitnessCarrier ENNReal (borel _) inferInstance
      (fun p => p.1.1 (p.2.1, p.2.2)) := by
  have hc : Continuous (fun p : WitnessCarrier => (p.1.1, p.2)) := by fun_prop
  have h := jointEval_borel.comp hc.borel_measurable
  simpa only [Function.comp_def] using h

private theorem witness_secondDist_borel :
    @Measurable WitnessCarrier ENNReal (borel _) inferInstance
      (fun p => p.1.2 (p.2.1, p.2.2)) := by
  have hc : Continuous (fun p : WitnessCarrier => (p.1.2, p.2)) := by fun_prop
  have h := jointEval_borel.comp hc.borel_measurable
  simpa only [Function.comp_def] using h

private theorem witness_firstSetDist_borel (s : ℝ) :
    @Measurable WitnessCarrier ENNReal (borel _) inferInstance
      (fun p => movingOpenSetDist p.1.1 s p.2.1 p.2.2) := by
  have hc : Continuous (fun p : WitnessCarrier => (p.1.1, p.2)) := by fun_prop
  have h := (movingOpenSetDist_joint_borel s).comp hc.borel_measurable
  simpa only [Function.comp_def] using h

private theorem witness_secondSetDist_borel (s : ℝ) :
    @Measurable WitnessCarrier ENNReal (borel _) inferInstance
      (fun p => movingOpenSetDist p.1.2 s p.2.1 p.2.2) := by
  have hc : Continuous (fun p : WitnessCarrier => (p.1.2, p.2)) := by fun_prop
  have h := (movingOpenSetDist_joint_borel s).comp hc.borel_measurable
  simpa only [Function.comp_def] using h

 
theorem GWitness_borel (r κ C : ℝ) :
    @MeasurableSet WitnessCarrier (borel _) {p | GWitness r κ C p} := by
  letI : MeasurableSpace WitnessCarrier := borel _
  letI : OpensMeasurableSpace WitnessCarrier := ⟨le_rfl⟩
  have hz : MeasurableSet {p : WitnessCarrier | p.2.1 ∈ Metric.closedBall (0 : ℂ) r} := by
    have hc : Continuous (fun p : WitnessCarrier => p.2.1) := by fun_prop
    exact (Metric.isClosed_closedBall.preimage hc).measurableSet
  have hw : MeasurableSet {p : WitnessCarrier | p.2.2 ∈ Metric.closedBall (0 : ℂ) r} := by
    have hc : Continuous (fun p : WitnessCarrier => p.2.2) := by fun_prop
    exact (Metric.isClosed_closedBall.preimage hc).measurableSet
  have hne : MeasurableSet {p : WitnessCarrier | p.2.1 ≠ p.2.2} := by
    have hc₁ : Continuous (fun p : WitnessCarrier => p.2.1) := by fun_prop
    have hc₂ : Continuous (fun p : WitnessCarrier => p.2.2) := by fun_prop
    exact (isOpen_ne_fun hc₁ hc₂).measurableSet
  have hd := witness_firstDist_borel
  have hs := witness_secondSetDist_borel (κ * r)
  have hpos : MeasurableSet {p : WitnessCarrier |
      (0 : ENNReal) < p.1.1 (p.2.1, p.2.2)} :=
    measurableSet_lt measurable_const hd
  have hfin : MeasurableSet {p : WitnessCarrier |
      p.1.1 (p.2.1, p.2.2) < (∞ : ENNReal)} :=
    measurableSet_lt hd measurable_const
  have hcmp : MeasurableSet {p : WitnessCarrier |
      ENNReal.ofReal C * p.1.1 (p.2.1, p.2.2) ≤
        movingOpenSetDist p.1.2 (κ * r) p.2.1 p.2.2} :=
    measurableSet_le (measurable_const.mul hd) hs
  unfold GWitness
  simpa only [Set.ofPred_and] using hz.inter (hw.inter (hne.inter (hpos.inter (hfin.inter hcmp))))

 

theorem GtildeWitness_borel (r κ C : ℝ) :
    @MeasurableSet WitnessCarrier (borel _) {p | GtildeWitness r κ C p} := by
  letI : MeasurableSpace WitnessCarrier := borel _
  letI : OpensMeasurableSpace WitnessCarrier := ⟨le_rfl⟩
  have hz : MeasurableSet {p : WitnessCarrier | p.2.1 ∈ Metric.closedBall (0 : ℂ) r} := by
    have hc : Continuous (fun p : WitnessCarrier => p.2.1) := by fun_prop
    exact (Metric.isClosed_closedBall.preimage hc).measurableSet
  have hw : MeasurableSet {p : WitnessCarrier | p.2.2 ∈ Metric.closedBall (0 : ℂ) r} := by
    have hc : Continuous (fun p : WitnessCarrier => p.2.2) := by fun_prop
    exact (Metric.isClosed_closedBall.preimage hc).measurableSet
  have hne : MeasurableSet {p : WitnessCarrier | p.2.1 ≠ p.2.2} := by
    have hc₁ : Continuous (fun p : WitnessCarrier => p.2.1) := by fun_prop
    have hc₂ : Continuous (fun p : WitnessCarrier => p.2.2) := by fun_prop
    exact (isOpen_ne_fun hc₁ hc₂).measurableSet
  have hd := witness_secondDist_borel
  have hs := witness_firstSetDist_borel (κ * r)
  have hpos : MeasurableSet {p : WitnessCarrier |
      (0 : ENNReal) < p.1.2 (p.2.1, p.2.2)} :=
    measurableSet_lt measurable_const hd
  have hfin : MeasurableSet {p : WitnessCarrier |
      p.1.2 (p.2.1, p.2.2) < (∞ : ENNReal)} :=
    measurableSet_lt hd measurable_const
  have hcmp : MeasurableSet {p : WitnessCarrier |
      p.1.2 (p.2.1, p.2.2) ≤
        ENNReal.ofReal C * movingOpenSetDist p.1.1 (κ * r) p.2.1 p.2.2} :=
    measurableSet_le hd (measurable_const.mul hs)
  unfold GtildeWitness
  simpa only [Set.ofPred_and] using hz.inter (hw.inter (hne.inter (hpos.inter (hfin.inter hcmp))))

 


def LocalWitnessRelation (a : ENNReal) (z : ℂ) (r : ℝ)
    (p : WitnessCarrier) : Prop :=
  p.2.1 ∈ Metric.ball z (r / 2) ∧
  p.2.2 ∈ Metric.ball z (r / 2) ∧
  p.2.1 ≠ p.2.2 ∧
  0 < openBallPathInf p.1.1 z r p.2.1 p.2.2 ∧
  openBallPathInf p.1.1 z r p.2.1 p.2.2 <
    boundaryBallInf p.1.1 z r p.2.1 ∧
  0 < openBallPathInf p.1.2 z r p.2.1 p.2.2 ∧
  openBallPathInf p.1.2 z r p.2.1 p.2.2 <
    boundaryBallInf p.1.2 z r p.2.1 ∧
  a * openBallPathInf p.1.1 z r p.2.1 p.2.2 <
    openBallPathInf p.1.2 z r p.2.1 p.2.2

private theorem witness_firstOpenInf_borel (z : ℂ) (r : ℝ) :
    @Measurable WitnessCarrier ENNReal (borel _) inferInstance
      (fun p => openBallPathInf p.1.1 z r p.2.1 p.2.2) := by
  have hc : Continuous (fun p : WitnessCarrier =>
      (p.1.1, (z, (r, p.2)))) := by fun_prop
  have h := openBallPathInf_joint_borel.comp hc.borel_measurable
  simpa only [Function.comp_def] using h

private theorem witness_secondOpenInf_borel (z : ℂ) (r : ℝ) :
    @Measurable WitnessCarrier ENNReal (borel _) inferInstance
      (fun p => openBallPathInf p.1.2 z r p.2.1 p.2.2) := by
  have hc : Continuous (fun p : WitnessCarrier =>
      (p.1.2, (z, (r, p.2)))) := by fun_prop
  have h := openBallPathInf_joint_borel.comp hc.borel_measurable
  simpa only [Function.comp_def] using h

private theorem witness_firstBoundary_borel (z : ℂ) (r : ℝ) :
    @Measurable WitnessCarrier ENNReal (borel _) inferInstance
      (fun p => boundaryBallInf p.1.1 z r p.2.1) := by
  have hc : Continuous (fun p : WitnessCarrier =>
      (p.1.1, (z, (r, p.2.1)))) := by fun_prop
  have h := boundaryBallInf_joint_borel.comp hc.borel_measurable
  simpa only [Function.comp_def] using h

private theorem witness_secondBoundary_borel (z : ℂ) (r : ℝ) :
    @Measurable WitnessCarrier ENNReal (borel _) inferInstance
      (fun p => boundaryBallInf p.1.2 z r p.2.1) := by
  have hc : Continuous (fun p : WitnessCarrier =>
      (p.1.2, (z, (r, p.2.1)))) := by fun_prop
  have h := boundaryBallInf_joint_borel.comp hc.borel_measurable
  simpa only [Function.comp_def] using h

 

theorem LocalWitnessRelation_borel (a : ENNReal) (z : ℂ) (r : ℝ) :
    @MeasurableSet WitnessCarrier (borel _)
      {p | LocalWitnessRelation a z r p} := by
  letI : MeasurableSpace WitnessCarrier := borel _
  letI : OpensMeasurableSpace WitnessCarrier := ⟨le_rfl⟩
  have hu : MeasurableSet {p : WitnessCarrier | p.2.1 ∈ Metric.ball z (r / 2)} := by
    have hc : Continuous (fun p : WitnessCarrier => p.2.1) := by fun_prop
    exact (Metric.isOpen_ball.preimage hc).measurableSet
  have hv : MeasurableSet {p : WitnessCarrier | p.2.2 ∈ Metric.ball z (r / 2)} := by
    have hc : Continuous (fun p : WitnessCarrier => p.2.2) := by fun_prop
    exact (Metric.isOpen_ball.preimage hc).measurableSet
  have hne : MeasurableSet {p : WitnessCarrier | p.2.1 ≠ p.2.2} := by
    have hc₁ : Continuous (fun p : WitnessCarrier => p.2.1) := by fun_prop
    have hc₂ : Continuous (fun p : WitnessCarrier => p.2.2) := by fun_prop
    exact (isOpen_ne_fun hc₁ hc₂).measurableSet
  have hd := witness_firstOpenInf_borel z r
  have he := witness_secondOpenInf_borel z r
  have hbd := witness_firstBoundary_borel z r
  have hbe := witness_secondBoundary_borel z r
  have hpD : MeasurableSet {p : WitnessCarrier |
      (0 : ENNReal) < openBallPathInf p.1.1 z r p.2.1 p.2.2} :=
    measurableSet_lt measurable_const hd
  have hbD : MeasurableSet {p : WitnessCarrier |
      openBallPathInf p.1.1 z r p.2.1 p.2.2 < boundaryBallInf p.1.1 z r p.2.1} :=
    measurableSet_lt hd hbd
  have hpE : MeasurableSet {p : WitnessCarrier |
      (0 : ENNReal) < openBallPathInf p.1.2 z r p.2.1 p.2.2} :=
    measurableSet_lt measurable_const he
  have hbE : MeasurableSet {p : WitnessCarrier |
      openBallPathInf p.1.2 z r p.2.1 p.2.2 < boundaryBallInf p.1.2 z r p.2.1} :=
    measurableSet_lt he hbe
  have hratio : MeasurableSet {p : WitnessCarrier |
      a * openBallPathInf p.1.1 z r p.2.1 p.2.2 <
        openBallPathInf p.1.2 z r p.2.1 p.2.2} :=
    measurableSet_lt (measurable_const.mul hd) he
  unfold LocalWitnessRelation
  simpa only [Set.ofPred_and] using
    hu.inter (hv.inter (hne.inter (hpD.inter (hbD.inter
      (hpE.inter (hbE.inter hratio))))))


end Uniqueness.Toolkit.MovingEndpoints
end SupercriticalLQGUniqueness
