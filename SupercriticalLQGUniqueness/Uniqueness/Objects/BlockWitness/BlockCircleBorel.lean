import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness.BlockGeoCode
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact




 


set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness

private def circlePoint (c : ℂ) (R : NNReal) (θ : ℝ) : ℂ :=
  c + (R : ℂ) * Complex.exp (θ * Complex.I)

private theorem circlePoint_sphere (c : ℂ) (R : NNReal) (θ : ℝ) :
    circlePoint c R θ ∈ sphere c (R : ℝ) := by
  rw [mem_sphere, dist_eq_norm, circlePoint, add_sub_cancel_left,
    norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact abs_of_nonneg R.property

private theorem circlePoint_closedBall (c : ℂ) (R : NNReal) (θ : ℝ) :
    circlePoint c R θ ∈ closedBall c (R : ℝ) :=
  mem_closedBall.mpr (le_of_eq (circlePoint_sphere c R θ))

private def circlePointSub (c : ℂ) (R : NNReal) (θ : ℝ) : closedBall c (R : ℝ) :=
  ⟨circlePoint c R θ, circlePoint_closedBall c R θ⟩

private theorem circlePointSub_measurable (c : ℂ) (R : NNReal) :
    Measurable (circlePointSub c R) := by
  apply Measurable.subtype_mk
  unfold circlePoint
  fun_prop

private abbrev CircleInput (c : ℂ) (R : NNReal) :=
  LSCMetric × ((closedBall c (R : ℝ)) × ℝ)

private def badAngle (c : ℂ) (R : NNReal)
    (p : CircleInput c R × ℝ) : Prop :=
  p.2 ∈ Set.Ico 0 (2 * Real.pi) ∧
    ¬ p.1.1.internal (closedBall c (R : ℝ))
      (circlePointSub c R p.2, p.1.2.1) ≤ ENNReal.ofReal p.1.2.2

private theorem measurableSet_badAngle (c : ℂ) (R : NNReal) :
    MeasurableSet {p : CircleInput c R × ℝ | badAngle c R p} := by
  let K : Set ℂ := closedBall c (R : ℝ)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hcp : Measurable (fun p : CircleInput c R × ℝ => circlePointSub c R p.2) :=
    (circlePointSub_measurable c R).comp measurable_snd
  have hu : Measurable (fun p : CircleInput c R × ℝ => p.1.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_fst
  have hd : Measurable (fun p : CircleInput c R × ℝ => p.1.1) :=
    measurable_fst.comp measurable_fst
  let f : LSCMetric × (K × K) → ENNReal :=
    fun q => q.1.internal K (q.2.1, q.2.2)
  let h : CircleInput c R × ℝ → LSCMetric × (K × K) :=
    fun p => (p.1.1, (circlePointSub c R p.2, p.1.2.1))
  have hf : Measurable f := (Toolkit.MovingEndpoints.internal_compact_joint_lsc hK).measurable
  have hh : Measurable h := hd.prodMk (hcp.prodMk hu)
  have hcost : Measurable (fun p : CircleInput c R × ℝ =>
      p.1.1.internal K (circlePointSub c R p.2, p.1.2.1)) := by
    change Measurable (f ∘ h)
    exact hf.comp hh
  have hB : Measurable (fun p : CircleInput c R × ℝ =>
      ENNReal.ofReal p.1.2.2) := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_snd.comp measurable_snd).comp measurable_fst)
  exact (measurableSet_Ico.preimage measurable_snd).inter
    (measurableSet_le hcost hB).compl

 

theorem measurable_circle_bad (c : ℂ) (R : NNReal) :
    Measurable (fun p : CircleInput c R =>
      Objects.Shadow.circleOuter c R 0
        (sphere c (R : ℝ) \
          Objects.Producer.goodSet p.1 c p.2.1 (R : ℝ) p.2.2 p.2.1.property)) := by
  have hangle : Measurable (fun p : CircleInput c R =>
      ENNReal.ofReal (R : ℝ) * volume
        {θ : ℝ | (p, θ) ∈ {q | badAngle c R q}}) :=
    measurable_const.mul (measurable_measure_prodMk_left (measurableSet_badAngle c R))
  convert hangle using 1
  funext p
  unfold Objects.Shadow.circleOuter
  congr 1
  congr 1
  ext θ
  have hs : c + (R : ℂ) * Complex.exp (θ * Complex.I) ∈ sphere c (R : ℝ) :=
    circlePoint_sphere c R θ
  have hc : c + (R : ℂ) * Complex.exp (θ * Complex.I) ∈ closedBall c (R : ℝ) :=
    circlePoint_closedBall c R θ
  simp only [Set.mem_ofPred_eq, badAngle, Set.mem_sdiff, Objects.Producer.goodSet,
    zero_add, hs, true_and]
  constructor
  · rintro ⟨hθ, hnot⟩
    refine ⟨hθ, ?_⟩
    intro hcost
    apply hnot
    exact ⟨hc, by simpa only [circlePointSub, circlePoint] using hcost⟩
  · rintro ⟨hθ, hnot⟩
    refine ⟨hθ, ?_⟩
    rintro ⟨hx, hcost⟩
    apply hnot
    simpa only [circlePointSub, circlePoint] using hcost


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness
