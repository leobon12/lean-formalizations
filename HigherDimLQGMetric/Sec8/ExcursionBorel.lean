import HigherDimLQGMetric.Sec8.ExcursionMeas

/-!
# A Borel excursion observable

The boundary and collector times are found from closed hitting sets. Testing
the open collector at a dense sequence of times gives a countable description
of the excursion event. The internal distance is represented by its Borel
chain formula on length metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology Metric unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Last boundary hit before a test time. -/
def sec8Alpha (η : C(unitInterval, Rd d)) (z : Rd d) (r : ℝ)
    (τ : unitInterval) : unitInterval :=
  sec8LastHit η (ball z (4 * r))ᶜ τ

/-- First boundary hit after a test time. -/
def sec8Beta (η : C(unitInterval, Rd d)) (z : Rd d) (r : ℝ)
    (τ : unitInterval) : unitInterval :=
  sec8FirstHit η (ball z (4 * r))ᶜ τ

theorem measurable_sec8Alpha_joint (z : Rd d) (r : ℝ) :
    Measurable fun p : C(unitInterval, Rd d) × unitInterval =>
      sec8Alpha p.1 z r p.2 :=
  measurable_sec8LastHit_joint _ isOpen_ball.isClosed_compl

theorem measurable_sec8Beta_joint (z : Rd d) (r : ℝ) :
    Measurable fun p : C(unitInterval, Rd d) × unitInterval =>
      sec8Beta p.1 z r p.2 :=
  measurable_sec8FirstHit_joint _ isOpen_ball.isClosed_compl

/-- The first closed-collector hit after the left boundary. -/
def sec8SigmaFirst (η : C(unitInterval, Rd d)) (V : Set (Rd d))
    (z : Rd d) (r : ℝ) (τ : unitInterval) : unitInterval :=
  sec8FirstHit η (closure V) (sec8Alpha η z r τ)

/-- The last closed-collector hit before the right boundary. -/
def sec8SigmaLast (η : C(unitInterval, Rd d)) (V : Set (Rd d))
    (z : Rd d) (r : ℝ) (τ : unitInterval) : unitInterval :=
  sec8LastHit η (closure V) (sec8Beta η z r τ)

theorem measurable_sec8SigmaFirst_joint (V : Set (Rd d)) (z : Rd d) (r : ℝ) :
    Measurable fun p : C(unitInterval, Rd d) × unitInterval =>
      sec8SigmaFirst p.1 V z r p.2 := by
  exact (measurable_sec8FirstHit_joint _ isClosed_closure).comp
    (measurable_fst.prodMk (measurable_sec8Alpha_joint z r))

theorem measurable_sec8SigmaLast_joint (V : Set (Rd d)) (z : Rd d) (r : ℝ) :
    Measurable fun p : C(unitInterval, Rd d) × unitInterval =>
      sec8SigmaLast p.1 V z r p.2 := by
  exact (measurable_sec8LastHit_joint _ isClosed_closure).comp
    (measurable_fst.prodMk (measurable_sec8Beta_joint z r))

theorem measurable_sec8SigmaFirst_fixed (V : Set (Rd d)) (z : Rd d)
    (r : ℝ) (τ : unitInterval) :
    Measurable fun η : C(unitInterval, Rd d) => sec8SigmaFirst η V z r τ := by
  unfold sec8SigmaFirst sec8Alpha
  exact (measurable_sec8FirstHit_joint _ isClosed_closure).comp
    (measurable_id.prodMk
      (measurable_sec8LastHit _ isOpen_ball.isClosed_compl τ))

theorem measurable_sec8SigmaLast_fixed (V : Set (Rd d)) (z : Rd d)
    (r : ℝ) (τ : unitInterval) :
    Measurable fun η : C(unitInterval, Rd d) => sec8SigmaLast η V z r τ := by
  unfold sec8SigmaLast sec8Beta
  exact (measurable_sec8LastHit_joint _ isClosed_closure).comp
    (measurable_id.prodMk
      (measurable_sec8FirstHit _ isOpen_ball.isClosed_compl τ))

/-- Borel excursion test at one time. The collector visit has its own
countable test time `υ`; `τ` locates the component inside the ball. -/
def sec8ExcAtBorel (η : C(unitInterval, Rd d)) (D : ContMetric d)
    (V : Set (Rd d)) (z : Rd d) (r ϑ : ℝ)
    (τ υ : unitInterval) : Prop :=
  η τ ∈ ball z (4 * r) ∧
  sec8Alpha η z r τ < τ ∧ τ < sec8Beta η z r τ ∧
  sec8Alpha η z r τ < υ ∧ υ < sec8Beta η z r τ ∧ η υ ∈ V ∧
  sec8Alpha η z r τ < sec8SigmaFirst η V z r τ ∧
  sec8SigmaFirst η V z r τ ≤ sec8SigmaLast η V z r τ ∧
  sec8SigmaLast η V z r τ < sec8Beta η z r τ ∧
  ENNReal.ofReal ϑ ≤ D.chainInf (ball z (4 * r))
    (η (sec8SigmaFirst η V z r τ)) (η (sec8SigmaLast η V z r τ))

/-- Countable dense-time encoding of an excursion. -/
def ExcBorel (η : C(unitInterval, Rd d)) (D : ContMetric d)
    (V : Set (Rd d)) (z : Rd d) (r ϑ : ℝ) : Prop :=
  ∃ n m : ℕ, sec8ExcAtBorel η D V z r ϑ
    (TopologicalSpace.denseSeq unitInterval n)
    (TopologicalSpace.denseSeq unitInterval m)

theorem measurableSet_sec8ExcAtBorel (V : Set (Rd d)) (hV : IsOpen V)
    (z : Rd d) (r ϑ : ℝ) (τ υ : unitInterval) :
    MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d |
      sec8ExcAtBorel p.1 p.2 V z r ϑ τ υ} := by
  let α : C(unitInterval, Rd d) × ContMetric d → unitInterval :=
    fun p => sec8Alpha p.1 z r τ
  let β : C(unitInterval, Rd d) × ContMetric d → unitInterval :=
    fun p => sec8Beta p.1 z r τ
  let σ₁ : C(unitInterval, Rd d) × ContMetric d → unitInterval :=
    fun p => sec8SigmaFirst p.1 V z r τ
  let σ₂ : C(unitInterval, Rd d) × ContMetric d → unitInterval :=
    fun p => sec8SigmaLast p.1 V z r τ
  have hp : Measurable fun p : C(unitInterval, Rd d) × ContMetric d => p.1 := measurable_fst
  have hα : Measurable α := (measurable_sec8Alpha_joint z r).comp
    (hp.prodMk measurable_const)
  have hβ : Measurable β := (measurable_sec8Beta_joint z r).comp
    (hp.prodMk measurable_const)
  have hσ₁ : Measurable σ₁ := by
    exact (measurable_sec8SigmaFirst_fixed V z r τ).comp hp
  have hσ₂ : Measurable σ₂ := by
    exact (measurable_sec8SigmaLast_fixed V z r τ).comp hp
  have heval₁ : Measurable fun p : C(unitInterval, Rd d) × ContMetric d => p.1 (σ₁ p) :=
    continuous_eval.measurable.comp (hp.prodMk hσ₁)
  have heval₂ : Measurable fun p : C(unitInterval, Rd d) × ContMetric d => p.1 (σ₂ p) :=
    continuous_eval.measurable.comp (hp.prodMk hσ₂)
  have hchain : Measurable fun p : C(unitInterval, Rd d) × ContMetric d =>
      p.2.chainInf (ball z (4 * r)) (p.1 (σ₁ p)) (p.1 (σ₂ p)) :=
    (ContMetric.measurable_chainInf _).comp
      (measurable_snd.prodMk (heval₁.prodMk heval₂))
  have h₁ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d |
      p.1 τ ∈ ball z (4 * r)} :=
    (((continuous_eval_const τ).measurable.comp hp) isOpen_ball.measurableSet)
  have h₂ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d | α p < τ} :=
    measurableSet_lt hα measurable_const
  have h₃ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d | τ < β p} :=
    measurableSet_lt measurable_const hβ
  have h₄ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d | α p < υ} :=
    measurableSet_lt hα measurable_const
  have h₅ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d | υ < β p} :=
    measurableSet_lt measurable_const hβ
  have h₆ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d | p.1 υ ∈ V} :=
    (((continuous_eval_const υ).measurable.comp hp) hV.measurableSet)
  have h₇ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d | α p < σ₁ p} :=
    measurableSet_lt hα hσ₁
  have h₈ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d | σ₁ p ≤ σ₂ p} :=
    measurableSet_le hσ₁ hσ₂
  have h₉ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d | σ₂ p < β p} :=
    measurableSet_lt hσ₂ hβ
  have h₁₀ : MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d |
      ENNReal.ofReal ϑ ≤ p.2.chainInf (ball z (4 * r))
        (p.1 (σ₁ p)) (p.1 (σ₂ p))} :=
    measurableSet_le measurable_const hchain
  change MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d |
    p.1 τ ∈ ball z (4 * r) ∧ α p < τ ∧ τ < β p ∧ α p < υ ∧
    υ < β p ∧ p.1 υ ∈ V ∧ α p < σ₁ p ∧ σ₁ p ≤ σ₂ p ∧
    σ₂ p < β p ∧ ENNReal.ofReal ϑ ≤ p.2.chainInf (ball z (4 * r))
      (p.1 (σ₁ p)) (p.1 (σ₂ p))}
  exact h₁.inter (h₂.inter (h₃.inter (h₄.inter (h₅.inter (h₆.inter
    (h₇.inter (h₈.inter (h₉.inter h₁₀))))))))

theorem measurableSet_ExcBorel (V : Set (Rd d)) (hV : IsOpen V)
    (z : Rd d) (r ϑ : ℝ) :
    MeasurableSet {p : C(unitInterval, Rd d) × ContMetric d |
      ExcBorel p.1 p.2 V z r ϑ} := by
  have heq : {p : C(unitInterval, Rd d) × ContMetric d |
      ExcBorel p.1 p.2 V z r ϑ} =
      ⋃ n : ℕ, ⋃ m : ℕ, {p | sec8ExcAtBorel p.1 p.2 V z r ϑ
        (TopologicalSpace.denseSeq unitInterval n)
        (TopologicalSpace.denseSeq unitInterval m)} := by
    ext p
    simp only [ExcBorel, mem_ofPred_eq, mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    measurableSet_sec8ExcAtBorel V hV z r ϑ _ _

/-- Measurability remains valid when the path, metric, and threshold are all
measurable functions of a common input. -/
theorem measurableSet_ExcBorel_comp {Ω : Type} [MeasurableSpace Ω]
    {η : Ω → C(unitInterval, Rd d)} {D : Ω → ContMetric d} {ϑ : Ω → ℝ}
    (hη : Measurable η) (hD : Measurable D) (hϑ : Measurable ϑ)
    (V : Set (Rd d)) (hV : IsOpen V) (z : Rd d) (r : ℝ) :
    MeasurableSet {ω : Ω | ExcBorel (η ω) (D ω) V z r (ϑ ω)} := by
  have hat (τ υ : unitInterval) :
      MeasurableSet {ω : Ω | sec8ExcAtBorel (η ω) (D ω) V z r (ϑ ω) τ υ} := by
    have hbase : MeasurableSet {ω : Ω |
        sec8ExcAtBorel (η ω) (D ω) V z r 0 τ υ} :=
      (hη.prodMk hD) (measurableSet_sec8ExcAtBorel V hV z r 0 τ υ)
    have hσ₁ : Measurable fun ω : Ω => sec8SigmaFirst (η ω) V z r τ :=
      (measurable_sec8SigmaFirst_fixed V z r τ).comp hη
    have hσ₂ : Measurable fun ω : Ω => sec8SigmaLast (η ω) V z r τ :=
      (measurable_sec8SigmaLast_fixed V z r τ).comp hη
    have heval₁ : Measurable fun ω : Ω => η ω (sec8SigmaFirst (η ω) V z r τ) :=
      continuous_eval.measurable.comp (hη.prodMk hσ₁)
    have heval₂ : Measurable fun ω : Ω => η ω (sec8SigmaLast (η ω) V z r τ) :=
      continuous_eval.measurable.comp (hη.prodMk hσ₂)
    have hchain : Measurable fun ω : Ω =>
        (D ω).chainInf (ball z (4 * r))
          (η ω (sec8SigmaFirst (η ω) V z r τ))
          (η ω (sec8SigmaLast (η ω) V z r τ)) :=
      (ContMetric.measurable_chainInf _).comp
        (hD.prodMk (heval₁.prodMk heval₂))
    have hthreshold : MeasurableSet {ω : Ω |
        ENNReal.ofReal (ϑ ω) ≤ (D ω).chainInf (ball z (4 * r))
          (η ω (sec8SigmaFirst (η ω) V z r τ))
          (η ω (sec8SigmaLast (η ω) V z r τ))} :=
      measurableSet_le (ENNReal.measurable_ofReal.comp hϑ) hchain
    have heq : {ω : Ω | sec8ExcAtBorel (η ω) (D ω) V z r (ϑ ω) τ υ} =
        {ω : Ω | sec8ExcAtBorel (η ω) (D ω) V z r 0 τ υ} ∩
        {ω : Ω | ENNReal.ofReal (ϑ ω) ≤ (D ω).chainInf (ball z (4 * r))
          (η ω (sec8SigmaFirst (η ω) V z r τ))
          (η ω (sec8SigmaLast (η ω) V z r τ))} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, sec8ExcAtBorel,
        ENNReal.ofReal_zero, zero_le, and_true, and_assoc]
    rw [heq]
    exact hbase.inter hthreshold
  have heq : {ω : Ω | ExcBorel (η ω) (D ω) V z r (ϑ ω)} =
      ⋃ n : ℕ, ⋃ m : ℕ, {ω : Ω |
        sec8ExcAtBorel (η ω) (D ω) V z r (ϑ ω)
          (TopologicalSpace.denseSeq unitInterval n)
          (TopologicalSpace.denseSeq unitInterval m)} := by
    ext ω
    simp only [ExcBorel, mem_ofPred_eq, mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m => hat _ _

end HigherDimLQGMetric
