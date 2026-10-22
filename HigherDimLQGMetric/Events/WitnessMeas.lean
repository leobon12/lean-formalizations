import HigherDimLQGMetric.Events.ScaledEvent
import HigherDimLQGMetric.Select.Internal
import HigherDimLQGMetric.Field.StandardBorel
import LQGMetric.Meas.UM
import Mathlib.Topology.UnitInterval

/-!
# The path length observable

Port of the measurable path-length input in GM S3 `GoodAnnulusMeas4a`.
This is the first ingredient of the analytic witness-event projection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Topology MeasureTheory unitInterval
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open LQGMetric
open scoped ENNReal

variable {d : ℕ}

private def pathProj (t : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one t

private theorem pathProj_coe_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (pathProj t : ℝ) = t := by
  simp [pathProj, Set.projIcc_of_mem _ ht]

/-- A continuous unit-interval path, extended to a real-parameter path. -/
def pathExt (η : C(unitInterval, Rd d)) (t : ℝ) : Rd d := η (pathProj t)

theorem pathExt_continuousOn (η : C(unitInterval, Rd d)) :
    ContinuousOn (pathExt η) (Icc 0 1) :=
  (η.continuous.comp continuous_projIcc).continuousOn

theorem pathExt_zero (η : C(unitInterval, Rd d)) : pathExt η 0 = η 0 := by
  simp only [pathExt]
  rw [show pathProj 0 = 0 from Set.projIcc_left zero_le_one]

theorem pathExt_one (η : C(unitInterval, Rd d)) : pathExt η 1 = η 1 := by
  simp only [pathExt]
  rw [show pathProj 1 = 1 from Set.projIcc_right zero_le_one]

theorem pathExt_range (η : C(unitInterval, Rd d)) :
    pathExt η '' Icc 0 1 = range η := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨pathProj t, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t, t.2, ?_⟩
    exact congrArg η (Subtype.ext (pathProj_coe_of_mem t.2))

/-- A path continuous on `[0,1]` has an equivalent continuous-map encoding. -/
theorem exists_pathContinuousMap {P : ℝ → Rd d}
    (hP : ContinuousOn P (Icc 0 1)) :
    ∃ η : C(unitInterval, Rd d),
      EqOn (pathExt η) P (Icc 0 1) ∧
      ∀ D : ContMetric d, D.len (pathExt η) 0 1 = D.len P 0 1 := by
  let η : C(unitInterval, Rd d) :=
    ⟨fun t => P t, hP.comp_continuous continuous_subtype_val (fun t => t.2)⟩
  have he : EqOn (pathExt η) P (Icc 0 1) := by
    intro t ht
    simp only [pathExt, η, ContinuousMap.coe_mk, pathProj_coe_of_mem ht]
  exact ⟨η, he, fun D => D.len_congr he⟩

/-- The metric length of a continuous unit-interval path is lower
semicontinuous in both the metric and path. -/
theorem lowerSemicontinuous_lenPath :
    LowerSemicontinuous fun p : ContMetric d × C(unitInterval, Rd d) =>
      p.1.len (pathExt p.2) 0 1 := by
  have e : (fun p : ContMetric d × C(unitInterval, Rd d) =>
      p.1.len (pathExt p.2) 0 1) =
      fun p => ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1},
        ∑ i ∈ Finset.range q.1,
          ENNReal.ofReal (p.1.1 (p.2 (pathProj (q.2.1 (i + 1))), p.2 (pathProj (q.2.1 i)))) := by
    funext p
    unfold ContMetric.len curveLength eVariationOn pathExt
    simp only [Function.comp_apply, ContMetric.edist_pt]
  rw [e]
  refine lowerSemicontinuous_iSup fun q => Continuous.lowerSemicontinuous ?_
  refine continuous_finsetSum _ fun i _ => ENNReal.continuous_ofReal.comp ?_
  exact continuous_contMetric_apply_select.comp (continuous_fst.prodMk
    (((continuous_eval_const _).comp continuous_snd).prodMk
      ((continuous_eval_const _).comp continuous_snd)))

/-- Joint Borel measurability of the path length. -/
theorem measurable_lenPath :
    Measurable fun p : ContMetric d × C(unitInterval, Rd d) =>
      p.1.len (pathExt p.2) 0 1 :=
  lowerSemicontinuous_lenPath.measurable

/-- Borel version of the witness relation, replacing internal distances by
their countable-chain formulas. On length metrics it is the source relation. -/
def witnessRelBorel (A B : DistRd d → ContMetric d)
    (ξ Q ℓ t r : ℝ) (z : Rd d) :
    Set (DistRd d × C(unitInterval, Rd d)) :=
  {p | (∀ s : unitInterval, p.2 s ∈ annCl z r (2 * r)) ∧
    (A p.1).len (pathExt p.2) 0 1 =
      (A p.1).chainInf (ann z (3 * r / 4) (3 * r)) (p.2 0) (p.2 1) ∧
    ENNReal.ofReal (ℓ / 2 * sNorm ξ Q p.1 r z) ≤
      (A p.1).len (pathExt p.2) 0 1 ∧
    (A p.1).len (pathExt p.2) 0 1 ≤
      ENNReal.ofReal (ℓ * sNorm ξ Q p.1 r z) ∧
    ENNReal.ofReal t * (A p.1).len (pathExt p.2) 0 1 <
      (B p.1).chainInf (ann z (3 * r / 4) (3 * r)) (p.2 0) (p.2 1)}

set_option maxHeartbeats 1000000

/-- The path witness relation is Borel before projection. -/
theorem measurableSet_witnessRelBorel {A B : DistRd d → ContMetric d}
    (hA : Measurable A) (hB : Measurable B)
    (ξ Q ℓ t r : ℝ) (z : Rd d) :
    MeasurableSet (witnessRelBorel A B ξ Q ℓ t r z) := by
  let O : Set (Rd d) := ann z (3 * r / 4) (3 * r)
  have hη (s : unitInterval) :
      Measurable fun p : DistRd d × C(unitInterval, Rd d) => p.2 s :=
    (continuous_eval_const s).measurable.comp measurable_snd
  have hs : Measurable fun p : DistRd d × C(unitInterval, Rd d) =>
      sNorm ξ Q p.1 r z := by
    exact (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left r z)))).comp measurable_fst
  have hLA : Measurable fun p : DistRd d × C(unitInterval, Rd d) =>
      (A p.1).len (pathExt p.2) 0 1 :=
    measurable_lenPath.comp ((hA.comp measurable_fst).prodMk measurable_snd)
  have hIA : Measurable fun p : DistRd d × C(unitInterval, Rd d) =>
      (A p.1).chainInf O (p.2 0) (p.2 1) :=
    (ContMetric.measurable_chainInf O).comp
      ((hA.comp measurable_fst).prodMk ((hη 0).prodMk (hη 1)))
  have hIB : Measurable fun p : DistRd d × C(unitInterval, Rd d) =>
      (B p.1).chainInf O (p.2 0) (p.2 1) :=
    (ContMetric.measurable_chainInf O).comp
      ((hB.comp measurable_fst).prodMk ((hη 0).prodMk (hη 1)))
  have hLow : Measurable fun p : DistRd d × C(unitInterval, Rd d) =>
      ENNReal.ofReal (ℓ / 2 * sNorm ξ Q p.1 r z) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hs)
  have hHigh : Measurable fun p : DistRd d × C(unitInterval, Rd d) =>
      ENNReal.ofReal (ℓ * sNorm ξ Q p.1 r z) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hs)
  have hRatio : Measurable fun p : DistRd d × C(unitInterval, Rd d) =>
      ENNReal.ofReal t * (A p.1).len (pathExt p.2) 0 1 :=
    measurable_const.mul hLA
  unfold witnessRelBorel
  have hclosed : MeasurableSet {p : DistRd d × C(unitInterval, Rd d) |
      ∀ s : unitInterval, p.2 s ∈ annCl z r (2 * r)} := by
    have hc : IsClosed {η : C(unitInterval, Rd d) |
        ∀ s : unitInterval, η s ∈ annCl z r (2 * r)} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun s => (isClosed_annCl z r (2 * r)).preimage
        (continuous_eval_const s)
    exact hc.measurableSet.preimage measurable_snd
  exact hclosed.inter ((measurableSet_eq_fun hLA hIA).inter
    ((measurableSet_le hLow hLA).inter
      ((measurableSet_le hLA hHigh).inter
        (measurableSet_lt hRatio hIB))))

/-- The existential path relation is universally measurable. -/
theorem uMeasurableSet_exists_witnessRelBorel
    {A B : DistRd d → ContMetric d} (hA : Measurable A) (hB : Measurable B)
    (ξ Q ℓ t r : ℝ) (z : Rd d) :
    UMeasurableSet {g : DistRd d | ∃ η : C(unitInterval, Rd d),
      (g, η) ∈ witnessRelBorel A B ξ Q ℓ t r z} :=
  UMeasurableSet.setOf_exists (measurableSet_witnessRelBorel hA hB ξ Q ℓ t r z)

private theorem annCl_subset_outerAnn (z : Rd d) {r : ℝ} (hr : 0 < r) :
    annCl z r (2 * r) ⊆ ann z (3 * r / 4) (3 * r) := by
  intro x hx
  dsimp [ann, annCl] at hx ⊢
  constructor <;> linarith

/-- On length metrics, the Borel path relation is exactly the existential
part of the source witness event. -/
theorem witEvent_iff_exists_witnessRelBorel
    (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ t : ℝ)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (g : DistRd d)
    (hA : (A g).IsLength) (hB : (B g).IsLength) :
    g ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z ↔
      g ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z ∧
        ∃ η : C(unitInterval, Rd d),
          (g, η) ∈ witnessRelBorel A B ξ Q ℓ t r z := by
  let O : Set (Rd d) := ann z (3 * r / 4) (3 * r)
  have hO : IsOpen O := isOpen_ann _ _ _
  have hIO := annCl_subset_outerAnn z hr
  constructor
  · rintro ⟨hReg, P, hPI, ⟨hPc, hPO, hGeo⟩, hLow, hHigh, hRatio⟩
    obtain ⟨η, hηP, hLen⟩ := exists_pathContinuousMap hPc
    refine ⟨hReg, η, ?_⟩
    have h0 : pathExt η 0 = P 0 := hηP (by norm_num)
    have h1 : pathExt η 1 = P 1 := hηP (by norm_num)
    have hη0 : η 0 = P 0 := (pathExt_zero η).symm.trans h0
    have hη1 : η 1 = P 1 := (pathExt_one η).symm.trans h1
    have hηI : ∀ s : unitInterval, η s ∈ annCl z r (2 * r) := by
      intro s
      have hp : pathProj (s : ℝ) = s := Subtype.ext (pathProj_coe_of_mem s.2)
      have he : η s = P s := by
        calc
          η s = pathExt η (s : ℝ) := by simp only [pathExt, hp]
          _ = P s := hηP s.2
      rw [he]
      exact hPI s s.2
    unfold witnessRelBorel
    refine ⟨hηI, ?_, ?_, ?_, ?_⟩
    · change (A g).len (pathExt η) 0 1 = (A g).chainInf O (η 0) (η 1)
      rw [← (A g).internal_eq_chainInf hA hO, hη0, hη1, hLen]
      exact hGeo
    · rw [hLen]
      exact hLow
    · rw [hLen]
      exact hHigh
    · change ENNReal.ofReal t * (A g).len (pathExt η) 0 1 <
        (B g).chainInf O (η 0) (η 1)
      rw [hLen, ← (B g).internal_eq_chainInf hB hO, hη0, hη1]
      exact hRatio
  · rintro ⟨hReg, η, hRel⟩
    rcases hRel with ⟨hηI, hGeo, hLow, hHigh, hRatio⟩
    let P : ℝ → Rd d := pathExt η
    have hP0 : P 0 = η 0 := pathExt_zero η
    have hP1 : P 1 = η 1 := pathExt_one η
    have hPI : ∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl z r (2 * r) :=
      fun τ _ => hηI (pathProj τ)
    have hPO : ∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ O :=
      fun τ hτ => hIO (hPI τ hτ)
    have hGeo' : (A g).len P 0 1 = (A g).internal O (P 0) (P 1) := by
      rw [hP0, hP1, (A g).internal_eq_chainInf hA hO]
      exact hGeo
    have hRatio' : ENNReal.ofReal t * (A g).len P 0 1 <
        (B g).internal O (P 0) (P 1) := by
      rw [hP0, hP1, (B g).internal_eq_chainInf hB hO]
      exact hRatio
    exact ⟨hReg, P, hPI, ⟨pathExt_continuousOn η, hPO, hGeo'⟩,
      hLow, hHigh, hRatio'⟩

/-- Once the regular event is null-measurable, the witness event is too.
The only further inputs are the almost-sure length axioms. -/
theorem nullMeasurableSet_witEvent_of_regular
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : Measurable h)
    {A B : DistRd d → ContMetric d} (hA : Measurable A) (hB : Measurable B)
    (ξ Q U a A₀ ℓ β₀ t : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hLenA : ∀ᵐ ω ∂P, (A (h ω)).IsLength)
    (hLenB : ∀ᵐ ω ∂P, (B (h ω)).IsLength)
    (hReg : NullMeasurableSet
      (h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z) P) :
    NullMeasurableSet (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) P := by
  let E : Set (DistRd d) := {g | ∃ η : C(unitInterval, Rd d),
    (g, η) ∈ witnessRelBorel A B ξ Q ℓ t r z}
  have hE : NullMeasurableSet (h ⁻¹' E) P :=
    (uMeasurableSet_exists_witnessRelBorel hA hB ξ Q ℓ t r z).nullMeasurableSet_preimage
      hh.aemeasurable
  have heq : h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z =ᵐ[P]
      (h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z) ∩ (h ⁻¹' E) := by
    filter_upwards [hLenA, hLenB] with ω hlA hlB
    exact propext (witEvent_iff_exists_witnessRelBorel A B ξ Q U a A₀ ℓ β₀ t hr z
      (h ω) hlA hlB)
  exact (hReg.inter hE).congr heq.symm

end HigherDimLQGMetric
