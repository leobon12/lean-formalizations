/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR5Stages

/-!
# Conditional GFF laws and SDEs at every stopped canonical stage

The initial record and every previous stopped record are retained. The only
probabilistic input is the initial conditional GFF law; subsequent conditional
GFF laws and complete flow-line couplings follow by induction from K2.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u v

namespace InteractingSLE.Theorem14.GW2JDetR5

open Restart Exist Exist.Staged Exist.StagedLaw GW2Schedule GW2KM2

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) {S : Type v} [MeasurableSpace S]
    [StandardBorelSpace S] (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (τ : (n : ℕ) → Past S n → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (p : Ω → S) (F : Ω → DistOn upperHalfPlaneOpens)
    (hW₀ : Measurable W₀) (hp : Measurable p) (hF : Measurable F)
    (hτm : ∀ n, Measurable fun x : Past S n × ((ℝ≥0 → ℝ) × ℝ≥0∞) =>
      τ n x.1 x.2)
    (hτ : ∀ n (x : Past S n) (t : ℝ≥0),
      MeasurableSet[pathKilledSigma t] {e | τ n x e ≤ (t : ℝ≥0∞)})
    {A : Set S} (hA : MeasurableSet A)
    (hker : ∀ᵐ ω₀ ∂P, p ω₀ ∈ A →
      IsGFFWithBoundaryData (condExpKernel P (MeasurableSpace.comap p inferInstance) ω₀)
        F (W₀ (p ω₀)).fn (W₀ (p ω₀)).jumps)

include h13 hW₀ hp hF hτm hτ hA hker in
/-- At every finite stage the current field, given the entire stopped past,
has the GFF law of the recursively updated word. -/
theorem ae_isGFF_stageState : ∀ n, ∀ᵐ ω₀ ∂P,
    (stageState hκ h12p W₀ θ τ p F n ω₀).1 ∈ finitePast A n →
      IsGFFWithBoundaryData
        (condExpKernel P (MeasurableSpace.comap
          (fun ω => (stageState hκ h12p W₀ θ τ p F n ω).1) inferInstance) ω₀)
        (fun ω => (stageState hκ h12p W₀ θ τ p F n ω).2)
        (stageWord (κ := κ) W₀ θ n
          (stageState hκ h12p W₀ θ τ p F n ω₀).1).fn
        (stageWord (κ := κ) W₀ θ n
          (stageState hκ h12p W₀ θ τ p F n ω₀).1).jumps
  | 0 => hker
  | n + 1 => by
    have hx := measurable_stageState hκ h12p W₀ θ τ p F hW₀ hp hF hτm n
    exact ae_isGFF_post_stop hκ h12p h13 (θ n)
      (measurable_fst.comp hx) (measurable_snd.comp hx)
      (measurable_stageWord (κ := κ) hW₀ θ n) (measurableSet_finitePast hA n)
      (ae_isGFF_stageState n) (hτm n) (hτ n)

include h13 hW₀ hp hF hτm hτ hA hker in
/-- The next canonical piece is a full flow-line coupling under the regular
conditional law given every earlier record. No extra SDE availability input
is assumed at a later stage. -/
theorem ae_isFlowLineDriver_stagePiece (n : ℕ) : ∀ᵐ ω₀ ∂P,
    (stageState hκ h12p W₀ θ τ p F n ω₀).1 ∈ finitePast A n →
      IsFlowLineDriver κ
        (stageWord (κ := κ) W₀ θ n
          (stageState hκ h12p W₀ θ τ p F n ω₀).1).fn
        (stageWord (κ := κ) W₀ θ n
          (stageState hκ h12p W₀ θ τ p F n ω₀).1).jumps (θ n)
        (condExpKernel P (MeasurableSpace.comap
          (fun ω => (stageState hκ h12p W₀ θ τ p F n ω).1) inferInstance) ω₀)
        (fun ω => (stageState hκ h12p W₀ θ τ p F n ω).2)
        (fun t ω => (stagePiece hκ h12p W₀ θ τ p F n ω).1 t)
        (fun ω => (stagePiece hκ h12p W₀ θ τ p F n ω).2) := by
  have hx := measurable_stageState hκ h12p W₀ θ τ p F hW₀ hp hF hτm n
  have hEm := measurable_stagePiece hκ h12p W₀ θ τ p F hW₀ hp hF hτm n
  have hk := ae_isGFF_stageState hκ h12p h13 W₀ θ τ p F hW₀ hp hF hτm hτ hA hker n
  have hatom := ae_ae_eq_of_comap (P := P) (measurable_fst.comp hx)
  filter_upwards [hk, hatom] with ω₀ hgff hat hω₀
  let c := stageWord (κ := κ) W₀ θ n
    (stageState hκ h12p W₀ θ τ p F n ω₀).1
  let G : Ω → DistOn upperHalfPlaneOpens :=
    fun ω => (stageState hκ h12p W₀ θ τ p F n ω).2
  have hgff' := isGFFWithBoundaryData_flowField hκ
    c.isPiecewiseConstantBoundaryData 0 (θ n) (hgff hω₀)
  have heq : ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap
      (fun ω => (stageState hκ h12p W₀ θ τ p F n ω).1) inferInstance) ω₀),
      stagePiece hκ h12p W₀ θ τ p F n ω =
        drvOf (detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0)
          (flowLineNR c.fn c.jumps 0))
          (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
            (flowLineRhoL κ c.fn c.jumps 0 (θ n), flowLineRhoR κ c.fn c.jumps 0 (θ n))),
            flowField 0 (θ n * QuantumZipper.chiC κ) (G ω))) := by
    filter_upwards [hat] with ω hω
    change (stageState hκ h12p W₀ θ τ p F n ω).1 =
      (stageState hκ h12p W₀ θ τ p F n ω₀).1 at hω
    change wordDrv hκ h12p (θ n)
      (stageWord (κ := κ) W₀ θ n (stageState hκ h12p W₀ θ τ p F n ω).1) (G ω) = _
    rw [hω]
    exact GW2JDet.wordDrv_eq_drvOf h12p hκ (θ n) c (G ω)
  obtain ⟨𝓕, VL, VR, B, hC⟩ := isOptionalHullCoupling_drv h12p h13 hκ
    (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0) hgff' hEm heq
  exact ⟨(fun ω => flowField 0 (θ n * QuantumZipper.chiC κ) (G ω)),
    𝓕, VL, VR, B, fun ω => isTranslateAddConst_flowField 0 _ (G ω), hC⟩

include h13 hW₀ hp hF hτm hτ hA hker in
/-- A canonical stage has zero lifetime exactly at a threshold seed. In
particular, no admissible seed is killed at launch by the construction. -/
theorem ae_stage_zero_iff_threshold (n : ℕ) : ∀ᵐ ω₀ ∂P,
    (stageState hκ h12p W₀ θ τ p F n ω₀).1 ∈ finitePast A n →
    let c := stageWord (κ := κ) W₀ θ n
      (stageState hκ h12p W₀ θ τ p F n ω₀).1
    ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap
      (fun ω => (stageState hκ h12p W₀ θ τ p F n ω).1) inferInstance) ω₀),
      (stagePiece hκ h12p W₀ θ τ p F n ω).2 = 0 ↔
        ForceWord.ThresholdCondition
          (flowLineRhoL κ c.fn c.jumps 0 (θ n))
          (flowLineRhoR κ c.fn c.jumps 0 (θ n)) 0
          (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) := by
  filter_upwards [ae_isFlowLineDriver_stagePiece hκ h12p h13 W₀ θ τ p F
    hW₀ hp hF hτm hτ hA hker n] with ω₀ hω₀ hωA
  obtain ⟨X, 𝓕, VL, VR, B, -, hC⟩ := hω₀ hωA
  filter_upwards [hC.1.2.2.2.2] with ω hpath
  exact ⟨fun h0 => hpath.isForcePath.threshold_of_eq_zero h0,
    fun hth => WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hpath hth⟩

end InteractingSLE.Theorem14.GW2JDetR5
