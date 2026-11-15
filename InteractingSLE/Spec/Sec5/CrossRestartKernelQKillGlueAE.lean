/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQKillGlueMeas
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRouteQ

/-!
# Lemma 4.7 in the chart `Q`: almost every glued sample is good

Packet PROVE-CFRESTART4, item D1 (the Lemma 4.7 mirror of GLUECOND5's `cfGlueAE_isGood49` and `glueGood`). In the
setting of `Prop411Q.CfGlueAE`, almost every glued sample is good for the killed image word of the counterflow
(`Kill47.IsGood47`): the flow path is good with a generating trace in `ℍ` at positive times (Lemma 4.5 and Aux. lemma 7
for the (4.4) flow word), the counterflow history is a good hitting history (GLUECOND3), and the counterflow's trace
does not return to `0` (**the barrier no-return** `CfNoReturn.Route.CounterflowNoReturnAdmStatement`, which Zhan's
Part A inputs at `16/κ` give in both forms: `counterflowNoReturnAdmStatement_of_partA`, `…_of_partA_of_clearance`).

* **`ae_isGood47`**;
* `glueGood47 μ W VL VR ζ`: a measurable set of good glued samples, of full measure (`ae_mem_glueGood47`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q

namespace Kill47

/-- **Almost every glued sample is good** for the killed image word of the counterflow (given the barrier no-return of
centred counterflows, which Part A supplies). -/
theorem ae_isGood47 (hNR : CfNoReturn.Route.CounterflowNoReturnAdmStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      IsGood47 W VL VR ζ p := by
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hline] with ω hω using hω.1
  have hflow : ∀ᵐ ω ∂P, Aux50Hit.IsGoodPath W VL VR ζ ω ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ (∀ t : ℝ≥0, 0 < t → η t ∈ H) ∧
        seedLine ζ W ω = fun s : ℝ => η s.toNNReal := by
    filter_upwards [hline, Aux50Hit.ae_isGoodPath hC.1 hζ] with ω ⟨_, ⟨η, hη, he⟩, hP⟩ hg
    refine ⟨hg, η, hη, fun t ht => ?_, he⟩
    have h1 := hP.mem_H t ht
    rw [he] at h1
    simpa only [Real.toNNReal_coe] using h1
  have hfst := ae_glue_fst (μ := P) k hXm hflow
  have hhit := cfGlueAE_mem_goodHitSet κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hnr : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) hXm), p.2 ∈ Prop49Exit.nrSet :=
    ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf)
      (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw k hk
      Prop49Exit.measurableSet_nrSet (Prop49Exit.ae_cfHistory_mem_nrSet_of_adm hNR hκ hκ4 hF h44 hC hcf hlaw)
  filter_upwards [hfst, hhit, hnr] with p h1 h2 h3
  exact ⟨h1.1, h1.2, h2, fun u hu => Prop49Exit.histLine_ne_zero_of_mem_nrSet h3 hu⟩

section Good

variable {Ω : Type*} [MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {μ : Measure (Ω × HistorySpace 0 0)}

/-- **A measurable set of good glued samples** of full `μ`-measure (when good samples have full measure). -/
def glueGood47 (μ : Measure (Ω × HistorySpace 0 0)) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Set (Ω × HistorySpace 0 0) :=
  (toMeasurable μ {p | ¬ IsGood47 W VL VR ζ p})ᶜ

theorem measurableSet_glueGood47 : MeasurableSet (glueGood47 μ W VL VR ζ) :=
  (measurableSet_toMeasurable _ _).compl

theorem isGood47_of_mem_glueGood47 : ∀ p ∈ glueGood47 μ W VL VR ζ, IsGood47 W VL VR ζ p := fun p hp => by
  by_contra h
  exact hp (subset_toMeasurable _ _ h)

theorem ae_mem_glueGood47 (hae : ∀ᵐ p ∂μ, IsGood47 W VL VR ζ p) : ∀ᵐ p ∂μ, p ∈ glueGood47 μ W VL VR ζ := by
  rw [ae_iff]
  have : {a | ¬ a ∈ glueGood47 μ W VL VR ζ} = toMeasurable μ {p | ¬ IsGood47 W VL VR ζ p} := by
    ext p; simp [glueGood47]
  rw [this, measure_toMeasurable]
  exact ae_iff.1 hae

end Good

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
