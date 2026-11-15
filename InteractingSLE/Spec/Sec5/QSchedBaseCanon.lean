/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedChart
import InteractingSLE.Spec.Sec5.CfChartSetup

/-!
# Lemma 4.7's positive-time chart clause under the (4.4) heights

Packet PROVE-QSCHED. `CfChart.exists_chartCanon_omega` assumes Aux. lemma 130's uniform heights but uses them only
through the (4.4) heights at the prefix angle `θ₀` and at `π/2` (`CfChart.isHeightBounded44_of_strip`, lines 162–164
of `CfChartSetup.lean`). `exists_chartCanon_omega44` is that theorem under exactly these two height hypotheses; its
proof is the landed proof verbatim, with the two derived heights replaced by the hypotheses.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.QSched

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q CrossCond.Theta
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Lemma47Angle CfGiven CfChart
open Sec7.StripHeights44 (IsHeightBounded44)

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {θ₀ : ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Lemma 4.7's chart clause on the given space under the (4.4) heights** (`CfChart.exists_chartCanon_omega` with
Aux. lemma 130's heights replaced by the (4.4) heights at `θ₀` and `π/2`, the only consequences of them it uses).
The flow
coupling of the driver `W` (field `h′ = h + θ₀χ`), a coarse σ-algebra `m` of `Ω` and a coarse-measurable good set
`E` with: the killing time of the counterflow's image word infinite on `E`, the sample `(ω, cfHistory W′ ζ′ ω)` in `E`
almost surely, and the chart coupling clause of the field `−h′` (constants `−(π − θ₀)χ`, `−χ`) on `Ω` for the
pulled-back raw image filtration. -/
theorem exists_chartCanon_omega44 (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hθ : IsHeightBounded44 κ b J θ₀) (hπ : IsHeightBounded44 κ b J (π / 2))
    (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hD : IsFlowLineDriver κ b J θ₀ P h W ζ) {s : ℝ≥0} (hs : 0 < s) :
    ∃ (h' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (N : Set Ω)
      (E : Set (Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0))
      (hι : Measurable fun ω => (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω)),
      (∀ ω, IsTranslateAddConst 0 (θ₀ * chiC κ) (h ω) (h' ω)) ∧
      IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ₀)
        (flowLineRhoR κ b J 0 θ₀) P 𝓕 W VL VR B ζ h' ∧
      P N = 0 ∧ coarseSigma h' W VL VR ζ N ≤ mΩ ∧
      MeasurableSet E ∧ (∀ p ∈ E, IsGood47 W VL VR ζ p) ∧
      (∀ p ∈ E, qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E p = ⊤) ∧
      (∀ᵐ ω ∂P, (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω) ∈ E) ∧
      IsChartCanon (16 / κ) (iwLT κ θ₀ (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) (flowLineXL b J 0)
          (flowLineXR b J 0))
        (iwRT κ θ₀ (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) (flowLineXL b J 0) (flowLineXR b J 0)) P
        (Coupling.filtrationComap (qRaw (Ω := Coarse (coarseSigma h' W VL VR ζ N))
          (qxLT κ θ₀ (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) (flowLineXL b J 0) (flowLineXR b J 0))
          (qxRT κ θ₀ (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) (flowLineXL b J 0) (flowLineXR b J 0))
          W VL VR ζ s E) hι)
        (fun t ω => qW (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E t
          (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω))
        (fun i t ω => qVL (Ω := Coarse (coarseSigma h' W VL VR ζ N))
          (qxLT κ θ₀ (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) (flowLineXL b J 0) (flowLineXR b J 0))
          W VL VR ζ s E i t (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω))
        (fun j t ω => qVR (Ω := Coarse (coarseSigma h' W VL VR ζ N))
          (qxRT κ θ₀ (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) (flowLineXL b J 0) (flowLineXR b J 0))
          W VL VR ζ s E j t (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω))
        (fun ω => (qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E
          (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω) : ℝ≥0∞))
        (fun ω => fChart (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s
          (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω))
        (-((π - θ₀) * chiC κ)) (-chiC κ) (fun ω => -h' ω) := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hD
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  have h44 := Sec7.R7Outer.cond44_of_heights hκ hb hθ
  have hθb := RestartGen.cfThetaBounds_of_heights hκ hκ4 hb hπ θ₀
  have hXe : (fun ω => cfFieldT κ θ₀ (h' ω)) = h := funext fun ω => by
    rw [Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)]
    exact RestartGen.cfFieldT_flowField κ θ₀ (h ω)
  have hcf' : IsCenteredCounterflowDriver κ P (fun ω => cfFieldT κ θ₀ (h' ω)) W' ζ' := by rw [hXe]; exact hcf
  have hY := measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  have hXm : Measurable fun ω => cfFieldT κ θ₀ (h' ω) := (measurable_cfFieldT κ θ₀).comp hC.2.1
  set k := condDistrib (cfHistory W' ζ') (fun ω => cfFieldT κ θ₀ (h' ω)) P with hkdef
  have hk : P.map (fun ω => (cfFieldT κ θ₀ (h' ω), cfHistory W' ζ' ω)) =
      P.map (fun ω => cfFieldT κ θ₀ (h' ω)) ⊗ₘ k :=
    (compProd_map_condDistrib hXm.aemeasurable hY.aemeasurable).symm
  -- the null set and the coarse σ-algebra
  set N := toMeasurable P {ω | ¬ IsGoodFlow47 W VL VR ζ ω} with hNdef
  have hN0 : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 (ae_isGoodFlow47 hκ hκ4 hF h44 hC)
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hX := hC.2.2.2.1
  have hm : coarseSigma h' W VL VR ζ N ≤ mΩ := coarseSigma_le hC.2.1 hX hNm
  obtain ⟨Ψ, hΨm, hΨ⟩ :=
    Sec7.Lemma71H.hasFieldDeterminedHistories_of_cond44 href hκ hκ4 hF h44 P 𝓕 W VL VR B ζ h' hC
  have hinv : ∀ f : DistOn upperHalfPlaneOpens,
      Exist.flowField 0 (θ₀ * chiC κ) (cfFieldT κ θ₀ f) = f := fun f => by
    rw [cfFieldT, GlueCond.flowField_zero_flowField_zero, add_neg_cancel, GlueCond.flowField_zero_zero]
  have hmX : coarseSigma h' W VL VR ζ N ≤ fieldNullSigma P (fun ω => cfFieldT κ θ₀ (h' ω)) := by
    refine coarseSigma_le_fieldNullSigma (g := Exist.flowField 0 (θ₀ * chiC κ)) (Exist.measurable_flowField _ _)
      (Eventually.of_forall fun ω => (hinv (h' ω)).symm) hN0
      (Ψ := fun x => Ψ (Exist.flowField 0 (θ₀ * chiC κ) x)) (hΨm.comp (Exist.measurable_flowField _ _)) ?_
    filter_upwards [hΨ] with ω hω
    simp only [hinv]
    exact hω
  have hXmc : @IsMeasurableKilledDriving Ω (coarseSigma h' W VL VR ζ N) _ _ W VL VR ζ :=
    isMeasurableKilledDriving_coarse
  have hhm : Measurable[coarseSigma h' W VL VR ζ N] h' := measurable_field_coarse
  -- the good set
  set E₀ : Set (Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0) :=
    {p | p.1 ∉ N ∧ p.2 ∈ goodHitSet ∧ p.2 ∈ Prop49Exit.nrSet} with hE₀def
  have hNc : MeasurableSet[coarseSigma h' W VL VR ζ N] N := measurableSet_null_coarse
  have hE₀ : MeasurableSet E₀ :=
    (measurable_fst (show MeasurableSet (show Set (Coarse (coarseSigma h' W VL VR ζ N)) from N) from hNc).compl).inter
      ((measurable_snd measurableSet_goodHitSet).inter (measurable_snd Prop49Exit.measurableSet_nrSet))
  have hE₀g : ∀ p ∈ E₀, IsGood47 W VL VR ζ p := fun p hp =>
    isGood47_of_flow (by_contra fun hn => hp.1
      (subset_toMeasurable (μ := P) (s := {ω : Ω | ¬ IsGoodFlow47 W VL VR ζ ω}) hn)) hp.2.1 hp.2.2
  have hNR := CfNoReturn.Route.counterflowNoReturnAdmStatement_of_partA_of_clearance.{u} hA
  have hE₀ae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ₀ (h' ω)) ((measurable_cfFieldT κ θ₀).comp hC.2.1)),
      p ∈ E₀ := by
    have h1 : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ₀ (h' ω)) hXm), p.1 ∉ N :=
      ae_glue_fst (μ := P) k hXm (measure_eq_zero_iff_ae_notMem.1 hN0)
    have h2 := cfGlueAE_mem_goodHitSetT θ₀ κ hκ hκ4 _ _ _ _ hF h44 hθb P 𝓕 W VL VR B ζ h' hC P
      (fun ω => cfFieldT κ θ₀ (h' ω)) W' ζ' hcf' rfl k hk
    have h3 : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ₀ (h' ω)) hXm), p.2 ∈ Prop49Exit.nrSet :=
      ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf') hY rfl k hk Prop49Exit.measurableSet_nrSet
        (Lemma47Angle.ae_cfHistory_mem_nrSet_angle hNR hκ hκ4 hθb hC hcf' rfl)
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
    exact ⟨hp1, hp2, hp3⟩
  -- the good set on which the killing time is infinite
  set E : Set (Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0) :=
    E₀ ∩ {z | qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E₀ z = ⊤} with hEdef
  have hqTm : MeasurableSet {z : Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0 |
      qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E₀ z = ⊤} := by
    have e : {z : Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0 |
        qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E₀ z = ⊤} =
        ⋂ n : ℕ, {z | ((n : ℝ≥0) : WithTop ℝ≥0) < qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E₀ z} := by
      ext z
      simp only [mem_iInter]
      exact eq_top_iff_forall_nat_lt
    rw [e]
    exact MeasurableSet.iInter fun n => measurableSet_lt_qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) hXmc hE₀ hE₀g n
  have hE : MeasurableSet E := hE₀.inter hqTm
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := fun p hp => hE₀g p hp.1
  have hEtop : ∀ p ∈ E, qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E p = ⊤ := fun p hp =>
    (qT_congr_of_mem (Ω := Coarse (coarseSigma h' W VL VR ζ N)) (W := W) (VL := VL) (VR := VR) (ζ := ζ)
      (s := s) hp hp.1).trans hp.2
  have hEae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ₀ (h' ω)) ((measurable_cfFieldT κ θ₀).comp hC.2.1)),
      p ∈ E := by
    filter_upwards [hE₀ae, ae_qT_eq_top hθ₀.1 hθ₀.2 hA hκ hκ4 hF h44 hθb hC hcf' rfl k hk E₀ hE₀ae hs]
      with p h1 h2
    exact ⟨h1, h2⟩
  -- the sample of the given space is in the good set almost surely
  have hι : Measurable fun ω => (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω) :=
    (measurable_toCoarse hm).prodMk hY
  have hlaw := map_glue_coarse_eq hXm hY k hk hm hmX
  have hιE : ∀ᵐ ω ∂P, (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω) ∈ E := by
    have hg₁ : Measurable fun p : Ω × HistorySpace 0 0 => (toCoarse (coarseSigma h' W VL VR ζ N) p.1, p.2) :=
      ((measurable_toCoarse hm).comp measurable_fst).prodMk measurable_snd
    have h1 : ∀ᵐ z ∂((glueMeasure P k (fun ω => cfFieldT κ θ₀ (h' ω)) hXm).map
        fun p => (toCoarse (coarseSigma h' W VL VR ζ N) p.1, p.2)), z ∈ E := (ae_map_iff hg₁.aemeasurable hE).2 hEae
    rw [hlaw] at h1
    exact (ae_map_iff hι.aemeasurable hE).1 h1
  exact ⟨h', 𝓕, VL, VR, B, N, E, hι, htr, hC, hN0, hm, hE, hEg, hEtop, hιE,
    isChartCanon_coarse hκ hκ4 hF h44 hθb hC hcf' k hk hY hm hmX hXmc hhm E hE hEg hEae hs⟩


end Main

end InteractingSLE.Sec5.QSched
