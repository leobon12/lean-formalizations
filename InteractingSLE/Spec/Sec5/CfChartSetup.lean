/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfChartLife

/-!
# Lemma 4.7's chart clause on the given space: the setting of `CfGivenChartStatement`

Packet PROVE-CFCHART. From the binders of `CfGiven.CfGivenChartStatement` (a strip field `h` with a centred
counterflow `W′` and an angle-`θ₀` flow-line driver `W` of `h`, at a positive own time `s`) this file builds the
transfer data of `isChartCanon_coarse` and concludes the chart coupling clause of the counterflow's image word on the
given space `Ω`:

* the flow coupling of the driver (field `h′ = h + θ₀χ`), (4.4) at `θ₀` and the admissibility bounds at `π/2` from the
  heights;
* the conditional law `k` of the counterflow history given the field;
* the coarse σ-algebra `coarseSigma h′ W VL VR ζ N` (`N` a null set off which the flow path is good), which consists
  of events of the field up to null sets by the §4.2 reference (`Lemma71H.hasFieldDeterminedHistories_of_cond44`);
* the good set `E = {N-good flow} × (goodHitSet ∩ nrSet)` intersected with `{qT = ∞}`: on it the killing time is
  infinite at **every** sample.

## Main results

* `IsGoodFlow47`, `ae_isGoodFlow47` (the flow half of `IsGood47`, almost surely);
* `isHeightBounded44_of_strip` (the heights at every angle of `[−π/2, π/2]`);
* **`exists_chartCanon_omega`**: the chart clause on `Ω`, with the good set, the killing time infinite on it and the
  sample `ω ↦ (ω, cfHistory W′ ζ′ ω)` in it almost surely.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfChart

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q CrossCond.Theta
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Lemma47Angle CfGiven
open Sec7.StripHeights44 (IsHeightBounded44)

/-! ### The flow half of a good glued sample -/

section Flow

variable {Ω : Type*} {nL nR : ℕ}

/-- The flow half of `IsGood47`: a good path with a generating trace in `ℍ` at positive times (the seed line). -/
def IsGoodFlow47 (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (ω : Ω) : Prop :=
  Aux50Hit.IsGoodPath W VL VR ζ ω ∧
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ (∀ t : ℝ≥0, 0 < t → η t ∈ H) ∧
      seedLine ζ W ω = fun s : ℝ => η s.toNNReal

theorem isGood47_of_flow {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {p : Ω × HistorySpace 0 0} (hf : IsGoodFlow47 W VL VR ζ p.1) (hy : p.2 ∈ goodHitSet)
    (hnr : p.2 ∈ Prop49Exit.nrSet) : IsGood47 W VL VR ζ p :=
  ⟨hf.1, hf.2, hy, fun _ hu => Prop49Exit.histLine_ne_zero_of_mem_nrSet hnr hu⟩

theorem ae_isGoodFlow47 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∀ᵐ ω ∂P, IsGoodFlow47 W VL VR ζ ω := by
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hline] with ω hω using hω.1
  filter_upwards [hline, Aux50Hit.ae_isGoodPath hC.1 hζ] with ω ⟨_, ⟨η, hη, he⟩, hP⟩ hg
  refine ⟨hg, η, hη, fun t ht => ?_, he⟩
  have h1 := hP.mem_H t ht
  rw [he] at h1
  simpa only [Real.toNNReal_coe] using h1

end Flow

/-! ### Heights -/

/-- The strip heights at every angle of `[−π/2, π/2]` give (4.4) at each such angle. -/
theorem isHeightBounded44_of_strip {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {a : ℝ} (ha : a ∈ Icc (-(π / 2)) (π / 2)) : IsHeightBounded44 κ b J a := by
  have hχ := Sec4.chiC_pos hκ hκ4
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => hright a ha y hy hyJ⟩
  have := hleft a ha y hy hyJ
  have : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  linarith

/-! ### The clause on the given space -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {θ₀ : ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- `x = ∞` in `WithTop ℝ≥0` iff every natural number is below it. -/
theorem eq_top_iff_forall_nat_lt {x : WithTop ℝ≥0} : x = ⊤ ↔ ∀ n : ℕ, ((n : ℝ≥0) : WithTop ℝ≥0) < x := by
  refine ⟨fun hx n => hx ▸ WithTop.coe_lt_top _, fun hx => ?_⟩
  induction x with
  | top => rfl
  | coe r =>
    obtain ⟨n, hn⟩ := exists_nat_gt r
    exact absurd (WithTop.coe_lt_coe.1 (hx n)) (not_lt.2 hn.le)

/-- **Lemma 4.7's chart clause on the given space** (setting of `CfGivenChartStatement`, own time `s > 0`). The flow
coupling of the driver `W` (field `h′ = h + θ₀χ`), a coarse σ-algebra `m` of `Ω` and a coarse-measurable good set
`E` with: the killing time of the counterflow's image word infinite on `E`, the sample `(ω, cfHistory W′ ζ′ ω)` in `E`
almost surely, and the chart coupling clause of the field `−h′` (constants `−(π − θ₀)χ`, `−χ`) on `Ω` for the
pulled-back raw image filtration. -/
theorem exists_chartCanon_omega (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
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
  have hθ := isHeightBounded44_of_strip hκ hκ4 hleft hright hθ₀
  have hπ := isHeightBounded44_of_strip hκ hκ4 hleft hright
    (show π / 2 ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith [Real.pi_pos], le_rfl⟩)
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

end InteractingSLE.Sec5.CfChart
