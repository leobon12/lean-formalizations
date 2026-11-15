/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeMarg
import InteractingSLE.Spec.Sec7.HOuterWire
import InteractingSLE.Spec.Sec7.OuterGeomExt

/-!
# The intermediate mixed pocket of R.6's two-outer-arm case: configuration, versions and tests

PROVE-R6-SAFE. For two outer arms (`k/2 − 4 < r_L`, `k/2 − 4 < r_R`) the R.6 certificate of an outer pocket `C` of
`(α_R, α_L)` uses the mixed pocket `V ⊂ C` of `(α_R, β_L)` (supplement p. 476, "Application to two outer arms").
This file provides `V`'s side of the wiring:

* `V`'s R.7 configuration is the landed `OuterGeom.isR7OuterConfig_leftExt` (weights `(r_L, d)`, margins
  `(c + (θ_L − π/2)χ, c')`, arms `α_R, β_R, β_L, β_L`); its versions `isR7Versions_leftExt` use a frontier version
  `M_L` of `β_L` as the left wall;
* the named margin-general outer pocket geometry `OuterGeomAeMRemaining` (the `geom`/`geomInf` fields of
  `HOuter.R7OuterInputs` on every R.7 configuration at arbitrary margins; at the margins `(πχ(16/k), 0)` this is the
  landed chain `OuterGeom.outerGeomInputs_of_rest` + `OuterIn.ae_outerGeom(Inf)`);
* **`exists_outerCfgEvent`**: from it, on every outer R.7 configuration and every positive rational change parameter
  `s`, a walls-measurable event on which the outer pocket configuration (`IsOuterCfg` / `IsOuterCfgInf`) holds **at
  every sample**, containing almost every sample whose left wall at `rt s` is off the right wall (the outer analogue
  of `R6Fin.exists_cfgEvent_extremal`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open WholeField R7Outer R7Leaves R6Nest R6Rel HOuter WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks
  PocketWordAssembly PocketSeedOpen PocketStopField PocketStopWallsFin PocketStopWalls PocketCoupling
  StripPocketConfig PocketWordPerQ PocketStop R7StopIn

/-- **Named: the outer pocket geometry at arbitrary margins** — the `geom` and `geomInf` fields of
`HOuter.R7OuterInputs` (the erasure facts and the relative Loewner conclusion of `HOuter.OuterGeom(Inf)`, almost
surely on the change configuration at every positive rational change parameter) on every R.7 configuration with margins
`(c, c')`, every decomposition of its centred counterflow and every choice of versions. At `(πχ(16/k), 0)` this is
proved by the landed chain `OuterGeom.outerGeomInputs_of_rest` → `OuterIn.ae_outerGeom`, `OuterIn.ae_outerGeomInf`,
whose proofs do not use the values of the margins. -/
def OuterGeomAeMRemaining (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ q : ℚ, 0 < q →
      (∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        OuterGeom (R ω) (L ω) (StripSys.rt q) (η ω)) ∧
      ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        OuterGeomInf (R ω) (L ω) (StripSys.rt q) (η ω)

section Versions

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The versions of the intermediate mixed pocket's arms**: the right wall `R` of the original configuration and a
frontier version `M_L` of `β_L` as the left wall. -/
theorem isR7Versions_leftExt {W' : ℝ≥0 → Ω → ℝ} {αR αL βL R L ML : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hV : IsR7Versions P W' αR αL R L η) (hML : IsFrontierVersion P βL ML) :
    IsR7Versions P W' αR βL R ML η :=
  ⟨hV.R_cont, hV.R_zero, hV.R_meas, hV.R_ae, hML.1, hML.2.1, hML.2.2.1, hML.2.2.2, hV.η_cont, hV.η_zero, hV.η_meas,
    hV.η_trace⟩

end Versions

section Event

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **The outer pocket configuration at every sample of a walls' event** (one positive rational change parameter
`s`): on an outer R.7 configuration (`k/2 − 4 < max(r_L, r_R)`) with versions `R`, `L`, `η`, given the almost sure
outer pocket geometry at `rt s` (`HOuter.OuterGeom(Inf)`), there is a walls-measurable event `F` on which the change
configuration, the infinite lifetime and the outer pocket configuration (both shapes) hold, and which contains almost
every sample whose left wall at `rt s` is off the right wall. -/
theorem exists_outerCfgEvent (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : Sec4.Aux7Statement.{u} k)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 < max rL rR) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) (s : ℚ) (hs : 0 < s)
    (hgeo : ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt s) →
      0 < rightLo (R ω) (L ω) (StripSys.rt s) → OuterGeom (R ω) (L ω) (StripSys.rt s) (η ω))
    (hgeoI : ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt s) →
      rightLo (R ω) (L ω) (StripSys.rt s) = 0 → OuterGeomInf (R ω) (L ω) (StripSys.rt s) (η ω)) :
    ∃ F : Set Ω, MeasurableSet[wallsSigma P R L] F ∧
      (∀ᵐ ω ∂P, L ω (StripSys.rt s) ∉ range (R ω) → ω ∈ F) ∧
      ∀ ω ∈ F, IsChangeConfigInc (R ω) (L ω) (StripSys.rt s) ∧ ζ' ω = ⊤ ∧
        (0 < rightLo (R ω) (L ω) (StripSys.rt s) →
          IsOuterCfg (R ω) (L ω) (StripSys.rt s) (fun t : ℝ => W' t.toNNReal ω) (η ω)) ∧
        (rightLo (R ω) (L ω) (StripSys.rt s) = 0 →
          IsOuterCfgInf (R ω) (L ω) (StripSys.rt s) (fun t : ℝ => W' t.toNNReal ω) (η ω)) := by
  classical
  have hgff := hcfg.gff
  have hreg := hcfg.regular
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg, hV.R_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.1
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg, hV.L_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.2.2.2.1
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hpair := R7StopIn.ae_pair_r7 h55 hk4 hc hc' (R7.thetaR_lt_thetaL hk4 hL hR hmax.le)
    (thetaR_mem_r7 rR hk4 hL) (thetaL_mem_r7 rL hk4 hR) hgff hcfg.flow_αR hcfg.flow_αL hΦαR hΦαL
    (fun ω => (hΦ ω).1) (fun ω => (hΦ ω).2.2.2)
    (hreg.mono fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.2.2⟩)
  have hRL : ∀ᵐ ω ∂P, range (L ω) ⊆ closedLeftSide (R ω) := by
    filter_upwards [hpair, hV.R_ae, hV.L_ae] with ω hω hRe hLe
    rw [hRe, hLe]; exact hω.1
  have hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))) := by
    filter_upwards [hRL, hRs, hLs] with ω hω hRω hLω
    exact Lemma71Q.disjoint_range_leftSideOf_of_subset_closedLeftSide hLω hRω hω
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hgff hcfg.counterflow hV.η_trace
  have htrans := ae_transient_counterflow_r7 haux7 hk4 hc hc' hgff hcfg.counterflow hV.η_trace
  obtain ⟨G₀, hG₀m, hG₀ae, hG₀⟩ := exists_measurableSet_nullSets_ae (P := P)
    (hRs.and (hLs.and (hRL.and (hord.and (hζ.and (htrace.and (htrans.and (hgeo.and hgeoI))))))))
  have hG₀m' : MeasurableSet[wallsSigma P R L] G₀ := le_sup_right (a := MeasurableSpace.comap
    (fullHist ![R, L]) inferInstance) _ hG₀m
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  set F : Set Ω := G₀ ∩ {ω | L ω (StripSys.rt s) ∉ closure (range (R ω))} with hFdef
  have hFm : MeasurableSet[wallsSigma P R L] F :=
    StripSys.measurableSet_inter_notMem_closure_range (mΩ := wallsSigma P R L) hG₀m' (fun ω _ => hV.R_cont ω)
      (fun q' => hRm' _) (hLm' _)
  refine ⟨F, hFm, ?_, fun ω hω => ?_⟩
  · filter_upwards [hG₀ae] with ω hω hoff
    refine ⟨hω, ?_⟩
    show L ω (StripSys.rt s) ∉ closure (range (R ω))
    rwa [(Lemma71Pin.IsSimpleProper.isClosed_range (hG₀ ω hω).1).closure_eq]
  obtain ⟨hRω, hLω, hRLω, hordω, hζω, ⟨htr, hWc, hW0⟩, htrω, hgω, hgIω⟩ := hG₀ ω hω.1
  have hoff : L ω (StripSys.rt s) ∉ range (R ω) := fun h' => hω.2 (subset_closure h')
  have hpos' : 0 < StripSys.rt s := Real.toNNReal_pos.2 (Rat.cast_pos.2 hs)
  have hinc : IsChangeConfigInc (R ω) (L ω) (StripSys.rt s) :=
    (isChangeConfig_of_closedLeftSide hRω hLω hRLω hpos' hoff).isChangeConfigInc
  have hW0' : W' (Real.toNNReal 0) ω = 0 := by rw [Real.toNNReal_zero]; exact hW0
  refine ⟨hinc, hζω, fun hp => ?_, fun h0 => ?_⟩
  · obtain ⟨he, hl⟩ := hgω hinc hp
    exact ⟨hinc, hp, hinc.isFlowChartOriented_of_leftFrontier hinc.left rfl hordω, htr, hWc, hW0', he, hl⟩
  · obtain ⟨he, hl⟩ := hgIω hinc h0
    exact ⟨hinc, h0, hinc.isFlowChartOriented_of_leftFrontier hinc.left rfl hordω, htr, hWc, hW0', htrω, he, hl⟩

end Event

end InteractingSLE.Sec7.R6Safe
