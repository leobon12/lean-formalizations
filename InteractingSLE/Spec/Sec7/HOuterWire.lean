/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HOuterStop
import InteractingSLE.Spec.Sec7.HOuterMarkedInf
import InteractingSLE.Spec.Sec7.StripSafeWire

/-!
# Theorem R.7's outer pockets on the R.7 field: `hOuter` from the remaining named inputs

Packet PROVE-HOUTER. Theorem 1.2's late wiring (`StripSafe.r7ReferenceStatement_late_sideDet_safe`) takes the
outer-pocket completion `hOuter : ∀ … κ/2 − 4 < max r_L r_R → RefWire.OuterPocketCompletion κ r_L r_R`, the whole
mixed/outer pocket construction of Theorem R.7 (supplement §5, `source/spec/p433-480.md` L925–L1068). Here it is
reduced to the outer pocket's genuinely open source steps, everything else being proved on the R.7 configuration
(`R7Outer.IsR7OuterConfig`, PROVE-R7-OUTER):

* the walls are versions of the incoming arms `α_R`, `α_L` (`R7Leaves.IsR7Versions`, as for the extremal pockets), the
  counterflow's trace is a version of its generating trace;
* proved here from the configuration: the coupling decomposition of the centred counterflow, the centred GFF, the
  infinite lifetime, the walls' simplicity, field determination, entrance-history locality, order and distinct ranges
  (Proposition 5.5, Lemma 6.13 through `R7StopIn.ae_pair_r7`), the counterflow's Loewner trace and transience (Aux. 7),
  the selection of the pocket from the walls alone (`R7StopIn.exists_r7StopInEvent`), the flow-chart orientation, the
  measurable Jordan coordinates, the traversal's measurability, the measurable erasure, the hull sets and the union law
  of the relative complement (`HOuterStop`, `HOuterUnion`), **the walls' marked union law at the ambient stop `T⁰(q)`**
  (Aux. lemma 35; the marked stop of the outer pocket, `HOuterMarkedStop`, `HOuterMarkedInf`), the walls record and the
  transience `GoodR7`;
* **remaining named inputs** (`R7OuterInputs`): per realization, the erasure facts and the relative Loewner conclusion
  of the selected pocket (`OuterGeom`, `OuterGeomInf`: §5.3–§5.4, the outputs of PROVE-R7-STOPIN's
  `isErasurePocket_*` and PROVE-R7-GAPEQ's `relLoewner_*` once their named geometric inputs are supplied); the two-seed
  side limits (Lemmas R.5–R.6, the same `TwoSeedSideInput(Inf)` form as the extremal `hsd.side`); Proposition 5.13 for
  the counterflow (the same proposition as the extremal `hsd.det`).

## Main results

* `OuterGeom`, `OuterGeomInf`, `OuterWallsLaw`, `OuterWallsLawInf` (proved inside), `R7OuterInputs`, `R7OuterRemaining`;
* **`r7PocketStop_outer_of_config`**: `R7PocketStopStatement k r_L r_R GoodR7` on one outer configuration;
* **`outerPocketCompletion_of_remaining`**: `RefWire.OuterPocketCompletion k r_L r_R` from `R7OuterRemaining`;
* **`r7ReferenceStatement_late_sideDet_outer`**: the drop-in for `StripSafe.r7ReferenceStatement_late_sideDet_safe`
  with `hOuter` replaced by `R7OuterRemaining` on the outer range.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses; the named statements used are
Propositions 4.11 and 5.1 in chart `Q` and Aux. 7 (all on R48's list of Theorem 1.2 inputs).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open LQGMetric (DistOn IsZeroBoundaryGFF)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.HOuter

open R7Outer WangWu WholeField Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly
  PocketSeedOpen PocketStopField PocketStopWallsFin PocketStopWalls PocketCoupling PocketWordPerQ PocketStop R7Aux131
  R7Pocket RefWire R7Leaves R7StopIn

/-! ### The remaining inputs -/

section Inputs

/-- **The pocket geometry of one bounded realization** (§5.3–§5.4): the erasure facts of the change pocket between
the first visits of `m(y₀)` and `m(x₀)` and the relative Loewner conclusion in every Jordan coordinate. -/
def OuterGeom (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) : Prop :=
  IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) ∧
    ∀ ψ : ℂ → ℂ, IsCfJordan R L r ψ →
      RelLoewner (fun v => ψ (Sec6.erasedPath η (cfPocket R L r) (firstHit η (cfArcR R L r 1))
        (firstHit η (cfArcR R L r 0)) v))
        (Sec6.pocketClock η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
          (firstHit η (cfArcR R L r 0)))

/-- **The pocket geometry of one realization opening at the flow seed**: the erasure facts at infinity and the
relative Loewner conclusion in every Jordan coordinate at infinity. -/
def OuterGeomInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) : Prop :=
  IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0) (firstHit η (cfArcRInf R L r 0)) ∧
    ∀ ψ : ℂ → ℂ, IsCfJordanInf R L r ψ →
      RelLoewner (fun v => ψ (Sec6.erasedPathInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) v))
        (Sec6.clockEnd η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)))

variable {Ω : Type*}

/-- **The walls' marked union law at the ambient stop `T⁰(q)` of a bounded outer pocket on the event `G`** (Aux. lemma
35's marked stopping-time union law for `m(walls) ∪ R_{T⁰(q)}` with the relative history as marks): for every walls'
sub-event and every point-measurable Jordan coordinate. Proved on R.7 configurations in `r7PocketStop_outer_of_config`
(`PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0_marked`). -/
def OuterWallsLaw (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
    @IsPointMeasurable Ω 𝓦 R L r G ψ → ∀ q : ℝ≥0,
      PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
        (stopHull0 R L r W η ψ q) h₀ q

/-- **The walls' marked union law at the ambient stop `T⁰(q)` of an outer pocket opening at the flow seed.** -/
def OuterWallsLawInf (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ)
    (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
    @IsPointMeasurableInf Ω 𝓦 R L r G ψ → ∀ q : ℝ≥0,
      PocketStopWallsLaw 𝓦 P A (travAllInf R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
        (stopHull0Inf R L r W η ψ q) h₀ q

variable [mΩ : MeasurableSpace Ω]

/-- **The remaining inputs of Theorem R.7's mixed and outer pockets** on versions `R`, `L` of the walls `α_R`, `α_L` and
`η` of the counterflow's trace:
* `geom`, `geomInf` — at rational change times, almost surely on the change configuration, the pocket geometry
  (`OuterGeom`, `OuterGeomInf`; §5.3–§5.4);
* `side` — the two-seed side limits on such events (Lemmas R.5–R.6, the form `RefWire.TwoSeedSideInput(Inf)`);
* `det` — Proposition 5.13 for the counterflow: almost surely its trace is a Borel function of the field `h″`. -/
structure R7OuterInputs (k rL rR : ℝ) (P : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (h'' : Ω → DistOn upperHalfPlaneOpens) (u₀' : ℂ → ℝ) (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ) : Prop where
  geom : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
    0 < rightLo (R ω) (L ω) (StripSys.rt q) → OuterGeom (R ω) (L ω) (StripSys.rt q) (η ω)
  geomInf : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
    rightLo (R ω) (L ω) (StripSys.rt q) = 0 → OuterGeomInf (R ω) (L ω) (StripSys.rt q) (η ω)
  side : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
    (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
    (∀ ω ∈ G, ζ' ω = ⊤) →
    (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
    (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
    TwoSeedSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
        {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
      TwoSeedSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
        {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'
  det : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h'' inferInstance]
    fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t

end Inputs

/-! ### The outer pocket on one configuration -/

section Config

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **Theorem R.7's mixed or outer pocket on one R.7 configuration** (`max(r_L, r_R) > k/2 − 4`): on an
`IsR7OuterConfig` with walls `R`, `L` versions of the arms `α_R`, `α_L` and `η` a version of the counterflow's trace,
`R7PocketStopStatement k r_L r_R GoodR7` follows from `R7OuterInputs` alone. The pocket is selected from the walls
(`exists_r7StopInEvent`), and every other source fact of the stop-level statement is proved (see the module
docstring). -/
theorem r7PocketStop_outer_of_config (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : Sec4.Aux7Statement.{u} k)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 < max rL rR) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η)
    (hin : R7OuterInputs k rL rR P W' ζ' h'' u₀' R L η) :
    R7PocketStopStatement.{u} k rL rR GoodR7 := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hk0 : 0 < k := by linarith
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hreg := hcfg.regular
  -- the walls: field determination and entrance-history locality
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR
    (hreg.mono fun ω hω => hω.2.2.2.2.1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL
    (hreg.mono fun ω hω => hω.2.2.2.2.2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae
  -- the walls: simplicity, order, distinct ranges (Proposition 5.5, Lemma 6.13)
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
  have hnc : ∀ᵐ ω ∂P, ∃ t, L ω t ∉ range (R ω) := by
    filter_upwards [hpair, hV.R_ae, hV.L_ae] with ω hω hRe hLe
    obtain ⟨t, -, -, ht⟩ := hω.2.2 1 2 one_pos one_lt_two
    exact ⟨t, by rw [hRe, hLe]; exact ht⟩
  have hRL : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsSimpleProper (L ω) ∧ range (L ω) ⊆ closedLeftSide (R ω) := by
    filter_upwards [hpair, hRs, hLs, hV.R_ae, hV.L_ae] with ω hω hRω hLω hRe hLe
    refine ⟨hRω, hLω, ?_⟩
    rw [hRe, hLe]; exact hω.1
  have hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))) := by
    filter_upwards [hRL] with ω hω
    exact Lemma71Q.disjoint_range_leftSideOf_of_subset_closedLeftSide hω.2.1 hω.1 hω.2.2
  -- the counterflow
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hgff hcfg.counterflow hV.η_trace
  have htrans := ae_transient_counterflow_r7 haux7 hk4 hc hc' hgff hcfg.counterflow hV.η_trace
  -- the walls' σ-algebra and the selection of the pocket from the walls
  have : StandardBorelSpace (ULift.{u} (Fin 2 → Sec6.Hist)) :=
    LQGMetric.standardBorelSpace_of_measurableEquiv MeasurableEquiv.ulift
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hWeq : wallsSigma P R L ⊔ Ito.nullSets P = wallsSigma P R L := sup_eq_left.2 le_sup_right
  obtain ⟨q, hq, G, hGm, hPG, hG⟩ := exists_r7StopInEvent (𝓦 := wallsSigma P R L) (P := P) hRm' hLm' hRL hnc
    (Q := fun q ω => (IsLoewnerTrace (fun s : ℝ => W' s.toNNReal ω) (η ω) ∧
        Continuous (fun s : ℝ => W' s.toNNReal ω) ∧ W' 0 ω = 0) ∧
      Disjoint (range (R ω)) (leftSideOf (range (L ω))) ∧ Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ ζ' ω = ⊤ ∧
      (IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        OuterGeom (R ω) (L ω) (StripSys.rt q) (η ω)) ∧
      (IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        OuterGeomInf (R ω) (L ω) (StripSys.rt q) (η ω)))
    (fun q hq => by
      filter_upwards [htrace, hord, htrans, hζ, hin.geom q hq, hin.geomInf q hq] with ω h1 h2 h3 h4 h5 h6
      exact ⟨h1, h2, h3, h4, h5, h6⟩)
  rw [hWeq] at hGm
  have hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) := fun ω hω =>
    (hG ω hω).1.isChangeConfigInc
  have hcfgB : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := fun ω hω hpos => by
    obtain ⟨-, ⟨htr, hWc, hW0⟩, hordω, -, -, hgeo, -⟩ := hG ω hω
    have hinc := hconf ω hω
    obtain ⟨he, hl⟩ := hgeo hinc hpos
    exact ⟨hinc, hpos, hinc.isFlowChartOriented_of_leftFrontier hinc.left rfl hordω, htr, hWc,
      by simpa only [Real.toNNReal_zero] using hW0, he, hl⟩
  have hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := fun ω hω h0 => by
    obtain ⟨-, ⟨htr, hWc, hW0⟩, hordω, htr', -, -, hgeo⟩ := hG ω hω
    have hinc := hconf ω hω
    obtain ⟨he, hl⟩ := hgeo hinc h0
    exact ⟨hinc, h0, hinc.isFlowChartOriented_of_leftFrontier hinc.left rfl hordω, htr, hWc,
      by simpa only [Real.toNNReal_zero] using hW0, htr', he, hl⟩
  have hζG : ∀ ω ∈ G, ζ' ω = ⊤ := fun ω hω => (hG ω hω).2.2.2.2.1
  -- the field-level inputs on the two shapes
  set Gp := {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} with hGpdef
  set G0 := {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} with hG0def
  have hGpm : MeasurableSet[wallsSigma P R L] Gp :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0m : MeasurableSet[wallsSigma P R L] G0 := by
    convert hGm.diff hGpm using 1
    ext ω
    simp only [hGpdef, hG0def, mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hseed : ∀ ω ∈ G0, rightLo (R ω) (L ω) (StripSys.rt q) = 0 := fun ω hω =>
    le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1)
  obtain ⟨hs, hsI⟩ := hin.side q hq G hGm hPG hconf hζG hcfgB hcfgI
  -- the walls' marked union law at `T⁰(q)` (Aux. lemma 35, the marked stop of the outer pocket)
  have h𝓦d := wallsSigma_le_drivingFiltration (P := P) hX R L
  have hw : OuterWallsLaw (wallsSigma P R L) P R L (StripSys.rt q) (fun ω (s : ℝ) => W' s.toNNReal ω) η Gp
      (centredField h'' u₀') := fun A hA hAG ψ hψ hψm q' =>
    PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0_marked hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hV.R_cont
      hV.L_cont hV.R_zero hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL h𝓦d hRm' hLm' hGpm
      (fun ω hω => hconf ω hω.1) hA hAG (fun ω hω => hcfgB ω (hAG hω).1 (hAG hω).2)
      (fun ω hω => hζG ω (hAG hω).1) hψ hψm q'
  have hwI : OuterWallsLawInf (wallsSigma P R L) P R L (StripSys.rt q) (fun ω (s : ℝ) => W' s.toNNReal ω) η G0
      (centredField h'' u₀') := fun A hA hAG ψ hψ hψm q' =>
    PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0Inf_marked hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hV.R_cont
      hV.L_cont hV.R_zero hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL h𝓦d hRm' hLm' hG0m
      (fun ω hω => hconf ω hω.1) hA hAG (fun ω hω => hcfgI ω (hAG hω).1 (hseed ω (hAG hω)))
      (fun ω hω => hζG ω (hAG hω).1) hψ hψm q'
  have hfun : (fun ω => centredField h'' u₀' ω + smoothDist upperHalfPlaneOpens u₀') = h'' :=
    funext fun ω => by simp only [centredField, sub_add_cancel]
  have h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField h'' u₀' ω + smoothDist upperHalfPlaneOpens u₀') inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t := by
    rw [hfun]; exact hin.det
  refine r7PocketStop_of_outerConfig (𝓦 := wallsSigma P R L) (wallsSigma_le hV.R_meas hV.L_meas) hRm' hLm' hGm
    hPG hconf hcfgB hcfgI hV.η_cont hV.η_meas (isZeroBoundaryGFF_centredField hC hu₀') hu₀'.1 hu₀'.2.1 ?_ ?_
    (measurable_wallRecord R L) (wallsSigma_le_wallRecord R L) h513
  · intro A hA hAG hPA ψ hψ hψm
    obtain ⟨n, a, hn, hS⟩ := hs A hA hAG hPA ψ hψ hψm
    exact ⟨n, a, hn, fun q' => ⟨hw A hA hAG ψ hψ hψm q', hS q'⟩⟩
  · intro A hA hAG hPA ψ hψ hψm
    obtain ⟨n, a, hn, hS⟩ := hsI A hA hAG hPA ψ hψ hψm
    exact ⟨n, a, hn, fun q' => ⟨hwI A hA hAG ψ hψ hψm q', hS q'⟩⟩

end Config

/-! ### `hOuter` from the remaining inputs on every configuration -/

section Remaining

/-- **The remaining inputs of Theorem R.7's mixed and outer pockets** (`max(r_L, r_R) > k/2 − 4`): on every R.7
configuration with the heights `c = πχ(16/k)`, `c′ = 0` of the extremal family, every decomposition of its centred
counterflow, the force-word mean `u₀′` and every choice of versions of the walls `α_R`, `α_L` and of the counterflow's
trace, the inputs `R7OuterInputs` hold. -/
def R7OuterRemaining (k rL rR : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
      R7OuterInputs k rL rR P W' ζ' h'' u₀' R L η

/-- **The outer-pocket completion `RefWire.OuterPocketCompletion` from the remaining inputs** (the `hOuter` of
Theorem 1.2's late wiring at one outer pair): with `c = πχ(16/k)`, `c′ = 0`, on every configuration the decomposition of
its counterflow, the force-word mean and the versions are constructed (`R7Leaves.exists_isCfDecomp`,
`R7Leaves.exists_wallVersion`, `R7Leaves.exists_cfVersion_r7`), and `r7PocketStop_outer_of_config` applies. -/
theorem outerPocketCompletion_of_remaining (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) {k rL rR : ℝ} (haux7 : Sec4.Aux7Statement.{u} k)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 < max rL rR)
    (hrem : R7OuterRemaining.{u} k rL rR) : OuterPocketCompletion.{u} k rL rR := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  refine ⟨π * chiC (16 / k), 0, hc, le_rfl, ?_⟩
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
  obtain ⟨b', J', h', h'', 𝓕, VL, VR, B, hD⟩ := exists_isCfDecomp (by linarith : (0 : ℝ) < k).ne' hcfg.counterflow
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData k (flowLineRhoL k b' J' 0 0)
    (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0)
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hmR : ∀ t, Measurable fun ω => αR ω t := fun t => by
    have e : (fun ω => αR ω t) = fun ω => ΦαR (h ω) t := funext fun ω => by rw [(hΦ ω).1]
    rw [e]; exact (measurable_pi_apply t).comp (hΦαR.comp hcfg.gff.1)
  have hmL : ∀ t, Measurable fun ω => αL ω t := fun t => by
    have e : (fun ω => αL ω t) = fun ω => ΦαL (h ω) t := funext fun ω => by rw [(hΦ ω).2.2.2]
    rw [e]; exact (measurable_pi_apply t).comp (hΦαL.comp hcfg.gff.1)
  obtain ⟨R, hRc, hR0, hRm, hRae⟩ := exists_wallVersion hmR (hcfg.regular.mono fun ω hω => hω.1)
  obtain ⟨L, hLc, hL0, hLm, hLae⟩ := exists_wallVersion hmL (hcfg.regular.mono fun ω hω => hω.2.2.2.1)
  obtain ⟨η, hηc, -, hη0, hηm, hηtr⟩ := exists_cfVersion_r7 hk4 hc le_rfl hcfg.gff hcfg.counterflow
  have hV : IsR7Versions P W' αR αL R L η :=
    ⟨hRc, hR0, hRm, hRae, hLc, hL0, hLm, hLae, hηc, hη0, hηm, hηtr⟩
  exact r7PocketStop_outer_of_config h411 h51 haux7 hk4 hL hR hmax hc le_rfl hcfg hD hu₀' hV
    (hrem P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV)

open Wire StripSafe

/-- **Theorem R.7's reference without the outer-pocket completion as an input** (the drop-in for
`StripSafe.r7ReferenceStatement_late_sideDet_safe`): `hOuter` is replaced by the outer pockets' remaining inputs
`R7OuterRemaining` on the outer range; Propositions 4.11 and 5.1 in chart `Q` and Aux. lemma 7 are derived from the
A.1 rectangle families and the reference cover exactly as in that theorem. -/
theorem r7ReferenceStatement_late_sideDet_outer
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hsd : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalSideDetRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hout : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterRemaining.{0} k rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  have haux7 : ∀ k : ℝ, 4 < k → Sec4.Aux7Statement.{0} k :=
    aux7_of_sixteen_div fun κ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4
  exact r7ReferenceStatement_late_sideDet_safe hRect hRectEight Ref0 hCover0 hAvoid0 hsd
    fun κ hκ rL rR hL hR hmax => outerPocketCompletion_of_remaining h411 h51 (haux7 κ hκ) hκ hL hR hmax
      (hout κ hκ rL rR hL hR hmax)

end Remaining

end InteractingSLE.Sec7.HOuter
