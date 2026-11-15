/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LeavesSource

/-!
# Theorem R.7's extremal reference (Aux. lemma 131) on the R.7 field

Packet PROVE-R7-LEAVES. Theorem 1.2's wiring (`Wire.late_aux131Family`, PROVE-WIRE-PARTA) proves the extremal pockets
(`max(r_L, r_R) = d = k/2 − 4`) of Theorem R.7 from an abstract reference object with about thirty source facts
(`hAuxT'`, …, `hAuxord`, `hAuxtrace`). Here that object is **constructed**: on the R.7 field of
`R7Outer.IsR7OuterConfig` (the R48-safe construction `R7Outer.exists_isR7OuterConfig`, from Propositions 4.11 and 5.1
in chart `Q`), the right wall is the arm `α_R` (angle `θ_R`) and the left wall the arm `α_L` (angle `θ_L`); for
extremal pairs both angles are in `[−π/2, π/2]` (`R7Aux131.aux131_angles_of_max_eq`), so the pocket between them is
Aux. lemma 131's constant-angle pocket.

Discharged here (from the configuration alone): the counterflow coupling, its chart transport and translation, the
centred GFF, the force-word mean, the measurable killed driving, the infinite lifetime, the walls' continuity, start,
measurability, simplicity, field determination and entrance-history locality, distinct ranges (Proposition 5.5 and
Lemma 6.13 through `R7StopIn.ae_pair_r7`), the order (`α_L` in the closed left side of `α_R`), the counterflow's trace,
its Loewner trace and its transience (Aux. 7 at `k`), and the wall visits from rational first exits
(`WallsPath.ae_walls_of_simpleProper_rat_firstHit`).

**Remaining inputs** (`R7ExtremalInputs`, stated on any versions of the walls and the counterflow's trace): the two
rational first-exit laws (Lemma 5.7 in the inversion chart, the `hfirstR`/`hfirstL` of PROVE-WALLS-PATH), Aux. lemma
37's attachment constancy in the two pocket shapes, the two-seed side limits (Lemmas R.5–R.6, the `hAuxside` of the
wiring) and Proposition 5.13 for the counterflow (the counterflow is a Borel function of the field up to null sets).

* `IsR7Versions`, `R7ExtremalInputs`: the versions and the remaining inputs;
* `r7PocketStop_extremal_of_config`: `R7PocketStopStatement k r_L r_R GoodR7` on one configuration;
* `R7ExtremalRemaining`, `r7PocketStop_extremal`: the same from the remaining inputs on every configuration;
* `aux131Family_of_remaining`: the extremal family consumed by
  `RefWire.r7ReferenceStatement_of_extremal_outer_completion`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
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

namespace InteractingSLE.Sec7.R7Leaves

open R7Outer Sec5.Prop55Half WangWu WholeField Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks
  PocketWordAssembly PocketSeedOpen PocketStopField PocketStopWallsFin PocketStopWalls PocketCoupling
  StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket RefWire

/-! ### Transience of the R.7 counterflow -/

section Transient

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **The R.7 counterflow is transient** (Aux. lemma 7 at `k` for its admissible word; as
`StripPocketPath.ae_transient_counterflow`): every version of its trace tends to `∞` almost surely. -/
theorem ae_transient_counterflow_r7 (haux7 : Sec4.Aux7Statement.{u} k) (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖η ω t‖) atTop atTop := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / (16 / k) := by positivity
  obtain ⟨hbL, hbR⟩ := r7_cf_bounds (rL := rL) (rR := rR) hk4 hc hc'
  have hbd := StripPocketPath.counterflowData_bounds_off hκ (g := prop74Data (r7A k rR + c) (r7B k rL + c'))
    (J := {0}) hbL hbR
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk'
    (StripSysField.isPiecewiseConstant_counterflowData (16 / k) hb) hbd.1 hbd.2
  have hF' := Theorem15.isOrderedForceWord_flowLine
    (StripSysField.counterflowData (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')))
    (StripSysField.counterflowJumps {0}) 0
  have e : 16 / (16 / k) = k := by field_simp
  have haux7' : Sec4.Aux7Statement.{u} (16 / (16 / k)) := by rw [e]; exact haux7
  filter_upwards [haux7' _ _ _ _ P 𝓕₂ W' VL₂ VR₂ B₂ ζ' hF' hadm hC'.1, hηtr] with ω hω hη
  have h1 := hω.2.2 _ hη
  have h2 : Tendsto (fun t : ℝ => ‖η ω (t.toNNReal : ℝ)‖) atTop atTop := h1.comp tendsto_real_toNNReal_atTop
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.coe_toNNReal _ ht]

end Transient

/-! ### The versions and the remaining inputs -/

section Inputs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **Versions of the two walls and of the counterflow's trace**: `R`, `L` continuous from `0` at every sample,
measurable at fixed times, almost surely equal to the arms `α_R`, `α_L`; `η` continuous on `[0, ∞)` from `0` at every
sample, measurable at fixed times, almost surely the generating trace of the counterflow driver `W′`. -/
structure IsR7Versions (P : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (αR αL R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ) : Prop where
  R_cont : ∀ ω, Continuous (R ω)
  R_zero : ∀ ω, R ω 0 = 0
  R_meas : ∀ t, Measurable fun ω => R ω t
  R_ae : ∀ᵐ ω ∂P, R ω = αR ω
  L_cont : ∀ ω, Continuous (L ω)
  L_zero : ∀ ω, L ω 0 = 0
  L_meas : ∀ t, Measurable fun ω => L ω t
  L_ae : ∀ᵐ ω ∂P, L ω = αL ω
  η_cont : ∀ ω, ContinuousOn (η ω) (Ici 0)
  η_zero : ∀ ω, η ω 0 = 0
  η_meas : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t
  η_trace : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)

/-- **The remaining inputs of the extremal R.7 pocket** on versions `R`, `L`, `η` of the walls and of the counterflow:
* `firstR`, `firstL` — Lemma 5.7 in the inversion chart at rational wall times: the counterflow first hits the inverted
  wall prefix `m(R((0, q]))` at its tip `m(R(q))` (PROVE-WALLS-PATH's `hfirstR`, `hfirstL`);
* `attach`, `attachInf` — Aux. lemma 37's attachment constancy in the bounded change pocket and in the pocket at the
  flow seed (the `hattach`, `hattachI` of `RefWire.r7PocketStopStatement_of_sideLimit`, transience and the left
  wall's visits removed: they are proved here);
* `side` — the two-seed side limits (Lemmas R.5–R.6; the `hside` of `RefWire.r7PocketStopStatement_of_sideLimit` with
  the field's mean `u₀′` as harmonic part);
* `det` — Proposition 5.13 for the counterflow: almost surely its trace is a Borel function of the translated field
  `h″` of the coupling. -/
structure R7ExtremalInputs (k rL rR : ℝ) (P : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (h'' : Ω → DistOn upperHalfPlaneOpens) (u₀' : ℂ → ℝ) (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ) : Prop where
  firstR : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
    Sec4.IsFirstHitPoint (η ω) T (negInv '' (R ω '' Ioc 0 (StripSys.rt q))) (negInv (R ω (StripSys.rt q)))
  firstL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
    Sec4.IsFirstHitPoint (η ω) T (negInv '' (L ω '' Ioc 0 (StripSys.rt q))) (negInv (L ω (StripSys.rt q)))
  attach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
    0 < rightLo (R ω) (L ω) (StripSys.rt q) →
    Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
      (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
      (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0))
  attachInf : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
    rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
    Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
      (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0))
  side : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
    (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
    (∀ ω ∈ G, ζ' ω = ⊤) →
    (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
    (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
    TwoSeedSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
        {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
      TwoSeedSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
        {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'
  det : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h'' inferInstance]
    fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t

end Inputs

/-! ### The extremal pocket on one configuration -/

section Config

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **Theorem R.7's extremal pocket on one R.7 configuration** (Aux. lemma 131, `max(r_L, r_R) = k/2 − 4`): on an
`IsR7OuterConfig` with walls `R`, `L` versions of the arms `α_R`, `α_L` and `η` a version of the counterflow's trace,
`R7PocketStopStatement k r_L r_R GoodR7` follows from the remaining inputs `R7ExtremalInputs` alone; every source fact
of `RefWire.r7PocketStopStatement_of_sideLimit` other than those is proved from the configuration. -/
theorem r7PocketStop_extremal_of_config (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : Sec4.Aux7Statement.{u} k)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : max rL rR = k / 2 - 4) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η)
    (hin : R7ExtremalInputs k rL rR P W' ζ' h'' u₀' R L η) :
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
  -- the walls: simplicity, determination, locality
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg, hV.R_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.1
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg, hV.L_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.2.2.2.1
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR
    (hreg.mono fun ω hω => hω.2.2.2.2.1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL
    (hreg.mono fun ω hω => hω.2.2.2.2.2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae
  -- the visits, from the rational first exits
  have hwR := WallsPath.ae_walls_of_simpleProper_rat_firstHit hRs hV.η_cont hin.firstR
  have hwL := WallsPath.ae_walls_of_simpleProper_rat_firstHit hLs hV.η_cont hin.firstL
  have hRw : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) := by
    filter_upwards [hRs, hwR] with ω h1 h2 using ⟨h1, h2⟩
  have hLw : ∀ᵐ ω ∂P, IsSimpleProper (L ω) ∧ IsWallReverseVisit (L ω) (η ω) := by
    filter_upwards [hLs, hwL] with ω h1 h2 using ⟨h1, h2.1⟩
  -- distinct ranges and order (Proposition 5.5, Lemma 6.13)
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hpair := R7StopIn.ae_pair_r7 h55 hk4 hc hc' (R7.thetaR_lt_thetaL hk4 hL hR hmax.ge)
    (thetaR_mem_r7 rR hk4 hL) (thetaL_mem_r7 rL hk4 hR) hgff hcfg.flow_αR hcfg.flow_αL hΦαR hΦαL
    (fun ω => (hΦ ω).1) (fun ω => (hΦ ω).2.2.2)
    (hreg.mono fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.2.2⟩)
  have hne : ∀ᵐ ω ∂P, range (L ω) ≠ range (R ω) := by
    filter_upwards [hpair, hV.R_ae, hV.L_ae] with ω hω hRe hLe
    obtain ⟨t, -, -, ht⟩ := hω.2.2 1 2 one_pos one_lt_two
    rw [hRe, hLe]
    intro hrange
    exact ht (hrange ▸ mem_range_self t)
  have hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))) := by
    filter_upwards [hpair, hRs, hLs, hV.R_ae, hV.L_ae] with ω hω hRω hLω hRe hLe
    have hsub : range (L ω) ⊆ closedLeftSide (R ω) := by rw [hRe, hLe]; exact hω.1
    exact Lemma71Q.disjoint_range_leftSideOf_of_subset_closedLeftSide hLω hRω hsub
  -- the counterflow
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hgff hcfg.counterflow hV.η_trace
  have htrans := ae_transient_counterflow_r7 haux7 hk4 hc hc' hgff hcfg.counterflow hV.η_trace
  have hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (L ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) := fun q hq => by
    filter_upwards [htrans, hwL, hin.attachInf q hq] with ω h1 h2 h3 hcf h0
    exact ⟨h1, h2.2, h3 hcf h0⟩
  have hfun : (fun ω => centredField h'' u₀' ω + smoothDist upperHalfPlaneOpens u₀') = h'' :=
    funext fun ω => by simp only [centredField, sub_add_cancel]
  have h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField h'' u₀' ω + smoothDist upperHalfPlaneOpens u₀') inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t := by
    rw [hfun]; exact hin.det
  exact RefWire.r7PocketStopStatement_of_sideLimit hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont
    hV.R_zero hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hV.η_cont hV.η_zero hRw hLw hne hord
    htrace hin.attach hattachI hu₀'.1 hu₀'.2.1 hin.side h513

end Config

/-! ### The extremal pockets from the remaining inputs on every configuration -/

/-- **The remaining inputs of Theorem R.7's extremal pockets** (`max(r_L, r_R) = k/2 − 4`): for some heights
`c, c' ≥ 0`, on every R.7 configuration, every decomposition of its centred counterflow, the force-word mean `u₀′` and
every choice of versions of the walls `α_R`, `α_L` and of the counterflow's trace, the inputs `R7ExtremalInputs` hold
(rational first exits, Aux. lemma 37's attachment constancy, the two-seed side limits, Proposition 5.13). -/
def R7ExtremalRemaining (k rL rR : ℝ) : Prop :=
  ∃ c c' : ℝ, 0 ≤ c ∧ 0 ≤ c' ∧
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
      (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
      IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
      ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
        (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
        (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
      ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
        (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
        (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
      ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
        R7ExtremalInputs k rL rR P W' ζ' h'' u₀' R L η

/-- **Theorem R.7's extremal pocket** (Aux. lemma 131) from its remaining inputs: the configuration
(`R7Outer.exists_isR7OuterConfig`), the decomposition of its counterflow, the force-word mean and the versions are
constructed here, and `r7PocketStop_extremal_of_config` applies. -/
theorem r7PocketStop_extremal (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) {k rL rR : ℝ} (haux7 : Sec4.Aux7Statement.{u} k)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : max rL rR = k / 2 - 4)
    (hrem : R7ExtremalRemaining.{u} k rL rR) : R7PocketStopStatement.{u} k rL rR GoodR7 := by
  obtain ⟨c, c', hc, hc', hrem⟩ := hrem
  obtain ⟨Ω, mΩ, hSB, P, hP, h, W', ζ', αR, βR, βL, αL, ζαR, ζβR, ζβL, ζαL, hcfg⟩ :=
    exists_isR7OuterConfig h411 h51 hk4 hL hR hmax.ge hc hc'
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
  obtain ⟨η, hηc, -, hη0, hηm, hηtr⟩ := exists_cfVersion_r7 hk4 hc hc' hcfg.gff hcfg.counterflow
  have hV : IsR7Versions P W' αR αL R L η :=
    ⟨hRc, hR0, hRm, hRae, hLc, hL0, hLm, hLae, hηc, hη0, hηm, hηtr⟩
  exact r7PocketStop_extremal_of_config h411 h51 haux7 hk4 hL hR hmax hc hc' hcfg hD hu₀' hV
    (hrem P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV)

/-- Aux. lemma 7 at every `k > 4` from its `16/κ` form (`16/(16/k) = k`), e.g.
`Sec5.aux7Statement_sixteen_div_of_partA_of_clearance`. -/
theorem aux7_of_sixteen_div (h7 : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec4.Aux7Statement.{u} (16 / κ)) (k : ℝ) (hk4 : 4 < k) :
    Sec4.Aux7Statement.{u} k := by
  have e : 16 / (16 / k) = k := by field_simp
  have hs : Sec4.Aux7Statement.{u} (16 / (16 / k)) :=
    h7 (16 / k) (R7.sixteen_div_pos (by linarith)) (R7.sixteen_div_lt_four hk4)
  rw [← e]
  exact @hs

/-- **The extremal family of Theorem R.7** (the `h131` of `RefWire.r7ReferenceStatement_of_extremal_outer_completion`)
from Propositions 4.11 and 5.1 in chart `Q`, Aux. lemma 7 and the remaining inputs. -/
theorem aux131Family_of_remaining (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : ∀ k : ℝ, 4 < k → Sec4.Aux7Statement.{u} k)
    (hrem : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalRemaining.{u} k rL rR) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7PocketStopStatement.{u} k rL rR GoodR7 := fun k hk4 rL rR hL hR hmax =>
  r7PocketStop_extremal h411 h51 (haux7 k hk4) hk4 hL hR hmax (hrem k hk4 rL rR hL hR hmax)

/-- **Theorem R.7's reference** (`hR7`) from the extremal remaining inputs and the outer-pocket completion. -/
theorem r7ReferenceStatement_of_remaining (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : ∀ k : ℝ, 4 < k → Sec4.Aux7Statement.{u} k)
    (hrem : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalRemaining.{u} k rL rR)
    (hout : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPocketCompletion.{u} k rL rR) :
    R7.R7ReferenceStatement.{u} :=
  r7ReferenceStatement_of_extremal_outer_completion h411 h51 (aux131Family_of_remaining h411 h51 haux7 hrem) hout

end InteractingSLE.Sec7.R7Leaves
