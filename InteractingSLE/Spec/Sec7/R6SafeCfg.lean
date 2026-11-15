/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FinCfg
import InteractingSLE.Spec.Sec7.StripSafeWire

/-!
# R.6's inner tests from a constant-angle strip system (R48-safe)

PROVE-R6-SAFE. `R6Fin.exists_cfgEvent_extremal` (PROVE-R6-CERT2) takes a full strip system
(`StripSys.IsStripSystem`), which PROVE-STRIPSYS-SAFE showed is not constructible R48-safely on R.7 configurations.
It uses the strip system only for Aux. 37's attachments, which need only the constant-angle walls.
`exists_cfgEvent_extremal_const` is the same theorem for a constant-angle strip system
(`StripSafe.IsConstStripSystem`, drivers regular at every sample), with the attachments from
`StripSafe.r7Attach_of_constStrip`; the proof is otherwise verbatim.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open LQGMetric (DistOn)
open QuantumZipper (H chiC)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open R7Outer R7Leaves WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly
  PocketSeedOpen PocketStopWalls PocketCoupling StripPocketConfig R7Aux131 PocketWordPerQ PocketStopWallsFin

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **The extremal pocket configuration at every sample of a walls' event** (Aux. 131, one rational change
parameter `s`), from a **constant-angle** strip system (`R6Fin.exists_cfgEvent_extremal` with
`StripSafe.IsConstStripSystem` and regular drivers): on an extremal R.7 configuration (strip heights `hcumL`,
`hcumR`), with versions `R`, `L`, `η` of the arms and of the counterflow's trace, there is a walls-measurable event
`F` on which the change configuration, the infinite lifetime and the extremal pocket configuration (both shapes)
hold, and which contains almost every sample whose left wall at `rt s` is off the right wall. -/
theorem exists_cfgEvent_extremal_const (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : max rL rR = k / 2 - 4) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSafe.IsConstStripSystem (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} P h W' ζ' Es)
    (hSreg : ∀ spec j ω, Exist.Staged.IsRegularDriver (Es spec j ω))
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ ({0} : Finset ℝ) →
      prop74Data (r7A k rR + c) (r7B k rL + c') y + a * chiC (16 / k) ≤ -sleLambda (16 / k))
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ ({0} : Finset ℝ) →
      sleLambda (16 / k) ≤ prop74Data (r7A k rR + c) (r7B k rL + c') y + a * chiC (16 / k))
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) (s : ℚ) (hs : 0 < s) :
    ∃ F : Set Ω, MeasurableSet[wallsSigma P R L] F ∧
      (∀ᵐ ω ∂P, L ω (StripSys.rt s) ∉ range (R ω) → ω ∈ F) ∧
      ∀ ω ∈ F, IsChangeConfigInc (R ω) (L ω) (StripSys.rt s) ∧ ζ' ω = ⊤ ∧
        (0 < rightLo (R ω) (L ω) (StripSys.rt s) →
          IsCfPocketConfig (R ω) (L ω) (StripSys.rt s) (fun t : ℝ => W' t.toNNReal ω) (η ω)) ∧
        (rightLo (R ω) (L ω) (StripSys.rt s) = 0 →
          IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt s) (fun t : ℝ => W' t.toNNReal ω) (η ω)) := by
  classical
  have hgff := hcfg.gff
  have hreg := hcfg.regular
  obtain ⟨-, hθ1, hθ2, hθ3⟩ := aux131_angles_of_max_eq hk4 hL hR hmax
  have hθRc : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) := ⟨hθ1, (hθ2.trans_le hθ3).le⟩
  have hθLc : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) := ⟨(hθ1.trans_lt hθ2).le, hθ3⟩
  -- the walls: simple proper curves
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg, hV.R_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.1
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg, hV.L_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.2.2.2.1
  -- the rational first exits (Lemma 4.7) and the visits
  have hflR : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaR k rL) P h R ζαR :=
    IsFlowLine.congr_path hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
  have hflL : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaL k rR) P h L ζαL :=
    IsFlowLine.congr_path hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
  have hfirstR := firstHit_r7 h411 h47 h47T hk4 hc hc' hgff hcfg.counterflow hθRc hflR hRs hV.η_zero hV.η_trace
  have hfirstL := firstHit_r7 h411 h47 h47T hk4 hc hc' hgff hcfg.counterflow hθLc hflL hLs hV.η_zero hV.η_trace
  have hwR := WallsPath.ae_walls_of_simpleProper_rat_firstHit hRs hV.η_cont hfirstR
  have hwL := WallsPath.ae_walls_of_simpleProper_rat_firstHit hLs hV.η_cont hfirstL
  -- the order (Proposition 5.5, Lemma 6.13)
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hpair := R7StopIn.ae_pair_r7 h55 hk4 hc hc' (R7.thetaR_lt_thetaL hk4 hL hR hmax.ge)
    (thetaR_mem_r7 rR hk4 hL) (thetaL_mem_r7 rL hk4 hR) hgff hcfg.flow_αR hcfg.flow_αL hΦαR hΦαL
    (fun ω => (hΦ ω).1) (fun ω => (hΦ ω).2.2.2)
    (hreg.mono fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.2.2⟩)
  have hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))) := by
    filter_upwards [hpair, hRs, hLs, hV.R_ae, hV.L_ae] with ω hω hRω hLω hRe hLe
    have hsub : range (L ω) ⊆ closedLeftSide (R ω) := by rw [hRe, hLe]; exact hω.1
    exact Lemma71Q.disjoint_range_leftSideOf_of_subset_closedLeftSide hLω hRω hsub
  -- the counterflow
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hgff hcfg.counterflow hV.η_trace
  have htrans := ae_transient_counterflow_r7 haux7 hk4 hc hc' hgff hcfg.counterflow hV.η_trace
  -- Aux. 37's attachments
  obtain ⟨hat, hatI⟩ := StripSafe.r7Attach_of_constStrip h44 hk4 hL hR hmax hc hc' hcfg hS hSreg hcumL hcumR hV
    hfirstR hfirstL
  -- the conull walls' event
  obtain ⟨G₀, hG₀m, hG₀ae, hG₀⟩ := exists_measurableSet_nullSets_ae (P := P)
    (hRs.and (hLs.and (hwR.and (hwL.and (hord.and (hζ.and (htrace.and (htrans.and
      ((hat s hs).and (hatI s hs))))))))))
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
  obtain ⟨hRω, hLω, hwRω, hwLω, hordω, hζω, ⟨htr, hWc, hW0⟩, htrω, hatω, hatIω⟩ := hG₀ ω hω.1
  have hoff : L ω (StripSys.rt s) ∉ range (R ω) := fun h' => hω.2 (subset_closure h')
  have hpos' : 0 < StripSys.rt s := Real.toNNReal_pos.2 (Rat.cast_pos.2 hs)
  have hconf : IsChangeConfigInc (R ω) (L ω) (StripSys.rt s) :=
    isChangeConfigInc_of_reverseVisit hRω hLω (hV.η_cont ω) (hV.η_zero ω) hwRω.1 hwLω.1 hwRω.2 hpos' hoff
  have hor := hconf.isFlowChartOriented_of_leftFrontier hconf.left rfl hordω
  have hW0' : W' (Real.toNNReal 0) ω = 0 := by rw [Real.toNNReal_zero]; exact hW0
  refine ⟨hconf, hζω, fun hp => ⟨hconf, hp, hor, htr, hWc, hW0', hwRω.1, hwLω.1, hwRω.2, hatω hconf hp⟩,
    fun h0 => ⟨hconf, h0, hor, htr, hWc, hW0', htrω, hwRω.1, hwLω.1, hwRω.2, hwLω.2, hatIω hconf h0⟩⟩

end InteractingSLE.Sec7.R6Safe
