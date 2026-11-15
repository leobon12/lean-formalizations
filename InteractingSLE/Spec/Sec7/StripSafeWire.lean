/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSafeR7
import InteractingSLE.Spec.Sec7.R7LeavesWire

/-!
# Theorem R.7's extremal reference without strip systems: `hstrip` discharged (R48-safe)

Packet PROVE-STRIPSYS-SAFE. PROVE-R7-LEAVES reduced Aux. lemma 37's attachments for the R.7 arms to a strip system on
every R.7 configuration (`R7Leaves.R7StripOnConfig`, the input `hstrip` of
`R7Leaves.r7ReferenceStatement_late_sideDet`),
which so far followed only from Theorem 1.4's staged-history construction input, i.e. through
`Theorem12ParamStatement` (R48-forbidden for Theorem 1.2's inputs). The attachments only use the constant-angle walls,
so the constant-angle strip system suffices, and it is constructed here from `h44` alone:

* **`exists_isConstStripSystem_r7`**: on every R.7 configuration with heights `c = πχ(16/k)`, `c′ = 0`, the field and
  the centred counterflow carry a constant-angle strip system (`StripSafe.IsConstStripSystem` at `16/k`) whose drivers
  are regular at every sample (`StripSafe.exists_isConstStripSystem`; counterflow lifetime from
  `R7Leaves.ae_counterflow_trace_r7`, heights from `R7Leaves.r7_strip_heights`);
* **`r7Attach_of_constStrip`**: `R7Leaves.r7Attach_of_stripSystem` for a constant-angle strip system (with
  `StripSafe.hwit_r7`, `hwitI_r7`; no regularization needed since the drivers are regular everywhere);
* **`r7ExtremalRemaining_of_core`**: `R7Leaves.r7ExtremalRemaining_of_strip` without `hstrip`;
* **`r7ReferenceStatement_late_leaves_safe`**, **`r7ReferenceStatement_late_sideDet_safe`**: the drop-ins
  `R7Leaves.r7ReferenceStatement_late_leaves` / `…_sideDet` for `Wire.late_r7ReferenceFamily` without `hstrip`.

R48: the only named inputs are those of `R7Leaves.r7ReferenceStatement_late_sideDet` minus `hstrip`; `h44` is
`Wire.late_theorem12ParamCond44Statement` from the A.1 rectangle families (R74). No Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param`, `Theorem14.StagedHistoryConstructionStatement`.
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

namespace InteractingSLE.Sec7.StripSafe

open R7Outer Sec5.Prop55Half WangWu WholeField Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks
  PocketWordAssembly PocketSeedOpen PocketStopField PocketStopWallsFin PocketStopWalls PocketCoupling
  StripPocketConfig PocketWordPerQ PocketStop R7Pocket RefWire R7Leaves
open R7Aux131 (constSpec aux131_angles_of_max_eq heights_const isFlowLineDriver_const)
open Exist.Staged (IsRegularDriver)

/-! ### The constant-angle strip system on every R.7 configuration -/

section Config

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **A constant-angle strip system on every R.7 configuration** (heights `c = πχ(16/k)`, `c′ = 0`), R48-safe: the
field and the centred counterflow of the configuration carry `StripSafe.IsConstStripSystem` at `16/k` with drivers
regular at every sample. -/
theorem exists_isConstStripSystem_r7 (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    ∃ Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      IsConstStripSystem (16 / k) (prop74Data (r7A k rR + π * chiC (16 / k)) (r7B k rL + 0)) {0} P h W' ζ' Es ∧
        ∀ spec j ω, IsRegularDriver (Es spec j ω) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights (rL := rL) (rR := rR) hk4
  exact exists_isConstStripSystem h44 hκ hκ4
    (isPiecewiseConstant_prop74Data (r7A k rR + π * chiC (16 / k)) (r7B k rL + 0)) hcumL hcumR hcfg.gff
    hcfg.counterflow ((ae_counterflow_trace_r7 hk4 hc le_rfl hcfg.gff hcfg.counterflow).mono fun ω hω => hω.1)

end Config

/-! ### Aux. lemma 37's attachments from a constant-angle strip system -/

section Attach

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **Aux. lemma 37's attachment constancy for the extremal R.7 pocket from a constant-angle strip system** (port of
`R7Leaves.r7Attach_of_stripSystem`: the strip system weakened to `IsConstStripSystem`, its drivers regular at every
sample, so no regularization is needed; the witness exclusions are `StripSafe.hwit_r7`, `hwitI_r7`). -/
theorem r7Attach_of_constStrip (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (hk4 : 4 < k) (hL : -2 < rL)
    (hR : -2 < rR) (hmax : max rL rR = k / 2 - 4) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsConstStripSystem (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} P h W' ζ' Es)
    (hreg : ∀ spec j ω, IsRegularDriver (Es spec j ω))
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ ({0} : Finset ℝ) →
      prop74Data (r7A k rR + c) (r7B k rL + c') y + a * chiC (16 / k) ≤ -sleLambda (16 / k))
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ ({0} : Finset ℝ) →
      sleLambda (16 / k) ≤ prop74Data (r7A k rR + c) (r7B k rL + c') y + a * chiC (16 / k))
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η)
    (hfirstR : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (R ω '' Ioc 0 (StripSys.rt q))) (negInv (R ω (StripSys.rt q))))
    (hfirstL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (L ω '' Ioc 0 (StripSys.rt q))) (negInv (L ω (StripSys.rt q)))) :
    (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0))) ∧
    (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0))) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  obtain ⟨-, hθ1, hθ2, hθ3⟩ := aux131_angles_of_max_eq hk4 hL hR hmax
  have hθR : R7.thetaR k rL ∈ Ico (-(π / 2)) (π / 2) := ⟨hθ1, hθ2.trans_le hθ3⟩
  have hθL : R7.thetaL k rR ∈ Ioc (-(π / 2)) (π / 2) := ⟨hθ1.trans_lt hθ2, hθ3⟩
  have hθRc : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) := Ico_subset_Icc_self hθR
  have hθLc : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθL
  have hregR : ∀ ω, IsRegularDriver (Es (constSpec (R7.thetaR k rL)) 0 ω) := fun ω => hreg _ _ ω
  have hregL : ∀ ω, IsRegularDriver (Es (constSpec (R7.thetaL k rR)) 0 ω) := fun ω => hreg _ _ ω
  -- the arms are the constant-angle walls of the strip family
  have hflR : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaR k rL) P h R ζαR :=
    IsFlowLine.congr_path hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
  have hflL : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaL k rR) P h L ζαL :=
    IsFlowLine.congr_path hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
  obtain ⟨hL0R, hR0R⟩ := heights_const hκ hκ4 hcumL hcumR hθRc
  obtain ⟨hL0L, hR0L⟩ := heights_const hκ hκ4 hcumL hcumR hθLc
  have hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (constSpec (R7.thetaR k rL)) 0 ω).1 ⊤ (R ω) :=
    (ae_isGeneratingTrace_of_isFlowLine h44 hκ hκ4 hb hL0R hR0R hflR (isFlowLineDriver_const hκ hb hcfg.gff
      (StripSafe.isStagedHistory_const hS hθRc))).mono fun ω hω => hω.2.2
  have hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (constSpec (R7.thetaL k rR)) 0 ω).1 ⊤ (L ω) :=
    (ae_isGeneratingTrace_of_isFlowLine h44 hκ hκ4 hb hL0L hR0L hflL (isFlowLineDriver_const hκ hb hcfg.gff
      (StripSafe.isStagedHistory_const hS hθLc))).mono fun ω hω => hω.2.2
  -- the walls' visits and order
  have hreg' := hcfg.regular
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg', hV.R_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.1
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg', hV.L_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.2.2.2.1
  have hwR := WallsPath.ae_walls_of_simpleProper_rat_firstHit hRs hV.η_cont hfirstR
  have hwL := WallsPath.ae_walls_of_simpleProper_rat_firstHit hLs hV.η_cont hfirstL
  have hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧
      IsWallReverseVisit (L ω) (η ω) ∧ IsWallVisited (L ω) (η ω) := by
    filter_upwards [hwR, hwL] with ω h1 h2 using ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))) := by
    filter_upwards [hcfg.order, hRs, hLs, hV.R_ae, hV.L_ae] with ω hω hRω hLω hRe hLe
    have hsub : range (L ω) ⊆ closedLeftSide (R ω) := by rw [hRe, hLe]; exact hω.2.1
    exact Lemma71Q.disjoint_range_leftSideOf_of_subset_closedLeftSide hLω hRω hsub
  have hwit := StripSafe.hwit_r7 h44 hS hcumL hcumR hθR hθL hregR hregL hV.R_cont hV.R_zero hV.R_meas hRtr
    hV.L_cont hV.L_zero hV.L_meas hLtr hV.η_trace hwalls hord
  have hwitI := StripSafe.hwitI_r7 h44 hS hcumL hcumR hθR hθL hregR hregL hV.R_cont hV.R_zero hV.R_meas hRtr
    hV.L_cont hV.L_zero hV.L_meas hLtr hV.η_trace hwalls hord
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hV.η_trace
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
        0 < rightLo (R ω) (L ω) (StripSys.rt q) →
          ¬ StripPocketPath.IsPocketWitness (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
      simp only [ae_all_iff]
      exact hwit q hq
    filter_upwards [htrace, hwalls, hw] with ω htr hwl hwω hconf hpos
    exact StripPocketPath.attachmentConstancy_of_noWitness hconf hpos htr.1 htr.2.1 (by simpa using htr.2.2) hwl.1
      hwl.2.2.1 hwl.2.1 fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf hpos
  · have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
        rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
          ¬ StripPocketPath.IsPocketWitnessInf (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
      simp only [ae_all_iff]
      exact hwitI q hq
    filter_upwards [htrace, hwalls, hw] with ω htr hwl hwω hconf h0
    exact StripPocketPath.attachmentConstancyInf_of_noWitness hconf h0 htr.1 htr.2.1 (by simpa using htr.2.2)
      hwl.1 hwl.2.2.1 hwl.2.1 hwl.2.2.2 fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf h0

end Attach

/-! ### The extremal remaining inputs and Theorem R.7's reference without `hstrip` -/

section Remaining

/-- **The extremal remaining inputs from the core inputs alone** (`R7Leaves.r7ExtremalRemaining_of_strip` without its
input `hstrip`: the constant-angle strip system is `exists_isConstStripSystem_r7`, Aux. lemma 37's attachments are
`r7Attach_of_constStrip`). -/
theorem r7ExtremalRemaining_of_core (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) {k rL rR : ℝ}
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : max rL rR = k / 2 - 4)
    (hcore : R7ExtremalCoreRemaining.{u} k rL rR (π * chiC (16 / k)) 0) :
    R7ExtremalRemaining.{u} k rL rR := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights (rL := rL) (rR := rR) hk4
  refine ⟨π * chiC (16 / k), 0, hc, le_rfl, ?_⟩
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  have hC := hcore P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  obtain ⟨Es, hS, hreg⟩ := exists_isConstStripSystem_r7 h44 hk4 hcfg
  obtain ⟨hat, hatI⟩ := r7Attach_of_constStrip h44 hk4 hL hR hmax hc le_rfl hcfg hS hreg hcumL hcumR hV hC.firstR
    hC.firstL
  exact ⟨hC.firstR, hC.firstL, hat, hatI, hC.side, hC.det⟩

open Wire

/-- **Theorem R.7's reference without strip systems** (`R7Leaves.r7ReferenceStatement_late_leaves` without its input
`hstrip`): from the A.1 rectangle families, the reference cover and avoidance of Proposition 5.1, the core extremal
inputs `hcore` and the outer-pocket completion `hOuter`. -/
theorem r7ReferenceStatement_late_leaves_safe
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hcore : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalCoreRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} :=
    late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)
  exact r7ReferenceStatement_of_remaining h411 h51
    (aux7_of_sixteen_div fun κ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4)
    (fun k hk4 rL rR hL hR hmax => r7ExtremalRemaining_of_core h44 hk4 hL hR hmax
      (hcore k hk4 rL rR hL hR hmax)) hOuter

/-- **Theorem R.7's reference with the wall first exits proved and without strip systems**
(`R7Leaves.r7ReferenceStatement_late_sideDet` without its input `hstrip`): the drop-in for
`Wire.late_r7ReferenceFamily` whose remaining R.7 inputs are the side limits and Proposition 5.13 (`hsd`) and the
outer-pocket completion (`hOuter`). -/
theorem r7ReferenceStatement_late_sideDet_safe
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hsd : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalSideDetRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  refine r7ReferenceStatement_late_leaves_safe hRect hRectEight Ref0 hCover0 hAvoid0
    (fun k hk4 rL rR hL hR hmax => ?_) hOuter
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2
  exact @r7ExtremalCoreRemaining_of_sideDet.{0} h411 h470 h47T k rL rR (π * chiC (16 / k)) 0 hk4 hL hR hmax
    (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le) le_rfl (hsd k hk4 rL rR hL hR hmax)

end Remaining

end InteractingSLE.Sec7.StripSafe
