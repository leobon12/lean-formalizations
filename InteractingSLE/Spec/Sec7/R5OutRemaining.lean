import InteractingSLE.Spec.Sec7.R5OutShared
import InteractingSLE.Spec.Sec7.R5OutRelativeFromWord

/-! # The outer R.5 and continuity binders from the shared lift and initial-height inputs -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R5Out

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont R5Phase OuterCont R5Enl

universe u

open R7Outer R7Leaves StripPocketConfig RefWire HOuter

/-- Only the common lift and initial wall-height inputs remain. All source
reference charts, marked laws, ambient comparisons and incident covers are discharged. -/
def R7OuterLiftHeightMRemaining (k rL rR c c' : ℝ) : Prop :=
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
    ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedOuterLiftHeightInputOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) W' ζ' VL VR ∧
        TwoSeedOuterLiftHeightInputInfOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) W' ζ' VL VR

/-- Source component clauses of outer R.5, using the original rational-time
references and the R98 ambient half-disc comparison. -/
theorem r7OuterR5MRemainingCompOn_of_liftHeight {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hr5 : R7OuterLiftHeightMRemaining.{u} k rL rR c c') : R7OuterR5MRemainingCompOn.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hr5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
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
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR
    (hreg.mono fun ω hω => hω.2.2.2.2.1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL
    (hreg.mono fun ω hω => hω.2.2.2.2.2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  exact ⟨twoSeedR5CompInputOn_of_liftHeight hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hGp (fun ω hω => hcfgP ω hω.1 hω.2) (fun ω hω => hζG ω hω.1) hs,
    twoSeedR5CompInputInfOn_of_liftHeight hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hG0 hcfgI' (fun ω hω => hζG ω hω.1) hsI⟩


/-- The outer phase word follows from the source component clauses. -/
theorem r7OuterPhaseWordMRemaining_of_liftHeight {k rL rR c c' : ℝ}
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hShared : R7OuterLiftHeightMRemaining.{u} k rL rR c c') :
    R7OuterPhaseWordMRemaining.{u} k rL rR c c' :=
  r7OuterPhaseWordMRemaining_of_r5CompOn hk4 hc hc'
    (r7OuterR5MRemainingCompOn_of_liftHeight hk4 hc hc' hShared)

/-- The requested unchanged relative-cover binder, obtained from the source
rational-time proof and its phase word. -/
theorem r7OuterRelativeCoverMRemaining_of_liftHeight {k rL rR c c' : ℝ}
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hShared : R7OuterLiftHeightMRemaining.{u} k rL rR c c') :
    R7OuterRelativeCoverMRemaining.{u} k rL rR c c' :=
  r7OuterRelativeCoverMRemaining_of_phaseWord
    (r7OuterPhaseWordMRemaining_of_liftHeight hk4 hc hc' hShared)

/-- The outer phase continuity from the same shared lift and height inputs. -/
theorem r7OuterPhaseContMRemaining_of_liftHeight {k rL rR c c' : ℝ}
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hShared : R7OuterLiftHeightMRemaining.{u} k rL rR c c') :
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL rR c c' :=
  r7OuterPhaseContMRemaining_of_relativeCover hk4 hc hc'
    (r7OuterRelativeCoverMRemaining_of_liftHeight hk4 hc hc' hShared)

/-- A replacement for the outer R.5 continuity assembly input, leaving
only the shared lift words and initial wall heights named. -/
theorem hOuterCont_of_liftHeight
    (hShared : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterLiftHeightMRemaining.{u} k rL rR (Real.pi * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR := by
  apply hOuterCont_of_relativeCover
  intro k hk4 rL rR hL hR hmax
  exact r7OuterRelativeCoverMRemaining_of_liftHeight hk4
    (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith))
      (R7.sixteen_div_lt_four hk4)).le) le_rfl (hShared k hk4 rL rR hL hR hmax)

end InteractingSLE.Sec7.R5Out
