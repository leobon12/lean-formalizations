/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ConeData
import InteractingSLE.Spec.Supplement.BR3Ref
import InteractingSLE.Spec.Supplement.GW2SdpRoot
import InteractingSLE.Spec.Sec5.Aux61CptThm

/-!
# The near structure (N3), step G: the source counterflow's data word and its admissibility

Packet PROVE-GW2-SDE (round 18). The counterflow word `c′` of GEOM2's root word (`GW2Wm.rootWordX κ c′`) is data of
the top (`T14Cur.CfWord`). The source's centred counterflow is the angle-`0` flow line at `16/κ` of the EXPLICIT
counterflow data `counterflowData κ b` with jumps `counterflowJumps J` (`GW2Cone.isFlowLineDriver_counterflowData`).
Here:

* **`cfWordSrc c`**: a word of that data (`Restart.BoundaryWord.exists_fn_eq`), `cfWordSrc_jumps`, `cfWordSrc_fn`;
* **`isFlowLineDriver_cfWordSrc`**: the counterflow is the flow line of `cfWordSrc c` (`GW1.isFlowLineDriver_congr`);
* **`cfWordSrc_admissible`**: its prefix sums of force weights are `> −2` on both sides (Lemma GW0,
  `GW0.counterflow_admissible`, from Theorem 1.3 via `BR3Ref.gw0ForwardStatement_of_theorem13`);
* **`rootForms_zero_src`**: hence the side forms of the root word at the root `0` (`GW2Sdp.rootForms_zero`, the
  root's chart reader is `0` because a bounded hull inverts away from `0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist.Staged Exist.StagedLaw GW2TipSystem.RootC24 GW2TipSystem.RootH10 Sec7.StripSysField

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The source counterflow's data word**: a word of `counterflowData κ b` with jumps `counterflowJumps J`. -/
def cfWordSrc (c : SourceData Ω) : BoundaryWord :=
  (Restart.BoundaryWord.exists_fn_eq (isPiecewiseConstant_counterflowData c.κ c.hb)).choose

theorem cfWordSrc_jumps (c : SourceData Ω) : (cfWordSrc c).jumps = counterflowJumps c.jumps :=
  (Restart.BoundaryWord.exists_fn_eq (isPiecewiseConstant_counterflowData c.κ c.hb)).choose_spec.1

theorem cfWordSrc_fn (c : SourceData Ω) :
    ∀ y ∉ counterflowJumps c.jumps, (cfWordSrc c).fn y = counterflowData c.κ c.b y :=
  (Restart.BoundaryWord.exists_fn_eq (isPiecewiseConstant_counterflowData c.κ c.hb)).choose_spec.2

/-- **The source counterflow is the angle-`0` flow line at `16/κ` of its data word.** -/
theorem isFlowLineDriver_cfWordSrc (c : SourceData Ω) :
    ∃ h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
      IsFlowLineDriver (16 / c.κ) (cfWordSrc c).fn (cfWordSrc c).jumps 0 c.P h' c.W c.ζ := by
  obtain ⟨h', -, hfl⟩ := GW2Cone.isFlowLineDriver_counterflowData c.hκ c.hb c.hh c.hcf
  have hb' := isPiecewiseConstant_counterflowData c.κ c.hb
  have hoff : ∀ y, y ∉ counterflowJumps c.jumps → counterflowData c.κ c.b y = (cfWordSrc c).fn y :=
    fun y hy => (cfWordSrc_fn c y hy).symm
  have hlims := GW1.lims_eq_of_eq_off_finset (counterflowJumps c.jumps) hoff
  have hL : PiecewiseConstantBoundaryData.leftLim (counterflowData c.κ c.b) =
      PiecewiseConstantBoundaryData.leftLim (cfWordSrc c).fn := funext fun x => (hlims x).1
  have hR : PiecewiseConstantBoundaryData.rightLim (counterflowData c.κ c.b) =
      PiecewiseConstantBoundaryData.rightLim (cfWordSrc c).fn := funext fun x => (hlims x).2
  have hw := (cfWordSrc c).isPiecewiseConstantBoundaryData
  refine ⟨h', GW1.isFlowLineDriver_congr (GW1.jumpSet_eq_of_lims hb' hw hL hR) hL hR hfl⟩

/-- **The source counterflow word is admissible** (Lemma GW0): its prefix sums of force weights are `> −2`. -/
theorem cfWordSrc_admissible (c : SourceData Ω) :
    (∀ i : Fin (flowLineNL (cfWordSrc c).fn (cfWordSrc c).jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL (16 / c.κ) (cfWordSrc c).fn (cfWordSrc c).jumps 0 0 l) ∧
    (∀ i : Fin (flowLineNR (cfWordSrc c).fn (cfWordSrc c).jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR (16 / c.κ) (cfWordSrc c).fn (cfWordSrc c).jumps 0 0 l) := by
  have hGW0 : GW0.GW0ForwardStatement.{u} :=
    BR3Ref.gw0ForwardStatement_of_theorem13 Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
  obtain ⟨h', hfl⟩ := isFlowLineDriver_cfWordSrc c
  exact GW0.counterflow_admissible hGW0 c.hκ c.hκ4 hfl c.hζ

/-- **The side forms of the root word at the root `0`** for the source counterflow word, at a record of time `s`. -/
theorem rootForms_zero_src (c : SourceData Ω) (r : RecData) (hr : rtime r = c.s) :
    (∀ h ∈ GW2Sdp.rootHeightsL (GW2Wm.rootWordX c.κ (cfWordSrc c) 0 c.s r), h ∈ oldLeftHeights c.κ ∨
      ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / c.κ) * (1 + S) + Real.pi * chiC c.κ) ∧
    (∀ h ∈ GW2Sdp.rootHeightsR (GW2Wm.rootWordX c.κ (cfWordSrc c) 0 c.s r), h ∈ oldRightHeights c.κ ∨
      ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / c.κ) * (1 + S) - Real.pi * chiC c.κ) := by
  obtain ⟨hadmL, hadmR⟩ := cfWordSrc_admissible c
  have h0 : GW2Rz.baseRead 0 c.s r = 0 := by
    refine GW2Sdp.baseRead_zero c.s r hr ?_
    rw [Complex.ofReal_zero]
    exact Supp8.GB6.CoordB.zero_notMem_closure_invHull (continuous_rdrv r) c.s.coe_nonneg
  exact GW2Sdp.rootForms_zero c.hκ (cfWordSrc c) hadmL hadmR c.s r h0

end InteractingSLE.Theorem14.GW2Sds
