/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4BarrierCond
import InteractingSLE.Spec.Supplement.WalkContinuum
import InteractingSLE.Spec.Supplement.GW3SidedProofWalk
import InteractingSLE.Spec.Supplement.SB4ProofFrontier
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Supplement.GW4TraverseField
import InteractingSLE.Spec.Supplement.GB11ConnGrowth
import InteractingSLE.Spec.Supplement.GW2aPieceChart

/-!
# GB11's barrier input for each sample, from the walk inputs, SB's frontiers and the visit order

Packet PROVE-T14-GW4T4, item (3). `GW4Reg.GW4BarrierSelfRegStatement` (PROVE-T14-GW4T3) asks, `P`-almost surely,
for complete simple flows `α_R`, `α_L` parametrizing the two boundary walks, with the pocket shape, such that every
generating trace of the ambient counterflow satisfies GB11's barrier input (`GB11.IsGB11Barrier`). This file splits it
into the existing shared inputs and two new, sharply delimited ones.

## What is derived here

* **Complete simple flows** from GW1's properness of the two walks (`WalkCont.RightWalkProperRegStatement`,
  `GW3SidedProof.LeftWalkProperRegStatement`).
* **No common open subarc** from `WalkCont.WalkNoCommonContinuumRegStatement` (the image of a nondegenerate
  parameter interval is a nondegenerate continuum).
* **(GB11.B)**, every finite physical counterflow point lies in `R ∪ L ∪ ⋃ C_j`, from SB's frontier statement
  (`SB.SBFrontierRegStatement`: the completed range misses the open right side of `R` and the open left side of `L`)
  and Theorem 1.3 (a continuous driver with a trace), deterministically (`mem_barrierRegion_of_frontier`): a point of
  `ℍ` off the walks lies in its own component of `ℍ \ (R ∪ L)`, which is a between-component; a real point `x > 0` off
  `R` has a half-disc missing `R`, all of whose points are on the right of `R` (`x` is a positive real point off `R`
  in the closure of their component), and the counterflow, which is not real on any time interval
  (`Sec5.exists_mem_fwdHull_sdiff`), would enter that half-disc right after visiting `x`; likewise for `x < 0` and
  `L`; `x = 0` is no physical point of the counterflow.

## What remains (new named inputs, stated for every parametrization of the walks by complete simple flows)

* `WalkContactOrderRegStatement`: the common contacts have the same order along the two walks;
* `WalkPocketShapeRegStatement`: `GW4Reg.WalkPocketShape` (two-arc pockets, the chart exit, non-overlap);
* `CounterflowWallOrderRegStatement`: every generating trace of the counterflow visits both walks in strict reverse
  first-visit order (GW2a's "contained in the counterflow range in reverse first-visit order", GB6's first contacts).

## Main results

* `mem_barrierRegion_of_frontier` (deterministic);
* **`gw4BarrierSelfRegStatement_of_walks`**: `GW4BarrierSelfRegStatement` from Theorem 1.3, the two walks'
  properness, the no-common-continuum input, SB's frontiers and the three new inputs;
  `gw4BarrierPocketRegStatement_of_walks` (through PROVE-T14-GW4T3's transfer to the conditional law).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4BarrierSelf

open GW4Traverse GW4Ident GW4Reg

/-! ### (GB11.B) from the frontier statement -/

/-- The points of `ℍ` near a real point `x > 0` off a closed set `R` lie on the right of `R`. -/
theorem mem_rightSideOf_of_near {R : Set ℂ} {x : ℝ} (hx : 0 < x) (hxR : (x : ℂ) ∉ R) {δ : ℝ}
    (hδ : ball (x : ℂ) δ ∩ R = ∅) {z : ℂ} (hz : z ∈ ball (x : ℂ) δ ∩ H) : z ∈ rightSideOf R := by
  have hsub : ball (x : ℂ) δ ∩ H ⊆ H \ R := fun w hw => ⟨hw.2, fun hwR => (hδ ▸ ⟨hw.1, hwR⟩ : w ∈ (∅ : Set ℂ))⟩
  have hcomp := (HalfPlaneSep.isPreconnected_ball_inter_H (x : ℂ) δ).subset_connectedComponentIn hz hsub
  refine ⟨hsub hz, x, hx, hxR, closure_mono hcomp ?_⟩
  have h1 : |x - x| < δ := by
    rw [sub_self, abs_zero]
    exact lt_of_le_of_lt dist_nonneg (mem_ball.1 hz.1)
  exact GB11Conn.ofReal_mem_closure_ball_inter_H h1

/-- The points of `ℍ` near a real point `x < 0` off a closed set `L` lie on the left of `L`. -/
theorem mem_leftSideOf_of_near {L : Set ℂ} {x : ℝ} (hx : x < 0) (hxL : (x : ℂ) ∉ L) {δ : ℝ}
    (hδ : ball (x : ℂ) δ ∩ L = ∅) {z : ℂ} (hz : z ∈ ball (x : ℂ) δ ∩ H) : z ∈ leftSideOf L := by
  have hsub : ball (x : ℂ) δ ∩ H ⊆ H \ L := fun w hw => ⟨hw.2, fun hwL => (hδ ▸ ⟨hw.1, hwL⟩ : w ∈ (∅ : Set ℂ))⟩
  have hcomp := (HalfPlaneSep.isPreconnected_ball_inter_H (x : ℂ) δ).subset_connectedComponentIn hz hsub
  refine ⟨hsub hz, x, hx, hxL, closure_mono hcomp ?_⟩
  have h1 : |x - x| < δ := by
    rw [sub_self, abs_zero]
    exact lt_of_le_of_lt dist_nonneg (mem_ball.1 hz.1)
  exact GB11Conn.ofReal_mem_closure_ball_inter_H h1

/-- **(GB11.B) from the frontier statement** (deterministic). For a continuous driver `W` from `0` with a generating
trace `γ` on `[0, ∞]` and closed sets `R`, `L`: if the completed counterflow range misses the right side of `R` and
the left side of `L`, every finite physical counterflow point `−1/γ(t)` lies in `R ∪ L ∪ ⋃ betweenComponents R L`. -/
theorem mem_barrierRegion_of_frontier {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hγ : IsGeneratingTrace W ⊤ γ) {R L : Set ℂ} (hR : IsClosed R) (hL : IsClosed L)
    (hfR : counterflowCompletedRange W ∩ rightSideOf R = ∅) (hfL : counterflowCompletedRange W ∩ leftSideOf L = ∅)
    (t : ℝ≥0) (ht : γ t ≠ 0) : -(γ t)⁻¹ ∈ R ∪ L ∪ ⋃₀ betweenComponents R L := by
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  have hrange : ∀ s, γ s ≠ 0 → -(γ s)⁻¹ ∈ counterflowCompletedRange W := fun s hs => by
    unfold counterflowCompletedRange
    rw [CounterflowRange.tipSet_infinitySourceChart_top hγ hW hW0]
    exact Or.inl ⟨s, hs, rfl⟩
  set p := -(γ t)⁻¹ with hp
  by_cases hpRL : p ∈ R ∪ L
  · exact Or.inl hpRL
  refine Or.inr ?_
  by_cases hpH : p ∈ H
  · refine ⟨connectedComponentIn (H \ (R ∪ L)) p, ⟨p, ⟨hpH, hpRL⟩, fun h => ?_, fun h => ?_, rfl⟩,
      mem_connectedComponentIn ⟨hpH, hpRL⟩⟩
    · exact eq_empty_iff_forall_notMem.1 hfR p ⟨hrange t ht, h⟩
    · exact eq_empty_iff_forall_notMem.1 hfL p ⟨hrange t ht, h⟩
  exfalso
  have hpHbar : p ∈ Hbar := GW2aPiece.neg_inv_mem_Hbar (GW2aPiece.trace_mem_Hbar hγ hW hW0 t)
  have him : p.im = 0 := le_antisymm (not_lt.1 hpH) hpHbar
  set x := p.re with hxdef
  have hpx : p = (x : ℂ) := Complex.ext (by simp [hxdef]) (by simp [him])
  have hp0 : p ≠ 0 := neg_ne_zero.2 (inv_ne_zero ht)
  have hx0 : x ≠ 0 := fun h => hp0 (by rw [hpx, h, Complex.ofReal_zero])
  have hcont : ContinuousAt (fun s => -(γ s)⁻¹) t := (hγc.continuousAt.inv₀ ht).neg
  -- a later time at which the trace is in `ℍ` and the physical point is near `p`
  have hlater : ∀ δ > (0 : ℝ), ∃ v : ℝ≥0, γ v ≠ 0 ∧ -(γ v)⁻¹ ∈ ball (x : ℂ) δ ∩ H := by
    intro δ hδ
    obtain ⟨η, hη, hηs⟩ := Metric.continuousAt_iff.1 hcont δ hδ
    have htt : t < t + (η / 2).toNNReal := lt_add_of_pos_right t (Real.toNNReal_pos.2 (half_pos hη))
    obtain ⟨v, htv, hvb, hvK⟩ := Sec5.exists_mem_fwdHull_sdiff hW hW0 hγ htt
    have hvH : γ v ∈ H := hvK.1.1
    have hdist : dist v t < η := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 htv.le))]
      have h1 : (v : ℝ) ≤ t + η / 2 := by
        have := NNReal.coe_le_coe.2 hvb
        rwa [NNReal.coe_add, Real.coe_toNNReal _ (half_pos hη).le] at this
      linarith
    refine ⟨v, ne_zero_of_mem_H' hvH, ?_, negInv_mem_H' hvH⟩
    rw [mem_ball, ← hpx]
    exact hηs hdist
  rcases lt_or_gt_of_ne hx0 with hxn | hxp
  · have hxL : (x : ℂ) ∉ L := fun h => hpRL (Or.inr (hpx ▸ h))
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hL.isOpen_compl (x : ℂ) hxL
    have hδL : ball (x : ℂ) δ ∩ L = ∅ := eq_empty_of_forall_notMem fun w hw => hball hw.1 hw.2
    obtain ⟨v, hv0, hz⟩ := hlater δ hδ
    exact eq_empty_iff_forall_notMem.1 hfL _ ⟨hrange v hv0, mem_leftSideOf_of_near hxn hxL hδL hz⟩
  · have hxR : (x : ℂ) ∉ R := fun h => hpRL (Or.inl (hpx ▸ h))
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hR.isOpen_compl (x : ℂ) hxR
    have hδR : ball (x : ℂ) δ ∩ R = ∅ := eq_empty_of_forall_notMem fun w hw => hball hw.1 hw.2
    obtain ⟨v, hv0, hz⟩ := hlater δ hδ
    exact eq_empty_iff_forall_notMem.1 hfR _ ⟨hrange v hv0, mem_rightSideOf_of_near hxp hxR hδR hz⟩

/-! ### The new named inputs -/

/-- **Named input: the common contacts of the two walks are in the same order along both** (GB11's barrier input,
p. 555: "their common contacts have the same order along the two curves"; Theorem GW4's proof, p. 637: "the
ordered-contact Jordan argument"), for every parametrization of the walks by complete simple flows, R51 form. -/
def WalkContactOrderRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P, ∀ αR αL : ℝ≥0 → ℂ,
        range αR = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) →
        range αL = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) →
        GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
          ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')

/-- **Named input: the pocket shape of the two walks** (`GW4Reg.WalkPocketShape`: two-arc pockets between consecutive
contacts, the chart exit, non-overlapping parameter intervals; Lemma GW3, p. 636; GB11's barrier input, p. 555), for
every parametrization of the walks by complete simple flows, R51 form. -/
def WalkPocketShapeRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P, ∀ αR αL : ℝ≥0 → ℂ,
        range αR = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) →
        range αL = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) →
        GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
          WalkPocketShape αR αL

/-- **Named input: the counterflow visits both walks in strict reverse first-visit order** (GB11's barrier input,
p. 556: "`η` contains both extreme curves in reverse first-visit order"; Lemma GW2a, p. 623: "contained in the
counterflow range in reverse first-visit order", from GB6's first contacts, `Supp8.GB6.antitone_firstVisit`), for every
parametrization of the walks by complete simple flows and every generating trace of the counterflow, R51 form. -/
def CounterflowWallOrderRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P, ∀ αR αL : ℝ≥0 → ℂ,
        range αR = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) →
        range αL = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) →
        GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
          ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ →
            (∀ s s' : ℝ≥0, 0 < s → s < s' → GB11.firstVisit γ (αR s') < GB11.firstVisit γ (αR s)) ∧
              ∀ s s' : ℝ≥0, 0 < s → s < s' → GB11.firstVisit γ (αL s') < GB11.firstVisit γ (αL s)

/-! ### The per-sample barrier input -/

/-- **GB11's barrier input for each sample** (`GW4Reg.GW4BarrierSelfRegStatement`, conditional helper): from
Theorem 1.3, GW1's properness of the two walks, the no-common-continuum input, SB's frontier statement and the three
new inputs. Complete simple flows, no common open subarc and (GB11.B) are derived here
(`mem_barrierRegion_of_frontier`). -/
theorem gw4BarrierSelfRegStatement_of_walks (h13 : Exist.Theorem13Statement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u}) (hSB : SB.SBFrontierRegStatement.{u})
    (hCO : WalkContactOrderRegStatement.{u}) (hPS : WalkPocketShapeRegStatement.{u})
    (hVO : CounterflowWallOrderRegStatement.{u}) : GW4BarrierSelfRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hCO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hVO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ'] with ω hR hL hN hS hC hP hV htr
  obtain ⟨αR, hpR, hR0, hrR⟩ := hR
  obtain ⟨αL, hpL, hL0, hrL⟩ := hL
  have hfR : GB11.IsCompleteSimpleFlow αR := ⟨hpR.1, hpR.2.1, hR0, hpR.2.2.1, hpR.2.2.2⟩
  have hfL : GB11.IsCompleteSimpleFlow αL := ⟨hpL.1, hpL.2.1, hL0, hpL.2.2.1, hpL.2.2.2⟩
  obtain ⟨hW'c, hW'0, -⟩ := htr
  refine ⟨αR, αL, hrR, hrL, hfR, hfL, hP αR αL hrR hrL hfR hfL, fun γ hγ => ?_⟩
  obtain ⟨hVR, hVL⟩ := hV αR αL hrR hrL hfR hfL γ hγ
  refine ⟨hfR, hfL, hC αR αL hrR hrL hfR hfL, fun a b' hab hsub => ?_, fun t ht => ?_, hVR, hVL⟩
  · have hS' : αR '' Icc a b' ⊆ range αR ∩ range αL := fun z hz => ⟨image_subset_range _ _ hz, hsub hz⟩
    rw [hrR, hrL] at hS'
    have hsing := hN (αR '' Icc a b') hS' (isPreconnected_Icc.image _ hfR.1.continuousOn)
    have he := hsing ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩ ⟨b', ⟨hab.le, le_rfl⟩, rfl⟩
    exact absurd (hfR.2.1 he) hab.ne
  · rw [← hrR, ← hrL] at hS
    exact mem_barrierRegion_of_frontier hW'c hW'0 hγ (isClosed_range_of_isCompleteSimpleFlow hfR)
      (isClosed_range_of_isCompleteSimpleFlow hfL) hS.1 hS.2 t ht

/-- **GB11's barrier input under the conditional law** (`GW4Reg.GW4BarrierPocketRegStatement`, conditional helper),
through PROVE-T14-GW4T3's transfer `gw4BarrierPocketRegStatement_of_self`. -/
theorem gw4BarrierPocketRegStatement_of_walks (h13 : Exist.Theorem13Statement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u}) (hSB : SB.SBFrontierRegStatement.{u})
    (hCO : WalkContactOrderRegStatement.{u}) (hPS : WalkPocketShapeRegStatement.{u})
    (hVO : CounterflowWallOrderRegStatement.{u}) : GW4BarrierPocketRegStatement.{u} :=
  gw4BarrierPocketRegStatement_of_self (gw4BarrierSelfRegStatement_of_walks h13 hPR hPL hNC hSB hCO hPS hVO)

end GW4BarrierSelf

end Theorem14

end InteractingSLE
