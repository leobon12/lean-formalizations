/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkTchWire
import InteractingSLE.Spec.Supplement.GW2aContDefs

/-!
# Theorem 1.4's walk chart from GW2a's containment in the R51 form

Packet PROVE-T14-ASSEMBLE4. PROVE-WALK-TOUCH's `WalkTch.walkNormChartLocStatement_of_inputs` takes GW2a's
containment in the unregularized form `Theorem14.GW2aContainmentStatement`, but Theorem 1.4's top proves only the
R51 form `GW2aCont.GW2aContainmentRegStatement` (`GW2aStep.gw2aContainmentRegStatement_of_bw1`); by ruling R51 the
unregularized form is not available for irregular staged families. Every statement on the walk-chart chain already
carries the R51 hypothesis (every staged family is `StagedPiecesRegular`), and every containment call in the landed
proofs is made at the family at hand. So the landed proofs go through with the containment applied to that
regularity (as `Wire/Thm1415LateReg.lean` does for the other containment consumers).

The `_reg` theorems below are the landed proofs verbatim, with three kinds of change only: the type of `hA`, the
regularity argument inserted into each direct containment call, and the calls to the other `_reg` theorems.

* `WalkWords.Asm4.ae_wallFacts_reg`, `walkComponentWalkOrderStatement_of_walks_reg`,
  `walkComponentLandingStatement_of_walks_reg` (from `WalkWordsSector`);
* `WalkWords.Asm4.walkComponentOrientationStatement_of_theorem13_reg` (from `WalkWordsChron`);
* `WalkWords.Asm4.walkComponentWordStatement_of_walks_reg` (from `WalkWordsJunction`);
* `WalkWd.Asm4.walkFiniteMatchClosedStatement_of_inputs_reg` (from `WalkWdClosedWire`);
* `WalkTch.Asm4.walkTouchMatchStatement_of_inputs_reg` (from `WalkTchWire`);
* **`WalkTch.Asm4.walkNormChartLocStatement_of_inputs_reg`**: Theorem 1.4's binder `hNL` from Theorem 1.3 and the
  five GW3 inputs, GW2a's containment in the R51 form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

/-! ### From `WalkWordsSector` -/

namespace InteractingSLE.Theorem14.WalkWords.Asm4

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Function Metric
open QuantumZipper (H Hbar isOpen_H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)
open GW3SidedProof

/-- *R51 form* — The per-sample wall facts `hd`, `hneg` of `GW3SidedProof.gw3GeometryRegStatement_of_walks`,
almost surely, together with `WalkBetweenFacts`. -/
theorem ae_wallFacts_reg (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : RightWalkNegRealRegStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec)) :
    ∀ᵐ ω ∂P, Disjoint (WalkMean.physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (WalkMean.walkRuns κ b jumps E ω).1)
        (leftSideOf (WalkMean.physOf (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (WalkMean.walkRuns κ b jumps E ω).2)) ∧
      ∀ x : ℝ, x < 0 →
        (x : ℂ) ∈ WalkMean.physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (WalkMean.walkRuns κ b jumps E ω).1 →
        (x : ℂ) ∈ WalkMean.physOf (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (WalkMean.walkRuns κ b jumps E ω).2 := by
  have hpi := Real.pi_pos
  have hRA := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg, hRA,
    hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hPRω hPLω hRAω hFω hNRω
  obtain ⟨γR₀, hγR₀, -, hγR₀r⟩ := hPRω
  obtain ⟨γL₀, hγL₀, hγL₀0, hγL₀r⟩ := hPLω
  have hRK : range γR₀ ⊆ counterflowCompletedRange (fun t => W' t ω₀) := hγR₀r ▸ hRAω
  have hKL := hFω.2
  rw [← hγL₀r] at hKL
  have hd₀ : Disjoint (range γR₀) (leftSideOf (range γL₀)) := by
    rw [Set.disjoint_left]
    intro z hzR hzL
    exact (Set.eq_empty_iff_forall_notMem.1 hKL) z ⟨hRK hzR, hzL⟩
  have hneg₀ := neg_real_mem_of_frontier hγR₀ (isClosed_range_of_isProperCurve hγL₀ hγL₀0) hRK hKL
    (hγR₀r ▸ hNRω)
  rw [hγR₀r, hγL₀r] at hd₀
  rw [hγR₀r, hγL₀r] at hneg₀
  exact ⟨hd₀, hneg₀⟩

/-- *R51 form* — **`WalkComponentWalkOrderStatement`** from the named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks` (both walks proper curves from `0`, GW2a's containment, SB's
frontier statement, the right walk's negative reals); the contact order and no common continuum
come from `WalkBetweenFacts`. -/
theorem walkComponentWalkOrderStatement_of_walks_reg (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : RightWalkNegRealRegStatement.{u}) :
    WalkComponentWalkOrderStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg hdrv hfacts
  filter_upwards [ae_wallFacts_reg hPR hPL hA hF hNR hκ hκ4 hb hh hcf hζ' hE hreg, hfacts] with ω₀ hw hfω
  obtain ⟨hpf, -, hnc, -⟩ := hfω
  intro C hC c hc γR γL hrR hfR hrL hfL
  exact (chartFacts_of_walls hw.1 hw.2 hnc hC hc hrR hfR hrL hfL (hpf.2.2 γR γL hrR hrL hfR hfL)).2

/-- *R51 form* — **`WalkComponentLandingStatement`** from the same named inputs. -/
theorem walkComponentLandingStatement_of_walks_reg (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : RightWalkNegRealRegStatement.{u}) :
    WalkComponentLandingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg hdrv hfacts
  filter_upwards [ae_wallFacts_reg hPR hPL hA hF hNR hκ hκ4 hb hh hcf hζ' hE hreg, hfacts] with ω₀ hw hfω
  obtain ⟨hpf, -, hnc, -⟩ := hfω
  obtain ⟨⟨γR, hγR, hγR0, hrR⟩, ⟨γL, hγL, hγL0, hrL⟩, hco⟩ := hpf
  have hfR : GB11.IsCompleteSimpleFlow γR := ⟨hγR.1, hγR.2.1, hγR0, hγR.2.2.1, hγR.2.2.2⟩
  have hfL : GB11.IsCompleteSimpleFlow γL := ⟨hγL.1, hγL.2.1, hγL0, hγL.2.2.1, hγL.2.2.2⟩
  intro C hC c hc
  exact (chartFacts_of_walls hw.1 hw.2 hnc hC hc hrR hfR hrL hfL (hco γR γL hrR hrL hfR hfL)).1

end InteractingSLE.Theorem14.WalkWords.Asm4

/-! ### From `WalkWordsChron` -/

namespace InteractingSLE.Theorem14.WalkWords.Asm4

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open GW1WalkChain GW1Bookkeep GW1WalkFinish GW1ParamEvery Exist Exist.Staged Exist.StagedLaw
open WalkBdry WalkMean WalkNorm WalkInf WalkIntOrient WalkIntRunChron

/-- *R51 form* — **`WalkComponentOrientationStatement` from Theorem 1.3** and the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks`, GW2a's containment in the R51 form. -/
theorem walkComponentOrientationStatement_of_theorem13_reg (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) :
    WalkComponentOrientationStatement.{u} :=
  walkComponentOrientationStatement_of_walkOrder (walkComponentWalkOrderStatement_of_walks_reg hPR hPL hA hF hNR)
    (walkPieceChronologyStatement_of_theorem13 hT13 hT13₀)

end InteractingSLE.Theorem14.WalkWords.Asm4

/-! ### From `WalkWordsJunction` -/

namespace InteractingSLE.Theorem14.WalkWords.Asm4

open MeasureTheory ProbabilityTheory Filter Set Topology Complex Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)
open WalkBdry WalkMean WalkNorm

/-- *R51 form* — **`WalkComponentWordStatement`** from the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks` (the landing maps), GW1 piece simplicity and regularity (piece
data), and the proper walk parametrizations. -/
theorem walkComponentWordStatement_of_walks_reg (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) :
    WalkComponentWordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  filter_upwards [walkComponentLandingStatement_of_walks_reg hPR hPL hA hF hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    E hE hR hreg hfacts, hfacts, hRR, hRL] with ω hland hfω hωR hωL
  obtain ⟨hpf, hs, -, -⟩ := hfω
  obtain ⟨⟨γR, hγR, -, hrR⟩, ⟨γL, hγL, -, hrL⟩, -⟩ := hpf
  have hpdR : ∀ pc ∈ (walkRuns κ b jumps E ω).1.1,
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α := fun pc hpc => by
    obtain ⟨pre, post, hs'⟩ := List.append_of_mem hpc
    obtain ⟨f, W, α, hd⟩ := exists_pieceData (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
      (fun k c θ hl => WalkNorm.pieceRegular_of_event hωR k c θ hl) (fun k c θ hl => hs true k c θ hl) hs'
    exact ⟨_, f, W, α, hd⟩
  have hpdL : ∀ pc ∈ (walkRuns κ b jumps E ω).2.1,
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α := fun pc hpc => by
    obtain ⟨pre, post, hs'⟩ := List.append_of_mem hpc
    obtain ⟨f, W, α, hd⟩ := exists_pieceData (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
      (fun k c θ hl => WalkNorm.pieceRegular_of_event hωL k c θ hl) (fun k c θ hl => hs false k c θ hl) hs'
    exact ⟨_, f, W, α, hd⟩
  obtain ⟨hcR, hjR⟩ := ordOf_facts (spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (s := (walkRuns κ b jumps E ω).1) hγR hrR hpdR
  obtain ⟨hcL, hjL⟩ := ordOf_facts (spec := boundaryWalkSpec b jumps (Real.pi / 2) false)
    (s := (walkRuns κ b jumps E ω).2) hγL hrL hpdL
  intro C hC c hc
  obtain ⟨ℓ, hℓc, hℓi, hℓ⟩ := hland C hC c hc
  have hℓx : ∀ x : ℝ, ∃ p : ℂ, ℓ x = p ∧
      (0 < x → p ∈ physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1) ∧
      (x < 0 → p ∈ physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) := by
    intro x
    obtain ⟨p, hp, h1, h2⟩ := hc.2.2.2.2.1 x
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ (x : ℂ).im by simp)
    exact ⟨p, tendsto_nhds_unique (hℓ x) hp, h1, h2⟩
  obtain ⟨jumpsC, hpw⟩ := exists_isPiecewiseConstant_componentWord (κ := κ) hb
    (fun z hz => mem_ordOf_or_im_eq_zero hz) (fun z hz => mem_ordOf_or_im_eq_zero hz) hcR hcL hjR hjL hℓc hℓi hℓ
    (fun x hx => by obtain ⟨p, rfl, h1, -⟩ := hℓx x; exact h1 hx)
    (fun x hx => by obtain ⟨p, rfl, -, h2⟩ := hℓx x; exact h2 hx)
  exact ⟨jumpsC, hpw, isComponentBoundaryData_componentWord jumpsC⟩

end InteractingSLE.Theorem14.WalkWords.Asm4

/-! ### From `WalkWdClosedWire` -/

namespace InteractingSLE.Theorem14.WalkWd.Asm4

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)
open WalkBdry WalkNorm WalkMean WalkInf WalkWords WalkIntFill WalkIntClosed WalkIntFiber WalkIntActive
open WalkIntOrient WalkIntNeighborhood WalkIntWall GW1WalkFinish GW1WalkChain Exist

/-- *R51 form* — **`WalkFiniteMatchClosedStatement`** from Theorem 1.3, the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks` and `WalkTouchMatchStatement` — no live-piece input. -/
theorem walkFiniteMatchClosedStatement_of_inputs_reg (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u})
    (hTouch : WalkTouchMatchStatement.{u}) : WalkFiniteMatchClosedStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hpi := Real.pi_pos
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 hT13 hT13₀
  have hTip := walkTipCoordinatesStatement_of_d4 hT13 hD4
  have hClear := walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 hT13₀) hD4
  filter_upwards [hfacts, hRR, hRL, hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true),
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false),
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    WalkWords.Asm4.walkComponentOrientationStatement_of_theorem13_reg hT13 hT13₀ hPR hPL hA hF hNR κ hκ hκ4 b jumps
      hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts,
    WalkWords.Asm4.walkComponentWordStatement_of_walks_reg hPR hPL hA hF hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf
      hζ' E hE hR hreg hfacts,
    WalkWords.Asm4.walkComponentLandingStatement_of_walks_reg hPR hPL hA hF hNR κ hκ hκ4 b jumps hb P h hh W' ζ'
      hcf hζ' E hE hR hreg hfacts,
    hTouch κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts]
    with ω hf hωR hωL hS hAR hAL hTipR hTipL hClR hClL hor hwd hld hto
  intro α β hα hβ hα0 hβ0 hrR hrL C hC
  have hfα : GB11.IsCompleteSimpleFlow α := ⟨hα.1, hα.2.1, hα0, fun t => hα.2.2.1 t, hα.2.2.2⟩
  have hfβ : GB11.IsCompleteSimpleFlow β := ⟨hβ.1, hβ.2.1, hβ0, fun t => hβ.2.2.1 t, hβ.2.2.2⟩
  have hco := hf.1.2.2 α β hrR hrL hfα hfβ
  -- the pocket shape of the two walls
  have hno : ∀ a b' : ℝ≥0, a < b' → ¬ α '' Icc a b' ⊆ range β := by
    intro a b' hab hsub
    have hS' : α '' Icc a b' ⊆ physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 ∩
        physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 :=
      fun z hz => ⟨hrR ▸ image_subset_range _ _ hz, hrL ▸ hsub hz⟩
    have hsing := hf.2.2.1 _ hS' (isPreconnected_Icc.image _ hfα.1.continuousOn)
    have he := hsing ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩ ⟨b', ⟨hab.le, le_rfl⟩, rfl⟩
    exact absurd (hfα.2.1 he) hab.ne
  have hdL : Disjoint (range β) (rightSideOf (range α)) := by
    rw [hrR, hrL, Set.disjoint_left]
    intro z hzL hzR
    exact eq_empty_iff_forall_notMem.1 hS.1 z ⟨hAL hzL, hzR⟩
  have hdR : Disjoint (range α) (leftSideOf (range β)) := by
    rw [hrR, hrL, Set.disjoint_left]
    intro z hzR hzL
    exact eq_empty_iff_forall_notMem.1 hS.2 z ⟨hAR hzR, hzL⟩
  have hgeo : ∀ C' ∈ betweenComponents (range α) (range β),
      GW3.IsTwoArcJordanComponent (range α) (range β) C' ∨ GW3.HasOrientedUniformizer (range α) (range β) C' := by
    rw [hrR, hrL]; exact hf.2.2.2
  have hW := PocketMirror.pocketShapeDetStatement α β hfα hfβ hco hno hdL hdR hgeo
  -- the component chart
  obtain ⟨c, hc⟩ := GW3.exists_isComponentChart_of_geometry (hf.2.2.2 C hC)
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  have hcc : c.IsConformal := GW3Law.isConformal_of_isComponentChart hc hCoH.1 hCoH.2
  have hdom : (c.dom : Set ℂ) = C := by rw [hcc.coe_dom, GW3Joint.image_inv_eq_of_isComponentChart hc]
  obtain ⟨ℓ, -, hℓi, hℓ⟩ := hld C hC c hc
  obtain ⟨jumpsC, hpw, hcbd⟩ := hwd C hC c hc
  obtain ⟨horR, horL⟩ := hor C hC c hc
  obtain ⟨htR, htL⟩ := hto C hC c hc
  -- the runs
  have hregR := fun k c θ hl => pieceRegular_of_event hωR k c θ hl
  have hregL := fun k c θ hl => pieceRegular_of_event hωL k c θ hl
  have hDR : ∀ k, Exist.Staged.IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) :=
    fun k => hreg _ k ω
  have hDL : ∀ k, Exist.Staged.IsRegularDriver (E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) :=
    fun k => hreg _ k ω
  have hdR' := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR
      (fun k c θ hl => hf.2.1 true k c θ hl) hs
  have hdL' := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL
      (fun k c θ hl => hf.2.1 false k c θ hl) hs
  have hpdR : ∀ pc ∈ (walkRuns κ b jumps E ω).1.1,
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α := fun pc hpc => by
    obtain ⟨pre, post, hs'⟩ := List.append_of_mem hpc
    obtain ⟨f, W, α, hd⟩ := hdR' _ _ _ hs'
    exact ⟨_, f, W, α, hd⟩
  have hpdL : ∀ pc ∈ (walkRuns κ b jumps E ω).2.1,
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α := fun pc hpc => by
    obtain ⟨pre, post, hs'⟩ := List.append_of_mem hpc
    obtain ⟨f, W, α, hd⟩ := hdL' _ _ _ hs'
    exact ⟨_, f, W, α, hd⟩
  have hfR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (-(Real.pi / 2)) true
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR hDR hs h0
  have hfL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (Real.pi / 2) false
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL hDL hs h0
  have hCsub : C ⊆ H \ (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 ∪
      physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) :=
    Sec7.Prop74B.subset_of_mem_betweenComponents hC
  have hCR : Disjoint C (wsetOf (walkRuns κ b jumps E ω).1) := Set.disjoint_left.2 fun z hz hzw =>
    (hCsub hz).2 (Or.inl (Or.inl (Or.inr hzw.1)))
  have hCL : Disjoint C (wsetOf (walkRuns κ b jumps E ω).2) := Set.disjoint_left.2 fun z hz hzw =>
    (hCsub hz).2 (Or.inr (Or.inl (Or.inr hzw.1)))
  have hcC : MapsTo c.2.1 H C := hc.2.2.1
  have hland := hc.2.2.2.2.1
  have hpH : ∀ (x : ℝ) (p : ℂ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p.im ≠ 0 → p ∈ H := by
    intro x p hp him
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
    have hbar : p ∈ Hbar := QuantumZipper.isClosed_Hbar.mem_of_tendsto hp
      (eventually_nhdsWithin_of_forall fun w hw => le_of_lt (show (0 : ℝ) < (c.2.1 w).im from hCoH.2 (hcC hw)))
    exact lt_of_le_of_ne hbar (Ne.symm him)
  -- the controlled matches
  have hctlR : ∀ (x : ℝ) (p : ℂ), 0 < x → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p ∈ ordOf (walkRuns κ b jumps E ω).1 →
      p ∉ pieceEnds (walkRuns κ b jumps E ω).1.1 → p ∉ closure (wsetOf (walkRuns κ b jumps E ω).2) →
      IsControlledMatch (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2 true c x p := by
    intro x p hx hp hpo hpE hpL
    by_cases him : p.im = 0
    · exact htR x p hx hp him hpo hpE
    · exact fun U hU hpU => exists_controlledMatch_right hdR' hfR hCR hcc hcC
        (fun x hx => by
          obtain ⟨z, hz, hzR, -⟩ := hland x
          exact ⟨z, hz, mem_ordOf_or_im_eq_zero (hzR hx)⟩) hx hp (hpH x p hp him) hU hpU hpo hpE hpL horR
  have hctlL : ∀ (x : ℝ) (p : ℂ), x < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p ∈ ordOf (walkRuns κ b jumps E ω).2 →
      p ∉ pieceEnds (walkRuns κ b jumps E ω).2.1 → p ∉ closure (wsetOf (walkRuns κ b jumps E ω).1) →
      IsControlledMatch (walkRuns κ b jumps E ω).2 (walkRuns κ b jumps E ω).1 false c x p := by
    intro x p hx hp hpo hpE hpR
    by_cases him : p.im = 0
    · exact htL x p hx hp him hpo hpE
    · exact fun U hU hpU => exists_controlledMatch_left hdL' hfL hCL hcc hcC
        (fun x hx => by
          obtain ⟨z, hz, -, hzL⟩ := hland x
          exact ⟨z, hz, mem_ordOf_or_im_eq_zero (hzL hx)⟩) hx hp (hpH x p hp him) hU hpU hpo hpE hpR horL
  -- prefixes
  obtain ⟨R₀, hR₀⟩ := exists_closedPrefix_raw_eq_empty (-(Real.pi / 2)) true _ hregR hDR hTipR
  obtain ⟨L₀, hL₀⟩ := exists_closedPrefix_raw_eq_empty (Real.pi / 2) false _ hregL hDL hTipL
  have hrawR : ∀ R : WalkPrefix (walkRuns κ b jumps E ω).1, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H := fun R =>
    WalkIntRunChron.exists_raw_initial_segment_of_run
      (fun k c θ' hl hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ (hf.2.1 true) hTipR hl hseed)
      hClR hα hα0 hrR hDR R
  have hrawL : ∀ R : WalkPrefix (walkRuns κ b jumps E ω).2, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H := fun R =>
    WalkIntRunChron.exists_raw_initial_segment_of_run
      (fun k c θ' hl hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ (hf.2.1 false) hTipL hl hseed)
      hClL hβ hβ0 hrL hDL R
  exact finite_matches_closed_of_sample hα hβ hα0 hβ0 hrR hrL hco hW hC hc hdom hℓi hℓ
    (ordOf_facts hα hrR hpdR).1 (ordOf_facts hβ hrL hpdL).1 hctlR hctlL
    (fun pre post pc hs τ hτ => exists_walkPrefix (-(Real.pi / 2)) true _ hregR hDR hs hτ)
    (fun pre post pc hs τ hτ => exists_walkPrefix (Real.pi / 2) false _ hregL hDL hs hτ)
    hrawR hrawL R₀ hR₀ L₀ hL₀ hpw hcbd

end InteractingSLE.Theorem14.WalkWd.Asm4

/-! ### From `WalkTchWire` -/

namespace InteractingSLE.Theorem14.WalkTch.Asm4

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)
open Exist WalkBdry WalkMean WalkNorm WalkInf WalkWords WalkIntFill WalkIntFiber WalkIntActive WalkWd
open GW1WalkFinish GW1WalkChain

/-- *R51 form* — **`WalkTouchMatchStatement`** from Theorem 1.3 and the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks` (see the module docstring). -/
theorem walkTouchMatchStatement_of_inputs_reg (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hA : GW2aCont.GW2aContainmentRegStatement.{u}) (hF : SB.SBFrontierRegStatement.{u})
    (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) : WalkTouchMatchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hpi := Real.pi_pos
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 hT13 hT13₀
  have hTip := walkTipCoordinatesStatement_of_d4 hT13 hD4
  have hClear := walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 hT13₀) hD4
  filter_upwards [hfacts, hRR, hRL, hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true),
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false),
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    WalkWords.Asm4.walkComponentOrientationStatement_of_theorem13_reg hT13 hT13₀ hPR hPL hA hF hNR κ hκ hκ4 b jumps
      hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts,
    hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR]
    with ω hf hωR hωL hS hAR hAL hTipR hTipL hClR hClL hor hαω hβω
  obtain ⟨α, hα, hα0, hrR⟩ := hαω
  obtain ⟨β, hβ, hβ0, hrL⟩ := hβω
  replace hrR : range α = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 := hrR
  replace hrL : range β = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 := hrL
  intro C hC c hc
  have hfα : GB11.IsCompleteSimpleFlow α := ⟨hα.1, hα.2.1, hα0, fun t => hα.2.2.1 t, hα.2.2.2⟩
  have hfβ : GB11.IsCompleteSimpleFlow β := ⟨hβ.1, hβ.2.1, hβ0, fun t => hβ.2.2.1 t, hβ.2.2.2⟩
  have hco := hf.1.2.2 α β hrR hrL hfα hfβ
  -- the pocket shape of the two walls
  have hno : ∀ a b' : ℝ≥0, a < b' → ¬ α '' Icc a b' ⊆ range β := by
    intro a b' hab hsub
    have hS' : α '' Icc a b' ⊆ physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 ∩
        physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 :=
      fun z hz => ⟨hrR ▸ image_subset_range _ _ hz, hrL ▸ hsub hz⟩
    have hsing := hf.2.2.1 _ hS' (isPreconnected_Icc.image _ hfα.1.continuousOn)
    have he := hsing ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩ ⟨b', ⟨hab.le, le_rfl⟩, rfl⟩
    exact absurd (hfα.2.1 he) hab.ne
  have hdL : Disjoint (range β) (rightSideOf (range α)) := by
    rw [hrR, hrL, Set.disjoint_left]
    intro z hzL hzR
    exact eq_empty_iff_forall_notMem.1 hS.1 z ⟨hAL hzL, hzR⟩
  have hdR : Disjoint (range α) (leftSideOf (range β)) := by
    rw [hrR, hrL, Set.disjoint_left]
    intro z hzR hzL
    exact eq_empty_iff_forall_notMem.1 hS.2 z ⟨hAR hzR, hzL⟩
  have hgeo : ∀ C' ∈ betweenComponents (range α) (range β),
      GW3.IsTwoArcJordanComponent (range α) (range β) C' ∨ GW3.HasOrientedUniformizer (range α) (range β) C' := by
    rw [hrR, hrL]; exact hf.2.2.2
  have hW := PocketMirror.pocketShapeDetStatement α β hfα hfβ hco hno hdL hdR hgeo
  have hC' : C ∈ betweenComponents (range α) (range β) := by rw [hrR, hrL]; exact hC
  have hc' : IsComponentChart (range α) (range β) C c := by rw [hrR, hrL]; exact hc
  obtain ⟨hnot, hexit⟩ := pocket_landing_facts hfα hfβ hco hW hC' hc'
  have hαc : IsClosed (range α) := GW4Reg.isClosed_range_of_isCompleteSimpleFlow hfα
  have hβc : IsClosed (range β) := GW4Reg.isClosed_range_of_isCompleteSimpleFlow hfβ
  have hwR : wsetOf (walkRuns κ b jumps E ω).1 ⊆ range α := fun z hz => hrR ▸ Or.inl (Or.inr hz.1)
  have hwL : wsetOf (walkRuns κ b jumps E ω).2 ⊆ range β := fun z hz => hrL ▸ Or.inl (Or.inr hz.1)
  have hoR : ordOf (walkRuns κ b jumps E ω).1 ⊆ range α := fun z hz => hrR ▸ Or.inl (Or.inr hz)
  have hoL : ordOf (walkRuns κ b jumps E ω).2 ⊆ range β := fun z hz => hrL ▸ Or.inl (Or.inr hz)
  -- the component chart
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  have hcc : c.IsConformal := GW3Law.isConformal_of_isComponentChart hc hCoH.1 hCoH.2
  have hcC : MapsTo c.2.1 H C := hc.2.2.1
  have hland := hc.2.2.2.2.1
  obtain ⟨horR, horL⟩ := hor C hC c hc
  -- the runs
  have hregR := fun k c θ hl => pieceRegular_of_event hωR k c θ hl
  have hregL := fun k c θ hl => pieceRegular_of_event hωL k c θ hl
  have hDR : ∀ k, Exist.Staged.IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) :=
    fun k => hreg _ k ω
  have hDL : ∀ k, Exist.Staged.IsRegularDriver (E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) :=
    fun k => hreg _ k ω
  have hdR' := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR
      (fun k c θ hl => hf.2.1 true k c θ hl) hs
  have hdL' := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL
      (fun k c θ hl => hf.2.1 false k c θ hl) hs
  have hfR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (-(Real.pi / 2)) true
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR hDR hs h0
  have hfL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (Real.pi / 2) false
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL hDL hs h0
  have hjR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntBridge.prefixChart_disjoint_prefixSet (-(Real.pi / 2)) true
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR hDR hs h0
  have hjL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntBridge.prefixChart_disjoint_prefixSet (Real.pi / 2) false
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL hDL hs h0
  have ht0R : ∀ pc ∈ (walkRuns κ b jumps E ω).1.1, ∀ z, pc.1.tipAt pc.2.1 0 z → z.im = 0 :=
    fun pc hpc z hz => im_eq_zero_of_tipAt_zero hTipR hpc hz
  have ht0L : ∀ pc ∈ (walkRuns κ b jumps E ω).2.1, ∀ z, pc.1.tipAt pc.2.1 0 z → z.im = 0 :=
    fun pc hpc z hz => im_eq_zero_of_tipAt_zero hTipL hpc hz
  have hmkR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post) (τ : ℝ≥0)
      (hτ : (τ : ℝ≥0∞) < pc.2.2) => exists_walkPrefix (-(Real.pi / 2)) true _ hregR hDR hs hτ
  have hmkL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post) (τ : ℝ≥0)
      (hτ : (τ : ℝ≥0∞) < pc.2.2) => exists_walkPrefix (Real.pi / 2) false _ hregL hDL hs hτ
  have hrawR : ∀ R : WalkPrefix (walkRuns κ b jumps E ω).1, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H := fun R =>
    WalkIntRunChron.exists_raw_initial_segment_of_run
      (fun k c θ' hl hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ (hf.2.1 true) hTipR hl hseed)
      hClR hα hα0 hrR hDR R
  have hrawL : ∀ R : WalkPrefix (walkRuns κ b jumps E ω).2, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H := fun R =>
    WalkIntRunChron.exists_raw_initial_segment_of_run
      (fun k c θ' hl hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ (hf.2.1 false) hTipL hl hseed)
      hClL hβ hβ0 hrL hDL R
  refine ⟨fun x p hx hp him hpo hpE => ?_, fun x p hx hp him hpo hpE => ?_⟩
  · -- the right walk
    have hpα : p ∈ range α := hoR hpo
    have hpL : p ∉ closure (wsetOf (walkRuns κ b jumps E ω).2) := fun h =>
      (hnot x p hp).1 hx (closure_minimal hwL hβc h)
    obtain ⟨U₀, hU₀, hpU₀, hdomR⟩ := exists_dom_window_right hα hβ hα0 hβ0 hrR hrL hco hC hCoH.1 hcC hpα
      hmkR hrawR fun hb => by
        obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
        exact ⟨U, V, hUV, hUC, (hlt x p hp).1⟩
    exact fun U hU hpU => exists_controlledMatch_right_touch hα hoR hdR' hfR hjR ht0R hcc
      (fun x' hx' => by
        obtain ⟨z, hz, hzR, -⟩ := hland x'
        exact ⟨z, hz, hrR ▸ hzR hx'⟩) hx hp him hU hpU hpo hpE hpL horR hU₀ hpU₀ hdomR
  · -- the left walk
    have hpβ : p ∈ range β := hoL hpo
    have hpR : p ∉ closure (wsetOf (walkRuns κ b jumps E ω).1) := fun h =>
      (hnot x p hp).2 hx (closure_minimal hwR hαc h)
    obtain ⟨U₀, hU₀, hpU₀, hdomL⟩ := exists_dom_window_left hα hβ hα0 hβ0 hrR hrL hco hC hCoH.1 hcC hpβ
      hmkL hrawL fun hb => by
        obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
        exact ⟨U, V, hUV, hUC, (hlt x p hp).2⟩
    exact fun U hU hpU => exists_controlledMatch_left_touch hβ hoL hdL' hfL hjL ht0L hcc
      (fun x' hx' => by
        obtain ⟨z, hz, -, hzL⟩ := hland x'
        exact ⟨z, hz, hrL ▸ hzL hx'⟩) hx hp him hU hpU hpo hpE hpR horL hU₀ hpU₀ hdomL

/-- **Theorem 1.4's walk chart `hNL`** (`WalkNorm.WalkNormChartLocStatement`) from Theorem 1.3 and the five GW3
inputs, GW2a's containment in the R51 form (`WalkTch.walkNormChartLocStatement_of_inputs` with the containment
applied to regular staged families). -/
theorem walkNormChartLocStatement_of_inputs_reg (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) :
    WalkNormChartLocStatement.{u} :=
  WalkWd.walkNormChartLocStatement_of_closed_matches hT13 hT13₀
    (WalkWd.Asm4.walkFiniteMatchClosedStatement_of_inputs_reg hT13 hT13₀ hPR hPL hA hF hNR
      (walkTouchMatchStatement_of_inputs_reg hT13 hT13₀ hPR hPL hA hF hNR))

end InteractingSLE.Theorem14.WalkTch.Asm4
