/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsSector
import InteractingSLE.Spec.Supplement.WalkIntRunChronDirection

/-!
# The walk chronology from Theorem 1.3, and the orientation of component charts

Packet PROVE-WALK-WORDS. PROVE-T14-WALKINT's `WalkIntRunChron.recorded_piece_clock_order_of_mem` orders every
recorded piece's own time like the parameter of any full proper walk, given per-launch piece simplicity and connector
clearance; both are discharged from Theorem 1.3 exactly as in `WalkIntRunChron.ae_recorded_piece_direction`
(GW1's D.4 geometry, tip coordinates and exit classification). This gives the named input
`WalkPieceChronologyStatement` (`walkPieceChronologyStatement_of_theorem13`), hence
**`walkComponentOrientationStatement_of_theorem13`**: `WalkComponentOrientationStatement` from Theorem 1.3 and the five
named inputs of `GW3SidedProof.gw3GeometryRegStatement_of_walks`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkWords

open GW1WalkChain GW1Bookkeep GW1WalkFinish GW1ParamEvery Exist Exist.Staged Exist.StagedLaw
open WalkBdry WalkMean WalkNorm WalkInf WalkIntOrient WalkIntRunChron

/-- One walk's chronology from the clock order of its recorded pieces. -/
theorem lt_of_clock_order {γ : ℝ≥0 → ℂ} (hγ : GB11.IsCompleteSimpleFlow γ) {pc : Piece}
    (ho : ∀ (s t : ℝ≥0) (z w : ℂ), (s : ℝ≥0∞) ≤ pc.2.2 → (t : ℝ≥0∞) ≤ pc.2.2 →
      pc.1.tipAt pc.2.1 s z → pc.1.tipAt pc.2.1 t w → (s < t ↔ curveTime γ z < curveTime γ w))
    {t t' u u' : ℝ≥0} {z z' : ℂ} (ht' : (t' : ℝ≥0∞) ≤ pc.2.2) (hz : pc.1.tipAt pc.2.1 t z)
    (hz' : pc.1.tipAt pc.2.1 t' z') (hu : γ u = z) (hu' : γ u' = z') (htt' : t < t') : u < u' := by
  have ht : (t : ℝ≥0∞) ≤ pc.2.2 := (ENNReal.coe_le_coe.2 htt'.le).trans ht'
  have h := (ho t t' z z' ht ht' hz hz').1 htt'
  have e1 : curveTime γ z = u := hγ.2.1 ((apply_curveTime ⟨u, hu⟩).trans hu.symm)
  have e2 : curveTime γ z' = u' := hγ.2.1 ((apply_curveTime ⟨u', hu'⟩).trans hu'.symm)
  rwa [e1, e2] at h

/-- **The walk chronology from Theorem 1.3** (`WalkIntRunChron.recorded_piece_clock_order_of_mem`, with piece
simplicity at launch and connector clearance discharged as in `WalkIntRunChron.ae_recorded_piece_direction`). -/
theorem walkPieceChronologyStatement_of_theorem13 (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) : WalkPieceChronologyStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _hR hreg _hfacts hsimple
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 hT13 hT13₀
  have hTip := walkTipCoordinatesStatement_of_d4 hT13 hD4
  have hClear := walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 hT13₀) hD4
  filter_upwards [hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hsimple] with ω hTipR hTipL hClearR hClearL hs
  refine ⟨fun γ hrγ hγ pc hpc t t' u u' z z' ht' hz hz' hu hu' htt' => ?_,
    fun γ hrγ hγ pc hpc t t' u u' z z' ht' hz hz' hu hu' htt' => ?_⟩
  · have hpγ : Supp9B.IsProperCurve γ := ⟨hγ.1, hγ.2.1, hγ.2.2.2.1, hγ.2.2.2.2⟩
    exact lt_of_clock_order hγ (recorded_piece_clock_order_of_mem
      (fun k c θ' hl hseed => pieceSimpleAt_at_launch _ _ (hs true) hTipR hl hseed)
      hClearR hpγ hγ.2.2.1 hrγ hpc) ht' hz hz' hu hu' htt'
  · have hpγ : Supp9B.IsProperCurve γ := ⟨hγ.1, hγ.2.1, hγ.2.2.2.1, hγ.2.2.2.2⟩
    exact lt_of_clock_order hγ (recorded_piece_clock_order_of_mem
      (fun k c θ' hl hseed => pieceSimpleAt_at_launch _ _ (hs false) hTipL hl hseed)
      hClearL hpγ hγ.2.2.1 hrγ hpc) ht' hz hz' hu hu' htt'

/-- **`WalkComponentOrientationStatement` from Theorem 1.3** and the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks`. -/
theorem walkComponentOrientationStatement_of_theorem13 (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) :
    WalkComponentOrientationStatement.{u} :=
  walkComponentOrientationStatement_of_walks hPR hPL hA hF hNR (walkPieceChronologyStatement_of_theorem13 hT13 hT13₀)

/-- **`WalkCentralMatchStatement` from Theorem 1.3** and the same five named inputs. -/
theorem walkCentralMatchStatement_of_theorem13 (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) :
    WalkCentralMatchStatement.{u} :=
  walkCentralMatchStatement_of_orientation
    (walkComponentOrientationStatement_of_theorem13 hT13 hT13₀ hPR hPL hA hF hNR)

end InteractingSLE.Theorem14.WalkWords
