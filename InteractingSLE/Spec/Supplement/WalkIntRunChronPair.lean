/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronPairLeaf
import InteractingSLE.Spec.Supplement.WalkWordsArc

/-!
# The pair-geometry leaf from actual-run chronology

WalkWordsArc has landed. Its bookkeeping theorem applies directly to the
actual-run direction result, with no remaining direction or arc-data input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.WalkIntRunChron

open Exist WalkBdry WalkMean WalkNorm WalkInf

variable (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})

include hT13 hT13₀

/-- The recorded pieces traverse common points in the same own-time order. -/
theorem walkPieceDirectionStatement : WalkWords.WalkPieceDirectionStatement.{u} :=
  ae_recorded_piece_direction hT13 hT13₀

/-- All common-arc data follow from the actual-run direction theorem. -/
theorem walkPairArcDataStatement : WalkWords.WalkPairArcDataStatement.{u} :=
  WalkWords.walkPairArcDataStatement_of_direction (walkPieceDirectionStatement hT13 hT13₀)

/-- The common-arc pair leaf has no remaining chronology input. -/
theorem walkPairGeomCOStatement (hS : GW1Z.GW1PieceSimpleStatement.{u}) :
    WalkPairGeomCOStatement.{u} :=
  WalkWords.walkPairGeomCOStatement_of_arcData hS (walkPairArcDataStatement hT13 hT13₀)

/-- The original pair-geometry leaf from the existing walk/contact facts. -/
theorem walkPairGeomStatement (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u}) : WalkBdry.WalkPairGeomStatement.{u} :=
  walkPairGeomStatement_of_co hCO hPR hPL (walkPairGeomCOStatement hT13 hT13₀ hS)

end InteractingSLE.Theorem14.WalkIntRunChron
