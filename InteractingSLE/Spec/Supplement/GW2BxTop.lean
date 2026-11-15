/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxMain
import InteractingSLE.Spec.Supplement.GW2RePkg

/-!
# nearImg for ROOTX's stop package on the guarded base (decision D75)

Packet PROVE-GW2-BUF (round 21). D75: the top's family is ROOTX's `oneVerS` (NOTHR's stop family re-indexed), on
ASSEMBLE7's guarded base (`T14Re.chG = chL (T14Gd.guardBase (baseWm cwSrc))`). ROOTX's `T14Re.pkgOneG ψx Ex K₀ kSel k`
has the near data of BUF's `pkgS` at `ver₀ = GW2Nx.schedVerXStopFamily T14Asm7.h13` and `ch = T14Re.chG` (its shells
do not enter nearImg). So **`hnearImg_oneG`** is `vNearImgOn_pkgS` there, with:

* `ψx := psiGoodS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) T14Re.chG` (the goodness re-indexing),
  `Ex := exitB`, `kSel := kSelBS …` (BUF's selection);
* the instance inputs with no hypotheses (ROOTX's `T14Re.instInputsX_oneG`), NOTHR's cover, exhaustion and caps of
  the stop family (`GW2Nx.hcov_stop`, `GW2Nx.exhStopStatement_stop`, `GW2Nx.hcaps_stop`), the guarded base's word
  map (`T14Re.hβ_guardWm`);
* the death threshold `DeathThrXStatementS3` from STAGEMEAN's datum-form death clause (`deathThrX_stopD3`).

Remaining inputs (consumed as stated, by owner): RELDET's stopped stage law `GW2Rd.StageLawXSStatement` on the stop
family (D71), STAGEMEAN's datum-form death clause `GW2Ny.DeathExportFamilyD` on the stop family and `chG`, and
NEARIMG2's uncapped stage law `GW2Ni.StageLawUXStatement`.

* **`hnearImg_oneG`**, **`theorem14Statement_oneG_nearImg`** (ROOTX's top with `hnearImg` discharged).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Wire.T14Bx

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Re

/-- The guarded base's word map is GEOM2's base word raised by the candidate's angle. -/
theorem hβ_chG (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (y : Exist.StagedLaw.RecData) :
    (chG Ω c r l a).β y = GW2Rd.upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
      (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) y) := by
  rw [hβ_guardWm]
  show GW2Wm.schedWordMapX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
    ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) (GW2Rd.candAngle c r l a) y = _
  unfold GW2Wm.schedWordMapX
  rw [GW2Rj.candAngle_eq]

/-- **The top's `hnearImg` for ROOTX's stop package on the guarded base** (D75 (2)). -/
theorem hnearImg_oneG (K₀ : GW2Sde.PkgFamily.{u})
    (hlaw : GW2Rd.StageLawXSStatement.{u} T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13))
    (hexp : GW2Ny.DeathExportFamilyD.{u} T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG)
    (hlawU : GW2Ni.StageLawUXStatement.{u}) (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    GW2Sdz.VNearImgOn ((pkgOneG (GW2Bh.psiGoodS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG)
        GW2Bh.exitB K₀ (GW2Bh.kSelBS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG K₀) k).at 0)
      GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹ (aliveS GW2Sdq.gapFam Ω c r l) := by
  have hI : GW2Rv.InstInputsX T14Asm7.h13
      (GW2Bh.verS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG) chG :=
    instInputsX_oneG.{u} (GW2Bh.psiGoodS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG)
  have hdeath : GW2Bh.DeathThrXStatementS3 T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG :=
    GW2Bh.deathThrX_stopD3 T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ chG hI.word hexp
  exact GW2Bh.vNearImgOn_congr rfl rfl rfl
    (GW2Bh.vNearImgOn_pkgS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG K₀ hI hlaw hdeath hlawU
      (GW2Nx.hcov_stop T14Asm7.h13) (GW2Nx.exhStopStatement_stop T14Asm7.h13) (GW2Nx.hcaps_stop T14Asm7.h13)
      hβ_chG k Ω c r l)

end InteractingSLE.Wire.T14Bx

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Re

/-- **Theorem 1.4 on the guarded base with the stop package, `hnearImg` discharged** (ROOTX's
`theorem14Statement_oneG` with BUF's `ψx`, exits, selection and `T14Bx.hnearImg_oneG`). -/
theorem theorem14Statement_oneG_nearImg (K₀ : GW2Sde.PkgFamily.{u})
    (hlaw : GW2Rd.StageLawXSStatement.{u} T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13))
    (hexp : GW2Ny.DeathExportFamilyD.{u} T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG)
    (hlawU : GW2Ni.StageLawUXStatement.{u})
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_oneG (GW2Bh.psiGoodS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG) GW2Bh.exitB K₀
    (GW2Bh.kSelBS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG K₀)
    (fun Ω _ _ c r l n a => GW2Bh.exitB_spec Ω c r l n a)
    (T14Bx.hnearImg_oneG K₀ hlaw hexp hlawU) hcan hdet

end InteractingSLE.Wire
