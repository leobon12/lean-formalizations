/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ByMainG
import InteractingSLE.Spec.Supplement.GW2BxTop
import InteractingSLE.Spec.Supplement.GW2OzDth
import InteractingSLE.Spec.Supplement.GW2NqGT
import InteractingSLE.Spec.Supplement.GW2NqUnc

/-!
# The top's `hnearImg` with no open input (decision D88)

Packet PROVE-GW2-BUF (round 22). **`T14By.hnearImg_oneGC`**: the top's `hnearImg` for ROOTX's stop package on the
guarded base (`T14Re.pkgOneG` at BUF's goodness re-indexing `psiGoodS`, the exits `exitB` and BUF's selection
`kSelBS`), proved with NO hypotheses, by `vNearImgOn_pkgS3` with:

* `hlaw` — the guarded stopped stage law on the stop family, `GW2Ni.stageLawXSGTStatement_closed` (NEARIMG2, D88);
* `hlawU` — the guarded stopped uncapped law, `GW2Ni.stageLawUXSGTStatement_top` (NEARIMG2, D88; it asks fewer
  premises than nearImg supplies);
* `hdeath` — NOTHR's `GW2Oz.deathThrX3_chG`;
* the instance inputs, cover, exhaustion, caps and word map (ROOTX's `T14Re.instInputsX_oneG`, NOTHR's `hcov_stop`,
  `exhStopStatement_stop`, `hcaps_stop`, BUF's `T14Bx.hβ_chG`).

**`Wire.theorem14Statement_oneG_nearImgC`**: ROOTX's guarded top `Wire.theorem14Statement_oneG` with `hnearImg`
discharged; remaining binders SB2(2)'s `hcan`, `hdet`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire.T14By

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Re

/-- **The top's `hnearImg` with no open input** (ROOTX's stop package on the guarded base). -/
theorem hnearImg_oneGC (K₀ : GW2Sde.PkgFamily.{u}) (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    GW2Sdz.VNearImgOn ((pkgOneG (GW2Bh.psiGoodS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG)
        GW2Bh.exitB K₀ (GW2Bh.kSelBS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG K₀) k).at 0)
      GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹ (aliveS GW2Sdq.gapFam Ω c r l) := by
  have hI : GW2Rv.InstInputsX T14Asm7.h13
      (GW2Bh.verS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG) chG :=
    instInputsX_oneG.{u} (GW2Bh.psiGoodS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG)
  have hdeath : GW2Bh.DeathThrXStatementS3 T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG :=
    GW2Oz.deathThrX3_chG.{u}
  have hlaw : GW2Rd.StageLawXSGTStatement.{u} T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) :=
    GW2Ni.stageLawXSGTStatement_closed
  exact GW2Bh.vNearImgOn_congr rfl rfl rfl
    (GW2Bh.vNearImgOn_pkgS3 T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG K₀ hI hlaw hdeath
      (fun Ω _ _ c r l i hg hord hgd => (GW2Ni.stageLawUXSGTStatement_top.{u} Ω c r l i hg hord hgd).mono
        fun _ h hgx hold _ hTcu => h hgx hold hTcu)
      (GW2Nx.hcov_stop T14Asm7.h13) (GW2Nx.exhStopStatement_stop T14Asm7.h13) (GW2Nx.hcaps_stop T14Asm7.h13)
      T14Bx.hβ_chG k Ω c r l)

end InteractingSLE.Wire.T14By

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Re

/-- **Theorem 1.4 on the guarded base with the stop package, `hnearImg` discharged with no open input** (ROOTX's
`theorem14Statement_oneG` with BUF's `ψx`, exits, selection and `T14By.hnearImg_oneGC`). -/
theorem theorem14Statement_oneG_nearImgC (K₀ : GW2Sde.PkgFamily.{u})
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_oneG (GW2Bh.psiGoodS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG) GW2Bh.exitB K₀
    (GW2Bh.kSelBS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) chG K₀)
    (fun Ω _ _ c r l n a => GW2Bh.exitB_spec Ω c r l n a)
    (T14By.hnearImg_oneGC K₀) hcan hdet

end InteractingSLE.Wire
