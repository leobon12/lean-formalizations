/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerDWire
import InteractingSLE.Spec.Supplement.AStopSafeFst
import InteractingSLE.Spec.Supplement.AStopPathCanon
import InteractingSLE.Spec.Supplement.Aux85Junction
import InteractingSLE.Spec.Supplement.RetZoneMean
import InteractingSLE.Spec.Wire.RetMatchExplicitWire
import InteractingSLE.Spec.Coupling.WFSLeafDualNAssembly
import InteractingSLE.Spec.ZhanGT4.StopInvBCore
import InteractingSLE.Spec.ZhanGT4.A1RLawStmt
import InteractingSLE.Spec.ZhanGT4.A1G3RRMain
import InteractingSLE.Spec.ZhanGT4.A1ERecWire
import InteractingSLE.Spec.Sec5.TwoMarkTrace12Assembly
import InteractingSLE.Spec.Sec5.FwdNoEastTWire

/-!
# Theorem 1.5 assembled: the leaves

Packet PROVE-T15-ASSEMBLE. Each leaf of `Wire.theorem15Statement_lateD_expanded` (PROVE-T15-FCKER4) is discharged
here from Lemma 7.5, Theorems 1.2–1.3, Zhan's A.1 and the fibre cover of Prop. 5.1's (E1), using only landed results:

* **leaf 3** `RLC.RetOrdDetStatement` from Lemma 7.5 and Theorem 1.3 (`retOrdDetStatement_of_lemma75`):
  PROVE-T15-ASTOP-SAFE's `retOrdDetStatement_of_lemma75_path` with PROVE-T15-ASTOP-PATH's two pathwise statements
  (`aStopPathCanonFstStatement_of_lemma75`, `aStopPathCanonSndStatement`, verbatim SAFE's
  `AStopPath{Fst,Snd}Statement`);
* the retained conditional determination `RLC.RetainedCanonCondDetHistStatement` from Lemma 7.5 and Theorem 1.3
  (`retainedCanonCondDetHistStatement_of_lemma75`): Aux. 85's touching zones (`RLC.Aux85.retTouchZonesStatement`),
  Aux. 82's collar mean (`RLC.retCollarMeanStatement_of_lemma75`) and leaf 3;
* Lemma 7.6's determination `Sec7.Lemma76DetRStatement` from Lemma 7.5 and Theorem 1.3 (PROVE-T15-MATCH's
  `RetMatchExplicit.lemma76DetRStatement`);
* (G5) at `16/κ` from A.1's directional C laws, restricted to the parameters it is used at
  (`stoppingInverseBoundary_sixteen_div_of_dirsC`); Eight's large direction is PROVE-A1-EIGHTREC's
  `A1ERec.eightRectLawFstC` and G3's rows are `A1G3RR.g3RectRow`;
* (E1) below the critical gap from Theorem 1.3 and the dyadic fibre cover (`fwdNoEastSmallGap_of_thm13_dyCover`), with
  R5 on the negative side proved (`TwoMark.Trace12.r5NegStatement`).

R48: Theorems 1.2–1.3 enter only as hypotheses of these Theorem 1.5 leaves; nothing here feeds Theorems 1.2–1.3.
-/

set_option autoImplicit false

noncomputable section

namespace InteractingSLE.Wire.T15Asm

universe u

/-! ### Leaf 3 and the retained conditional determination -/

/-- **Theorem 1.5's leaf 3 (`RLC.RetOrdDetStatement`) from Lemma 7.5 and Theorem 1.3 alone.** -/
theorem retOrdDetStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) : RLC.RetOrdDetStatement.{u} :=
  RLC.AStopSafe.retOrdDetStatement_of_lemma75_path hL75 h13₀
    (RLC.AStopPath.aStopPathCanonFstStatement_of_lemma75 hL75) RLC.AStopPath.aStopPathCanonSndStatement

/-- **The retained conditional determination from Lemma 7.5 and Theorem 1.3 alone** (touching zones (Aux. 85),
collar mean (Aux. 82) and leaf 3). -/
theorem retainedCanonCondDetHistStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) : RLC.RetainedCanonCondDetHistStatement.{u} :=
  RLC.retainedCanonCondDetHistStatement_of_touch_det hL75
    (RLC.retTouchMeanWordStatement_of_zones_collar hL75 RLC.Aux85.retTouchZonesStatement
      (RLC.retCollarMeanStatement_of_lemma75 hL75))
    (retOrdDetStatement_of_lemma75 hL75 h13₀)

/-- **Lemma 7.6's determination from Lemma 7.5 and Theorem 1.3 alone** (PROVE-T15-MATCH). -/
theorem lemma76DetRStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) : Sec7.Lemma76DetRStatement.{u} :=
  RetMatchExplicit.lemma76DetRStatement h13₀ hL75

/-! ### (G5) from Zhan's A.1 -/

/-- **A.1's G3 core from G3's two directional C laws on `(4, 8)`** (the core is vacuous elsewhere; the rows are
`A1G3RR.g3RectRow`). -/
theorem g3Core_of_dirsC (hG3S : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawSndC κ)
    (hG3F : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawFstC κ) :
    ∀ κ : ℝ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ := fun κ h4 h8 =>
  ZhanGT4.A1RLaw.a1DualCouplingG3CoreStatement_of_dirsC (ZhanGT4.A1G3RR.g3RectRow κ) (hG3S κ h4 h8) (hG3F κ h4 h8)
    h4 h8

/-- **A.1's Eight core from Eight's small-curve directional C law on `[8, ∞)`** (the core is vacuous below `8`; the
large-curve direction is PROVE-A1-EIGHTREC's `A1ERec.eightRectLawFstC`). -/
theorem eightCore_of_sndC (hES : ∀ κ : ℝ, 8 ≤ κ → ZhanGT4.A1RLaw.EightRectLawSndC κ) :
    ∀ κ : ℝ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ := fun κ h8 =>
  ZhanGT4.A1RLaw.a1DualCouplingEightCoreStatement_of_dirsC (hES κ h8) (ZhanGT4.A1ERec.eightRectLawFstC κ) h8

/-- **(G5) at `16/κ`, `0 < κ < 4`, from A.1's directional C laws at the parameters it uses**: G3's two directions on
`(4, 8)` and Eight's small-curve direction on `[8, ∞)` (Eight's large direction is proved). -/
theorem stoppingInverseBoundary_sixteen_div_of_dirsC
    (hG3S : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawSndC κ)
    (hG3F : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawFstC κ)
    (hES : ∀ κ : ℝ, 8 ≤ κ → ZhanGT4.A1RLaw.EightRectLawSndC κ) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{u} (16 / κ) :=
  ZhanGT4.StopInvB.stoppingInverseBoundaryStatement_sixteen_div_of_core (g3Core_of_dirsC hG3S hG3F)
    (eightCore_of_sndC hES)

/-! ### (E1) below the critical gap -/

/-- **(E1) below the critical gap from Theorem 1.3 and the dyadic fibre cover** (R5 on the negative side is proved). -/
theorem fwdNoEastSmallGap_of_thm13_dyCover (h13 : Exist.Theorem13Statement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin) :
    Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u} fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂ :=
  Sec5.FwdNoEastT.fwdNoEastCrosscutTgtQOn_restrict
    (Sec5.Aux61Act.fwdNoEastCrosscutTgtQOn_of_dyCover_refWin (cfLineRegularQStatement_of_theorem13_current h13)
      hDy Sec5.TwoMark.Trace12.r5NegStatement)

/-- **(E1) below the critical gap from Theorem 1.3 and the fibre-local cover** (R5 on the negative side is proved). -/
theorem fwdNoEastSmallGap_of_thm13_localCover (h13 : Exist.Theorem13Statement.{u})
    (hcov : Sec5.Aux61UnionK.GluedLocalCoverOn.{u}) :
    Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u} fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂ :=
  Sec5.FwdNoEastT.fwdNoEastCrosscutTgtQOn_smallGap_of_thm13_localCover h13 hcov Sec5.TwoMark.Trace12.r5NegStatement

end InteractingSLE.Wire.T15Asm
