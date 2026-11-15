/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RmPkg
import InteractingSLE.Spec.Supplement.GW2SdsGap
import InteractingSLE.Spec.Supplement.GW2SdqGap

/-!
# Theorem 1.4 on the single rightward package (decision D61)

PROVE-GW2-ROOTX round 12. The current top (`theorem14Statement_assembled7Wm_shell`) on the single package
`T14Rm.pkgOne` (gap `GW2Sdq.gapFam`, counterflow word `cwSrc`):

* **`T14Rm.vNearImgOn_pkgOne K₀ kSel hI hlaw hdeath hsrc`**: `hnearImg` for `pkgOne psiGoodFam exitB` (BUF's
  `vNearImgOn_of_nearData` with `nearData_pkgOne`);
* **`Wire.theorem14Statement_assembled7Wm_one ψx Ex K₀ kSel`**: for ANY extra re-indexing `ψx`, exit rules `Ex`
  (measurable path rules), base `K₀` and selector `kSel`. Discharged: `hgap`, `hpos`, `hs`, `C`, `hshell`, `hnear`,
  `hwords`. Left: the top's instance binders `hmeanF`, `hno`, then `hnearImg` for `pkgOne` and `hTL`.
* **`Wire.theorem14Statement_assembled7Wm_oneF K₀ kSel`**: BUF's final choices `ψx := psiGoodFam`, `Ex := exitB`.
  `hnearImg` comes from BUF's `vNearImgOn_of_nearData`; what is left are BUF's consumed statements `hlaw`
  (`StageLawXStatement`), `hdeath` (`DeathThrXStatement`), `hsrc` (`SrcBoundStatement`), plus `hmeanF`, `hno`, `hTL`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire.T14Rm

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur

/-- **`hnearImg` for the single package with BUF's final choices** (`psiGoodFam`, `exitB`): BUF's
`vNearImgOn_of_nearData` with `nearData_pkgOne`. -/
theorem vNearImgOn_pkgOne (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})
    (hI : GW2Rv.InstInputsX.{u} T14Asm7.h13 (oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12))
      (chL (baseWm GW2Bh.cwSrc)))
    (hlaw : GW2Bh.StageLawXStatement.{u} T14Asm7.h13 (GW2Rd.schedVerXDeathFamily T14Asm7.h13))
    (hdeath : GW2Bh.DeathThrXStatement.{u} T14Asm7.h13 (GW2Rd.schedVerXDeathFamily T14Asm7.h13)
      (GW2Bh.pkgCh T14Asm7.h13 T14Asm7.h12 GW2Bh.cwSrc))
    (hsrc : GW2Bh.SrcBoundStatement.{u} T14Asm7.h13 T14Asm7.h12 K₀ kSel)
    (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    GW2Sdz.VNearImgOn ((pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel k).at 0)
      GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹ (aliveS GW2Sdq.gapFam Ω c r l) :=
  GW2Bh.vNearImgOn_of_nearData T14Asm7.h13 T14Asm7.h12 K₀ hI hlaw hdeath kSel hsrc
    (pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel)
    (fun k' Ω _ _ c r => nearData_pkgOne K₀ kSel k' Ω c r) k Ω c r l

end InteractingSLE.Wire.T14Rm

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj T14Rk
  T14Rm

/-- **Theorem 1.4 on the single rightward package** (D61), for any extra re-indexing, exit rules, base and
selector: `hgap`, `hpos`, `hs`, `C`, `hshell`, `hnear` and `hwords` discharged. -/
theorem theorem14Statement_assembled7Wm_one (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u})
    (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC (oneVer ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC (oneVer ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC (oneVer ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω
            (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC (oneVer ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l (rootPt r.1))
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ),
      Supp8.GB6.HullId.IsPathRule (Ex Ω c r l n a) ∧ Measurable (Ex Ω c r l n a))
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((pkgOne ψx Ex K₀ kSel k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l))
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} := by
  have hI := GW2Rd.instInputsX_of_linesX_mean (hword_baseWm GW2Bh.cwSrc) (hE₀_baseWm GW2Bh.cwSrc)
    (hbd_baseWm GW2Bh.cwSrc) hmeanF hno
  exact theorem14Statement_assembled7Wm_shell GW2Sdq.gapFam GW2Sdq.measurable_gapFam
    (fun _ _ _ c x => GW2Sds.ae_gapFam_pos c x) (oneVer ψx) GW2Bh.cwSrc hmeanF hno (oneKb ψx Ex K₀)
    (pkgOne ψx Ex K₀ kSel) (sameSlots_pkgOne ψx Ex K₀ kSel) (slowShell_pkgOne ψx Ex K₀ kSel 0)
    (nearStopsX_pkgOne ψx Ex K₀ hI hE) (vwordsX_pkgOne ψx Ex K₀ kSel hI) hnearImg hTL

/-- **Theorem 1.4 on BUF's final rightward package** (D61): `ψx := psiGoodFam`, `Ex := exitB`; `hnearImg` from
BUF's `vNearImgOn_of_nearData`. Left: BUF's consumed statements `hlaw`, `hdeath`, `hsrc`, the top's `hmeanF`,
`hno`, and `hTL`. -/
theorem theorem14Statement_assembled7Wm_oneF (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean
          ((instC (oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h).B t)
          (WholeField.centredField c.h
            (instC (oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX
            (instC (oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l
            (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX
        (instC (oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l
        (rootPt r.1))
    (hlaw : GW2Bh.StageLawXStatement.{u} T14Asm7.h13 (GW2Rd.schedVerXDeathFamily T14Asm7.h13))
    (hdeath : GW2Bh.DeathThrXStatement.{u} T14Asm7.h13 (GW2Rd.schedVerXDeathFamily T14Asm7.h13)
      (GW2Bh.pkgCh T14Asm7.h13 T14Asm7.h12 GW2Bh.cwSrc))
    (hsrc : GW2Bh.SrcBoundStatement.{u} T14Asm7.h13 T14Asm7.h12 K₀ kSel)
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} := by
  have hI := GW2Rd.instInputsX_of_linesX_mean (hword_baseWm GW2Bh.cwSrc) (hE₀_baseWm GW2Bh.cwSrc)
    (hbd_baseWm GW2Bh.cwSrc) hmeanF hno
  exact theorem14Statement_assembled7Wm_one (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel hmeanF
    hno (fun Ω _ _ c r l n a => GW2Bh.exitB_spec Ω c r l n a)
    (fun k Ω _ _ c r l => vNearImgOn_pkgOne K₀ kSel hI hlaw hdeath hsrc k Ω c r l) hTL

end InteractingSLE.Wire
