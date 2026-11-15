/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RkTop
import InteractingSLE.Spec.Supplement.GW2BvShare
import InteractingSLE.Spec.Supplement.GW2BvExit

/-!
# The top's single package on the rightward selection (decision D61)

PROVE-GW2-ROOTX round 12. D61: one package for `hwords`, `hshell` and `hnearImg`, on BUF's rightward selection
`withNearSB` (D37 (A)). The package **`pkgOne ψx Ex K₀ kSel k`** is

  `withNearSB (withShell (pkgXk ver cwSrc Kb k) (rjShells ver cwSrc)) nearLam (pkgNb h13 cwSrc) (kSel k)`

with:
* `ver = oneVer ψx = GW2Bh.pkgVer h13 ψx`: RELDET's death family re-indexed by BUF's `pkgPsi` (the cover
  re-indexing and the monotone hull of the extra re-indexing `ψx`, D45 (1));
* `Kb = oneKb ψx Ex K₀ = GW2Bh.pkgKb h13 h12 ψx cwSrc Ex K₀`: BUF's near stops for the exit rules `Ex` on `K₀`;
* the near base `oneNb = GW2Bh.pkgNb h13 cwSrc` (BUF's reference base word);
* the slow shells: ROOTX's `rjShell` (D33).

So its near data are BUF's `pkgB` (`nearData_pkgOne`, by `rfl`), and its slow shells are ROOTX's. Proved:
* `sameSlots_pkgOne` (`hs`), `slowShell_pkgOne` (`hsh` of `theorem14Statement_assembled7Wm_shell`);
* **`hshell_pkgOne`** (`hshell`): D33's shell field for the package, any gap family;
* **`vwordsX_pkgOne`** (`hwords`, rightward form): `GW2Bh.vwordsX_withNearSB` with BUF's near words
  (`ae_nearWords_pkg`), the rightward structure (`ae_nearStructBot_pkgNb`) and ROOTX's slow words
  (`GW2Rk.frameNSlowWordN_rjShell` with BUF's coverage `hcov_pkgVer`);
* **`nearStopsX_pkgOne`** (`hnear`): BUF's `nearStopsX_pkgKb` for measurable path-rule exits;
* **`nearData_pkgOne`**: the near data of `pkgOne (psiGoodFam) exitB` are those of BUF's final package `pkgF`, so
  BUF's `vNearImgOn_of_nearData` gives `hnearImg` for `pkgOne`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Wire.T14Rm

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj T14Rk

/-- **The top's version family**: BUF's re-indexed death family with the extra re-indexing `ψx`. -/
abbrev oneVer (ψx : GW2Bh.PsiFam.{u}) : GW2Rv.SchedVerXFamily.{u} := GW2Bh.pkgVer T14Asm7.h13 ψx

/-- **The top's base packages**: BUF's near stops for the exit rules `Ex` on the base `K₀` (every buffer index). -/
abbrev oneKb (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u}) :
    ℕ → GW2Sde.PkgFamily.{u} :=
  fun _ => GW2Bh.pkgKb T14Asm7.h13 T14Asm7.h12 ψx GW2Bh.cwSrc Ex K₀

/-- **The top's near base**: BUF's base word of the reference prefix record. -/
abbrev oneNb : NearBase.{u} := GW2Bh.pkgNb T14Asm7.h13 GW2Bh.cwSrc

/-- **The top's single package** at buffer index `k` (D61): ROOTX's `pkgX` on BUF's re-indexed death family and
near stops, with ROOTX's slow shells `rjShell` and BUF's rightward near selection on `oneNb`. -/
abbrev pkgOne (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u})
    (kSel : GW2Bh.NearSelB.{u}) (k : ℕ) : GW2Sdx.VPkgXFamily.{u} :=
  GW2Bh.withNearSB (withShell (pkgXk (oneVer ψx) GW2Bh.cwSrc (oneKb ψx Ex K₀) k) (rjShells (oneVer ψx) GW2Bh.cwSrc))
    GW2Sdh.nearLam oneNb (kSel k)

variable (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})

/-- **The package has the slots of ROOTX's package** (the top's `hs`). -/
theorem sameSlots_pkgOne (k : ℕ) :
    GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 (oneVer ψx) (chL (baseWm GW2Bh.cwSrc)) (oneKb ψx Ex K₀ k))
      (pkgOne ψx Ex K₀ kSel k) :=
  fun _ _ _ _ _ => ⟨rfl, rfl⟩

/-- **The package's slow shells are D33's** (the `hsh` of `theorem14Statement_assembled7Wm_shell`). -/
theorem slowShell_pkgOne (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (pkgOne ψx Ex K₀ kSel k Ω c r).slowShell l a ω =
      GW2Rj.rjShell T14Asm7.h13 (oneVer ψx) (GW2Bh.cwSrc Ω c r) c r l a ω :=
  rfl

/-- **The package's near data are BUF's final package's** (the `hV` of `GW2Bh.vNearImgOn_of_nearData`). -/
theorem nearData_pkgOne (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    (pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel k Ω c r).nearFamily =
        (GW2Bh.pkgF T14Asm7.h13 T14Asm7.h12 K₀ kSel k Ω c r).nearFamily ∧
      (pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel k Ω c r).nearCandidate =
        (GW2Bh.pkgF T14Asm7.h13 T14Asm7.h12 K₀ kSel k Ω c r).nearCandidate ∧
      (pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel k Ω c r).nearVar =
        (GW2Bh.pkgF T14Asm7.h13 T14Asm7.h12 K₀ kSel k Ω c r).nearVar :=
  ⟨rfl, rfl, rfl⟩

/-- **The near stops are good** (the top's `hnear`), for exit rules that are measurable path rules. -/
theorem nearStopsX_pkgOne (hI : GW2Rv.InstInputsX T14Asm7.h13 (oneVer ψx) (chL (baseWm GW2Bh.cwSrc)))
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ),
      Supp8.GB6.HullId.IsPathRule (Ex Ω c r l n a) ∧ Measurable (Ex Ω c r l n a)) (k : ℕ) :
    GW2Rv.NearStopsX T14Asm7.h13 (oneVer ψx) (chL (baseWm GW2Bh.cwSrc)) (oneKb ψx Ex K₀ k) :=
  GW2Bh.nearStopsX_pkgKb T14Asm7.h13 T14Asm7.h12 ψx GW2Bh.cwSrc Ex K₀ hI hE

/-- **`hshell` for the single package**: D33's shell field (`GW2Rj.rjShell_fact_scaled`) at buffer index `0`, for
any gap family; `hI` is the top's instance inputs (`GW2Rd.instInputsX_of_linesX_mean` with `hmeanF`, `hno`). -/
theorem hshell_pkgOne (hI : GW2Rv.InstInputsX T14Asm7.h13 (oneVer ψx) (chL (baseWm GW2Bh.cwSrc)))
    (gap : RootCv.GapFamily.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
          GW2Sdy.ShellFactLe c.κ (rjDrift GW2Bh.cwSrc Ω c r) ((pkgOne ψx Ex K₀ kSel 0 Ω c r).slowShell l a ω) ∧
            ((pkgOne ψx Ex K₀ kSel 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω := by
  intro Ω _ _ c r k l hl a
  exact GW2Rj.rjShell_fact_scaled (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀ hI GW2Bh.cwSrc
    (hβ_baseWm GW2Bh.cwSrc) (hE₀eq_baseWm GW2Bh.cwSrc) gap Ω c r k l hl a

/-- **`hwords` for the single package** (rightward form): BUF's near words and rightward structure, ROOTX's slow
words for `rjShell` with BUF's coverage. -/
theorem vwordsX_pkgOne (hI : GW2Rv.InstInputsX T14Asm7.h13 (oneVer ψx) (chL (baseWm GW2Bh.cwSrc))) (k : ℕ) :
    GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (pkgOne ψx Ex K₀ kSel k) GW2Sdh.nearLam := by
  have hslow := GW2Rk.frameNSlowWordN_rjShell
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀ hI
    GW2Sdq.gapFam GW2Sdh.nearLam GW2Bh.cwSrc (hβ_baseWm GW2Bh.cwSrc) (hE₀eq_baseWm GW2Bh.cwSrc)
    (GW2Bh.hcov_pkgVer T14Asm7.h13 ψx)
    (withShell (pkgXk (oneVer ψx) GW2Bh.cwSrc (oneKb ψx Ex K₀) k) (rjShells (oneVer ψx) GW2Bh.cwSrc))
    (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl)
  refine GW2Bh.vwordsX_withNearSB _ GW2Sdh.nearLam oneNb (kSel k) GW2Sdh.nearLam_ne (fun Ω _ _ c r l => ?_)
    (fun Ω _ _ c r l => GW2Bh.ae_nearStructBot_pkgNb T14Asm7.h13 Ω c r l) hslow
  filter_upwards [GW2Bh.ae_nearWords_pkg T14Asm7.h13 T14Asm7.h12 ψx GW2Bh.cwSrc Ex K₀ GW2Sdq.gapFam Ω c r l]
    with ω hω halive n
  filter_upwards [hω halive n] with m hm i j
  obtain ⟨h1, h2⟩ := hm (Nat.pair i j)
  refine ⟨h1, h2.trans ?_⟩
  rw [GW2Sdy.candidateAngle_pair]

end InteractingSLE.Wire.T14Rm
