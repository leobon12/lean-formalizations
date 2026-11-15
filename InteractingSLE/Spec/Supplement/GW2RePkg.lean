/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ReSlow
import InteractingSLE.Spec.Supplement.GW2RpPkg
import InteractingSLE.Spec.Wire.T14GdTop

/-!
# The stop package on ASSEMBLE7's guarded base (D75 (3), option (G))

PROVE-GW2-ROOTX round 15. The package of D68/D75 on the guarded word-map base `T14Gd.guardBase (baseWm cwSrc)`:

  `pkgOneG ψx Ex K₀ kSel k = withNearSB (withShell (pkgX h13 (oneVerS ψx) chG (oneKbG ψx Ex K₀ k)) (rjShells …))
    nearLam (oneNbS ψx) (kSel k)`, with `chG = chL (guardBase (baseWm cwSrc))`.

* The version family is `T14Rp.oneVerS ψx` (the stop family re-indexed on its own cover events and by BUF's `ψx`;
  D75 (1)). The near base `oneNbS ψx` (`GW2Rl.refNb`) and the shells `rjShell` do not depend on the base.
* **The instance inputs, with no hypotheses**: `instInputsX_oneG ψx` (ASSEMBLE7's `instInputsX_guardBase` with ROOTX's
  `hmeanFGuarded_oneVerS`, `hnoGuarded_oneVerS`).
* The guarded base keeps the word map (`hβ_guardWm`) and has `E₀ = (launchBadRec)ᶜ` on guarded histories
  (`hE₀_guardWm`); ROOTX's guarded chains (`GW2Re*`) need no more.

Proved, with no hypothesis beyond the exits' measurability `hE`:
* `hs` (**`sameSlots_pkgOneG`**), `hsh` (`slowShell_pkgOneG`), `hnear` (**`nearStopsX_pkgOneG`**);
* `hshell` (**`hshell_pkgOneG`**, D33's drift family `rjDrift cwSrc`);
* `hwords` (**`vwordsX_pkgOneG`**);
* the tops **`Wire.T14Re.gw2RootTestStatement_oneG`** and **`Wire.theorem14Statement_oneG`**: only
  `hnearImg` for `pkgOneG` (BUF's, D75 (2)) and SB2(2)'s `hcan`, `hdet` remain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Wire.T14Re

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj T14Rk
  T14Rp

/-- **The guarded choice family**: RELDET's lines on ASSEMBLE7's guarded word-map base at BUF's word. -/
abbrev chG : GW2Sdh.SchedChoiceFamily.{u} := chL (T14Gd.guardBase (baseWm GW2Bh.cwSrc))

/-- The guarded base keeps GEOM2's word map. -/
theorem hβ_guardWm (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (chG Ω c r l a).β = GW2Wm.schedWordMapX c.κ (GW2Bh.cwSrc Ω c r) (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a) := by
  rw [GW2Rd.schedChoiceLinesX_β, T14Gd.guardBase_β]
  rfl

/-- On guarded histories the guarded base's record event is D42's. -/
theorem hE₀_guardWm (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hg : T14Gd.Guard c r l) :
    (chG Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ := by
  rw [GW2Rd.schedChoiceLinesX_E₀, T14Gd.guardBase_E₀_of_guard _ a hg]
  rfl

/-- **The top's instance inputs on the guarded base for the stop package's family, with no hypotheses.** -/
theorem instInputsX_oneG (ψx : GW2Bh.PsiFam.{u}) : GW2Rv.InstInputsX T14Asm7.h13 (oneVerS ψx) chG :=
  T14Gd.instInputsX_guardBase GW2Bh.cwSrc (hmeanFGuarded_oneVerS ψx) (hnoGuarded_oneVerS ψx)

/-- The base packages on the guarded base: BUF's near stops for the exits `Ex` on `K₀`. -/
abbrev oneKbG (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u}) :
    ℕ → GW2Sde.PkgFamily.{u} :=
  fun _ => GW2Bh.nearStopPkgX T14Asm7.h13 (oneVerS ψx) chG Ex K₀

/-- **The stop package on the guarded base** at buffer index `k`. -/
abbrev pkgOneG (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u})
    (kSel : GW2Bh.NearSelB.{u}) (k : ℕ) : GW2Sdx.VPkgXFamily.{u} :=
  GW2Bh.withNearSB (withShell (GW2Rv.pkgX T14Asm7.h13 (oneVerS ψx) chG (oneKbG ψx Ex K₀ k))
    (rjShells (oneVerS ψx) GW2Bh.cwSrc)) GW2Sdh.nearLam (oneNbS ψx) (kSel k)

variable (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})

/-- **`hs`**: the package has the slots of ROOTX's package on the guarded base. -/
theorem sameSlots_pkgOneG (k : ℕ) :
    GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 (oneVerS ψx) chG (oneKbG ψx Ex K₀ k)) (pkgOneG ψx Ex K₀ kSel k) :=
  fun _ _ _ _ _ => ⟨rfl, rfl⟩

/-- `hsh`: the package's slow shells are D33's. -/
theorem slowShell_pkgOneG (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (pkgOneG ψx Ex K₀ kSel k Ω c r).slowShell l a ω =
      GW2Rj.rjShell T14Asm7.h13 (oneVerS ψx) (GW2Bh.cwSrc Ω c r) c r l a ω :=
  rfl

/-- **`hnear`**: the near stops are good, for exits that are measurable path rules. -/
theorem nearStopsX_pkgOneG
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ),
      Supp8.GB6.HullId.IsPathRule (Ex Ω c r l n a) ∧ Measurable (Ex Ω c r l n a)) (k : ℕ) :
    GW2Rv.NearStopsX T14Asm7.h13 (oneVerS ψx) chG (oneKbG ψx Ex K₀ k) :=
  GW2Bh.nearStopsX_nearStopPkgX (instInputsX_oneG ψx) hE K₀

/-- **`hshell`**: D33's shell field at buffer index `0` (guarded chain `rjShell_fact_scaledG`), any gap family. -/
theorem hshell_pkgOneG (gap : RootCv.GapFamily.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
          GW2Sdy.ShellFactLe c.κ (rjDrift GW2Bh.cwSrc Ω c r) ((pkgOneG ψx Ex K₀ kSel 0 Ω c r).slowShell l a ω) ∧
            ((pkgOneG ψx Ex K₀ kSel 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω := by
  intro Ω _ _ c r k l hl a
  exact GW2Rj.rjShell_fact_scaledG (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀
    (instInputsX_oneG ψx) GW2Bh.cwSrc hβ_guardWm hE₀_guardWm gap Ω c r k l hl a

/-- **`hwords`** (rightward form): ROOTX's guarded near words (`ae_nearSlotWordsG`, uniform cover `unifCover_verU`),
the rightward structure (`GW2Rl.hstructBot_junction`), and ROOTX's guarded slow words (`frameNSlowWordN_rjShellG`). -/
theorem vwordsX_pkgOneG (k : ℕ) :
    GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (pkgOneG ψx Ex K₀ kSel k) GW2Sdh.nearLam := by
  have hslow := GW2Rk.frameNSlowWordN_rjShellG
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀
    (instInputsX_oneG ψx) GW2Sdq.gapFam GW2Sdh.nearLam GW2Bh.cwSrc hβ_guardWm hE₀_guardWm (verCovers_oneVerS ψx)
    (withShell (GW2Rv.pkgX T14Asm7.h13 (oneVerS ψx) chG (oneKbG ψx Ex K₀ k)) (rjShells (oneVerS ψx) GW2Bh.cwSrc))
    (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl)
  refine GW2Bh.vwordsX_withNearSB _ GW2Sdh.nearLam (oneNbS ψx) (kSel k) GW2Sdh.nearLam_ne (fun Ω _ _ c r l => ?_)
    (GW2Rl.hstructBot_junction (oneVerS ψx) (oneNbS ψx) (heq_oneNbS ψx)) hslow
  filter_upwards [GW2Rl.ae_nearSlotWordsG (h13 := T14Asm7.h13) (oneVerS ψx) GW2Bh.cwSrc hβ_guardWm hE₀_guardWm
    (GW2Rl.unifCover_verU T14Asm7.h13 verCovers_stop ψx) (oneKbG ψx Ex K₀ k) GW2Sdq.gapFam Ω c r l]
    with ω hω halive n
  filter_upwards [hω halive n] with m hm i j
  obtain ⟨h1, h2⟩ := hm (Nat.pair i j)
  refine ⟨h1, h2.trans ?_⟩
  rw [GW2Sdy.candidateAngle_pair]

/-- **GW2's root tests on the guarded base for the stop package** (D75): SDE's scaled cover with the two-sided gap
family, the instance inputs proved, and the package fields proved; only `hnearImg` remains. -/
theorem gw2RootTestStatement_oneG
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ),
      Supp8.GB6.HullId.IsPathRule (Ex Ω c r l n a) ∧ Measurable (Ex Ω c r l n a))
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((pkgOneG ψx Ex K₀ kSel k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_inst GW2Sdq.gapFam GW2Sdq.measurable_gapFam (fun _ _ _ c x => GW2Sds.ae_gapFam_pos c x)
    (instInputsX_oneG ψx) (sameSlots_pkgOneG ψx Ex K₀ kSel) (nearStopsX_pkgOneG ψx Ex K₀ hE)
    (vwordsX_pkgOneG ψx Ex K₀ kSel) hnearImg (rjDrift GW2Bh.cwSrc) (hshell_pkgOneG ψx Ex K₀ kSel GW2Sdq.gapFam)

end InteractingSLE.Wire.T14Re

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Re

/-- **Theorem 1.4 on the guarded base with the stop package** (D54, D67, D68, D75): `hmeanF`, `hno` and every
package field but `hnearImg` discharged; binders `hnearImg` (BUF, D75 (2)) and SB2(2)'s `hcan`, `hdet` (as in
ASSEMBLE7's `theorem14Statement_assembledG`). -/
theorem theorem14Statement_oneG (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u})
    (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ),
      Supp8.GB6.HullId.IsPathRule (Ex Ω c r l n a) ∧ Measurable (Ex Ω c r l n a))
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((pkgOneG ψx Ex K₀ kSel k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l))
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  T14Asm7.theorem14Statement_of_rootTests (gw2RootTestStatement_oneG ψx Ex K₀ kSel hE hnearImg)
    (SB.Lk.sb2LowerLaunchLiftStatement_of_liftEx T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀
      (SB.Cg.sb2LowerTailLiftExStatement_of_rest T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀
        (SB.Lk.sb2LowerGeomRestV6 T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ sb2LowerStartDataFamStatement)
        hcan
        (SB.Ch.sb2LowerRelPosWRootStatement_of_det T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hdet)))

end InteractingSLE.Wire
