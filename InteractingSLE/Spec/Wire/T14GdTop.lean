/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T14GdBase

/-!
# Theorem 1.4 on the guarded base: the top re-wired to the guarded forms (D54, D67, D68)

Packet PROVE-T14-ASSEMBLE7 (round 2b). The top on D68's single family, NOTHR's stop family re-indexed with BUF's `ψx`
(`GW2Kt.stopPkgVer ψx`), and on the guarded word-map base `T14Gd.guardBase (baseWm GW2Bh.cwSrc)`
(`Spec/Wire/T14GdBase`). The instance inputs `hmeanF` and `hno` are **no longer binders**: they are discharged by
GEOM2's guarded `hmeanF` (`GW2Kt.hmeanFGuarded_stopPkgVer`) and ROOTX's guarded `hno` (`GW2Rn.hno_stopX`) through
`T14Gd.instInputsX_stopG`.

The remaining GW2 binders are the package fields on the guarded base (SDE's `VPairInputsXCSD` fields, as in
`T14Cur.gw2RootTestStatement_inst`): `hs`, `hnear`, `hwords`, `hnearImg`, `hshell`. ROOTX and BUF proved these for the
unguarded base `baseWm cwSrc` (`T14Rm.pkgOne`), using the identity `E₀ = (launchBadRec)ᶜ` at every history; on the
guarded base that identity holds on guarded histories only (`T14Gd.guardBase_E₀_of_guard`), which are all the top reads
(`GW2Kt.guard_of_aliveS`).

Main results: **`T14Gd.gw2RootTestStatement_stopG`** and **`Wire.theorem14Statement_assembledG`** (with SB2(2)'s
`hcan`, `hdet` as in `theorem14Statement_assembled16`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur

/-- **GW2's root tests on the guarded base for D68's family**: SDE's scaled cover with the two-sided gap family, the
instance inputs proved (`T14Gd.instInputsX_stopG`), and the package fields on the guarded base. -/
theorem T14Gd.gw2RootTestStatement_stopG (ψx : GW2Bh.PsiFam.{u}) {Kb : ℕ → GW2Sde.PkgFamily.{u}}
    {V : ℕ → GW2Sdx.VPkgXFamily.{u}}
    (hs : ∀ k : ℕ, GW2Rv.SameSlots
      (GW2Rv.pkgX T14Asm7.h13 (GW2Kt.stopPkgVer ψx) (chL (T14Gd.guardBase (baseWm GW2Bh.cwSrc))) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 (GW2Kt.stopPkgVer ψx)
      (chL (T14Gd.guardBase (baseWm GW2Bh.cwSrc))) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹ (aliveS GW2Sdq.gapFam Ω c r l))
    {C : GW2Rt.DriftFamily.{u}}
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_inst GW2Sdq.gapFam GW2Sdq.measurable_gapFam (fun _ _ _ c x => GW2Sds.ae_gapFam_pos c x)
    (T14Gd.instInputsX_stopG ψx) hs hnear hwords hnearImg C hshell

/-- **Theorem 1.4 on the guarded base** (D54, D67, D68): `hmeanF` and `hno` discharged by the owners' guarded forms;
binders the package fields on the guarded base and SB2(2)'s `hcan`, `hdet` (as in `theorem14Statement_assembled16`).
-/
theorem theorem14Statement_assembledG (ψx : GW2Bh.PsiFam.{u}) {Kb : ℕ → GW2Sde.PkgFamily.{u}}
    {V : ℕ → GW2Sdx.VPkgXFamily.{u}}
    (hs : ∀ k : ℕ, GW2Rv.SameSlots
      (GW2Rv.pkgX T14Asm7.h13 (GW2Kt.stopPkgVer ψx) (chL (T14Gd.guardBase (baseWm GW2Bh.cwSrc))) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 (GW2Kt.stopPkgVer ψx)
      (chL (T14Gd.guardBase (baseWm GW2Bh.cwSrc))) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹ (aliveS GW2Sdq.gapFam Ω c r l))
    {C : GW2Rt.DriftFamily.{u}}
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω)
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  T14Asm7.theorem14Statement_of_rootTests (T14Gd.gw2RootTestStatement_stopG ψx hs hnear hwords hnearImg hshell)
    (SB.Lk.sb2LowerLaunchLiftStatement_of_liftEx T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀
      (SB.Cg.sb2LowerTailLiftExStatement_of_rest T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀
        (SB.Lk.sb2LowerGeomRestV6 T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ sb2LowerStartDataFamStatement)
        hcan
        (SB.Ch.sb2LowerRelPosWRootStatement_of_det T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hdet)))

end InteractingSLE.Wire
