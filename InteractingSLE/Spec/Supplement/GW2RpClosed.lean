/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RnFam
import InteractingSLE.Spec.Supplement.GW2KxB0Nil
import InteractingSLE.Spec.Supplement.GW2KtTop

/-!
# The export family and `hno`, closed (D65 with GEOM2's landed base; D68)

PROVE-GW2-ROOTX round 14. GEOM2's root-`x` base `GW2Kx.claimAllX_nil_rootX` (landed) discharges the `hnil` of
`GW2Rn.exportFamilyLD_stopX`:

* **`baseNilX_closed cw hcw`**: GEOM2's base in the form `GW2Rn.BaseNilX`;
* **`exportFamilyLD_stopX_closed cw hcw`**, **`hno_stopX_closed cw hcw`**: NOTHR's `GW2Ny.ExportFamilyLD` for the
  stop family and the top's `hno` (guarded: strictly ordered histories, roots `0 ∨ lowerArcRoots`), for every
  counterflow word `cw` of the source's data;
* **`exportFamilyLD_stopReindex cw hcw φ hφ`**, **`hno_stopReindex`**: the same for the stop family re-indexed by
  any strictly monotone `φ` (the re-indexed instance at version `n` is the stop instance at `φ n`, by `rfl`; as GEOM2's
  `GW2Kt.hmeanFGuarded_stopReindex`);
* at BUF's word `cwSrc` (GEOM2's bridge `GW2Kt.isCfWordOf_cwSrc`): **`hno_stopPkgVer ψx`** for GEOM2's
  `GW2Kt.stopPkgVer ψx`, and the canonical-word forms `…_canon` with no input at all.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rp

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd
  Sec5.Prop513Schedule Supp8 Supp8.Q3Stop GW2Nx

/-- A counterflow word of the source's data at every setup and root. -/
abbrev IsCfWordFam (cw : Wire.T14Cur.CfWord.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r)

/-- A strictly monotone re-indexing per setup, root, history and candidate (`GW2Bh.verReindex`'s argument). -/
abbrev ReidxFam : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ

/-- The guarded `hno` binder: `NoThresholdX` at the top's instances on strictly ordered histories and admissible
roots (the conclusion of NOTHR's `GW2Ny.hno_baseWm_of_exportLD`). -/
abbrev HnoGuarded (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    (h : GW2Rv.GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
    ∀ a n : ℕ, NoThresholdX (Wire.T14Cur.instC ver base Ω c r l a n h) c r l (rootPt r.1)

/-- **GEOM2's root-`x` base** in the `hnil` form of `GW2Rn.exportFamilyLD_stopX` (and of RELDET's
`GW2Rd.hmeanF_rootX_of_nil`). -/
theorem baseNilX_closed (cw : Wire.T14Cur.CfWord.{u}) (hcw : IsCfWordFam cw) : GW2Rn.BaseNilX cw :=
  fun Ω _ _ c r h hx => GW2Kx.claimAllX_nil_rootX Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀
    Wire.T14Asm7.h13₀ c r (Or.inr hx) h.2 (hcw Ω c r)

/-- **D46's export family at every admissible root, closed** (stop family, GEOM2's word map). -/
theorem exportFamilyLD_stopX_closed (cw : Wire.T14Cur.CfWord.{u}) (hcw : IsCfWordFam cw) :
    GW2Ny.ExportFamilyLD (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) :=
  GW2Rn.exportFamilyLD_stopX cw hcw (baseNilX_closed cw hcw)

/-- **The top's guarded `hno`, closed** (stop family). -/
theorem hno_stopX_closed (cw : Wire.T14Cur.CfWord.{u}) (hcw : IsCfWordFam cw) :
    HnoGuarded (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) :=
  GW2Ny.hno_baseWm_of_exportLD cw (exportFamilyLD_stopX_closed cw hcw)

/-- **The export family for the stop family re-indexed by any strictly monotone `φ`** (the re-indexed instance at
`n` is the stop instance at `φ n`). -/
theorem exportFamilyLD_stopReindex (cw : Wire.T14Cur.CfWord.{u}) (hcw : IsCfWordFam cw) (φ : ReidxFam.{u})
    (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a)) :
    GW2Ny.ExportFamilyLD (GW2Bh.verReindex (schedVerXStopFamily Wire.T14Asm7.h13) φ hφ) (Wire.T14Cur.baseWm cw) :=
  fun Ω _ _ c r l hord h hroot a n => exportFamilyLD_stopX_closed cw hcw Ω c r l hord h hroot a (φ Ω c r l a n)

/-- **The top's guarded `hno` for the stop family re-indexed by any strictly monotone `φ`.** -/
theorem hno_stopReindex (cw : Wire.T14Cur.CfWord.{u}) (hcw : IsCfWordFam cw) (φ : ReidxFam.{u})
    (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a)) :
    HnoGuarded (GW2Bh.verReindex (schedVerXStopFamily Wire.T14Asm7.h13) φ hφ) (Wire.T14Cur.baseWm cw) :=
  GW2Ny.hno_baseWm_of_exportLD cw (exportFamilyLD_stopReindex cw hcw φ hφ)

/-- **The top's guarded `hno` for GEOM2's `stopPkgVer ψx` at BUF's word `cwSrc`.** -/
theorem hno_stopPkgVer (ψx : GW2Bh.PsiFam.{u}) :
    HnoGuarded (GW2Kt.stopPkgVer ψx) (Wire.T14Cur.baseWm GW2Bh.cwSrc) :=
  hno_stopReindex GW2Bh.cwSrc GW2Kt.isCfWordOf_cwSrc _ _

/-- The export family at GEOM2's canonical counterflow word, with no input. -/
theorem exportFamilyLD_stopX_canon_closed :
    GW2Ny.ExportFamilyLD.{u} (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) :=
  exportFamilyLD_stopX_closed GW2Nw.cfWordCanon GW2Nw.isCfWordOf_cfWordCanon

/-- The top's guarded `hno` at GEOM2's canonical counterflow word, with no input. -/
theorem hno_stopX_canon_closed :
    HnoGuarded.{u} (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) :=
  hno_stopX_closed GW2Nw.cfWordCanon GW2Nw.isCfWordOf_cfWordCanon

end InteractingSLE.Theorem14.GW2Rp
