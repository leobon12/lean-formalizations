/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RnExp
import InteractingSLE.Spec.Supplement.GW2NyKer
import InteractingSLE.Spec.Supplement.GW2NyVd
import InteractingSLE.Spec.Supplement.GW2TwCons
import InteractingSLE.Spec.Supplement.GW2PsmFarX
import InteractingSLE.Spec.Supplement.GW2NwMean

/-!
# D46's export family (datum form) at every admissible root (D65)

PROVE-GW2-ROOTX round 13. NOTHR's family statement `GW2Ny.ExportFamilyLD ver base` (the `hexp` of
`GW2Ny.hno_of_exportLD`, `hno_baseWm_of_exportLD`: roots `x ∈ {0} ∪ lowerArcRoots`, strictly ordered histories) at
the top's instances: NOTHR's stop-capped family `GW2Nx.schedVerXStopFamily` (D54) and GEOM2's word map
`Wire.T14Cur.baseWm cw`. Inputs:

* Claim(k) in the root-`x` chart at every history: RELDET's `GW2Rd.claimAtX_all_of_nil` from the base
  `GW2Rd.ClaimAllX c r cw []` — at the root `0` RELDET's `claimAllX_nil_root0` (GEOM2's landed base), at the roots
  of `lowerArcRoots` GEOM2's root-`x` base `hnil`, consumed as stated (the binder of RELDET's
  `GW2Rd.hmeanF_rootX_of_nil`);
* the stop property on the record event: NOTHR's `GW2Ny.hVdE_stop` (D67);
* the far height: `GW2Psm.ae_farR_srecX`;
* the export at one instance: `GW2Rn.stageKernelExportLD_rootX`.

Results:
* **`exportFamilyLD_stopX cw hcw hnil`**: `ExportFamilyLD (schedVerXStopFamily h13) (baseWm cw)`;
* **`hno_stopX cw hcw hnil`**: the top's `hno` at admissible roots (NOTHR's `hno_baseWm_of_exportLD`);
* `exportFamilyLD_stopX_canon`, `hno_stopX_canon`: the same at GEOM2's canonical counterflow word.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rn

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm GW2Rd Sec5.Prop513Schedule Supp8 Supp8.Q3Stop GW2Psm WholeField LocalSets GW2JointKernel GW2Nx

/-- GEOM2's root-`x` base (the `hnil` binder of RELDET's `GW2Rd.hmeanF_rootX_of_nil`). -/
abbrev BaseNilX (cw : Wire.T14Cur.CfWord.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q), GW2Rv.GoodRoot c r → rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps →
    ClaimAllX c r (cw Ω c r) []

/-- **D46's export at the top's instances at every admissible root** (stop-capped family, GEOM2's word map). -/
theorem exportFamilyLD_stopX (cw : Wire.T14Cur.CfWord.{u})
    (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r))
    (hnil : BaseNilX cw) :
    GW2Ny.ExportFamilyLD (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) := by
  intro Ω _ _ c r l hord h hroot a n
  have hTO : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  have hβ : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β = GW2Wm.schedWordMapX c.κ (cw Ω c r)
      (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1) (length_historyProgram c r l)
      (candAngle c r l a) := by
    rw [GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    rfl
  have hσa : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).σa =
      specOffset c.κ + candAngle c r l a * chiC c.κ := by
    show (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) Ω c r l a).σa = _
    unfold GW2Rd.schedChoiceLinesX
    split_ifs
    rfl
  have hu₀ := GW2Rd.schedChoiceLinesX_u₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a hTO
  have hβm : Measurable (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β := by
    rw [GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact (Wire.T14Cur.hword_baseWm cw Ω c r l hTO h a).1
  have hcount :
      (Set.range fun y => wordType c.κ ((Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β y)).Countable := by
    rw [GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact (Wire.T14Cur.hword_baseWm cw Ω c r l hTO h a).2.1
  have hE₀ : MeasurableSet (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).E₀ := by
    rw [GW2Rd.schedChoiceLinesX_E₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact Wire.T14Cur.hE₀_baseWm cw Ω c r l hTO h a
  have hGT := schedGTX_spec Wire.T14Asm7.h13 c r l a
  have hA := (schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).isA h.1 n
  have hV := (schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).fin n
  have hbase : ClaimAllX c r (cw Ω c r) [] := hroot.elim
    (fun hr0 => claimAllX_nil_root0 Wire.T14Asm7.h12 Wire.T14Asm7.h13 c r hr0 h.2 (hcw Ω c r))
    (fun hx => hnil Ω c r h hx)
  have hall := claimAtX_all_of_nil Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ c r hroot
    h.2 (cw Ω c r) hbase l hord
  exact stageKernelExportLD_rootX Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h13₀ c r l a hroot hord h.2 hGT hA
    hV (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a) hu₀ hcount (GW2Ny.hVdE_stop cw Ω c r l hord h a n)
    (fun w => hall a hGT hA hV _ hu₀ hβm hE₀ hβ hσa w)
    (fun w => GW2Psm.ae_farR_srecX c r l a hGT hA hV _ (cw Ω c r) (length_historyProgram c r l)
      (candAngle c r l a) hβ w)

/-- **The top's `hno` at every admissible root and strictly ordered history** (stop-capped family, GEOM2's word map),
from the export family (NOTHR's `hno_baseWm_of_exportLD`). -/
theorem hno_stopX (cw : Wire.T14Cur.CfWord.{u})
    (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r))
    (hnil : BaseNilX cw) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
      ∀ a n : ℕ, NoThresholdX (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw)
        Ω c r l a n h) c r l (rootPt r.1) :=
  GW2Ny.hno_baseWm_of_exportLD cw (exportFamilyLD_stopX cw hcw hnil)

/-- The export family at GEOM2's canonical counterflow word. -/
theorem exportFamilyLD_stopX_canon (hnil : BaseNilX.{u} GW2Nw.cfWordCanon.{u}) :
    GW2Ny.ExportFamilyLD.{u} (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) :=
  exportFamilyLD_stopX.{u} GW2Nw.cfWordCanon GW2Nw.isCfWordOf_cfWordCanon hnil

/-- The top's `hno` at GEOM2's canonical counterflow word, at every admissible root. -/
theorem hno_stopX_canon (hnil : BaseNilX.{u} GW2Nw.cfWordCanon.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
      ∀ a n : ℕ, NoThresholdX (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13)
        (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) Ω c r l a n h) c r l (rootPt r.1) :=
  hno_stopX.{u} GW2Nw.cfWordCanon GW2Nw.isCfWordOf_cfWordCanon hnil

end InteractingSLE.Theorem14.GW2Rn
