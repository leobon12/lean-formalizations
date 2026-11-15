/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PvExp
import InteractingSLE.Spec.Supplement.GW2NxMean
import InteractingSLE.Spec.Supplement.GW2TwCons
import InteractingSLE.Spec.Supplement.GW2NyVd

/-!
# D46's export (datum form) at the top's instances, root `0`

Packet PROVE-GW2-STAGEMEAN, R123 round (D60). The export `GW2Pw.StageKernelExportLD` at every instance the top reads
at a root `0` and a strictly ordered history: the stop-capped family `GW2Nx.schedVerXStopFamily` (NOTHR, D54) and the
base family of GEOM2's word map `Wire.T14Cur.baseWm cw`, with Claim(k) from RELDET's `GW2Rd.claimAt_all_root0`,
the stop property on the record event from NOTHR's `GW2Ny.hVdE_stop` (D67), the far height from `GW2Psm.ae_farR_srecX`:

* `ExportFamilyLD0`: the family statement (root `0`, strictly ordered histories);
* **`exportFamilyLD0_stop`**, **`exportFamilyLD0_stop_canon`** (GEOM2's canonical counterflow word).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Pv

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm GW2Rd Sec5.Prop513Schedule Supp8 Supp8.Q3Stop GW2Psm WholeField LocalSets GW2JointKernel GW2Nx

/-- **D46's export family in the datum form** at roots `0` and strictly ordered histories. -/
def ExportFamilyLD0 (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    (h : GW2Rv.GoodRoot c r) → rootPt r.1 = 0 → ∀ a n : ℕ,
      GW2Pw.StageKernelExportLD c r l a (Wire.T14Cur.instC ver base Ω c r l a n h) (rootPt r.1)

/-- **The export at the top's instances** (stop-capped family, GEOM2's word map; root `0`). -/
theorem exportFamilyLD0_stop (cw : Wire.T14Cur.CfWord.{u})
    (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r)) :
    ExportFamilyLD0 (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) := by
  intro Ω _ _ c r l hord h hr0 a n
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
  have hcount : (Set.range fun y => wordType c.κ ((Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β y)).Countable
      := by
    rw [GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact (Wire.T14Cur.hword_baseWm cw Ω c r l hTO h a).2.1
  have hE₀ : MeasurableSet (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).E₀ := by
    rw [GW2Rd.schedChoiceLinesX_E₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact Wire.T14Cur.hE₀_baseWm cw Ω c r l hTO h a
  have hGT := schedGTX_spec Wire.T14Asm7.h13 c r l a
  have hA := (schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).isA h.1 n
  have hV := (schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).fin n
  have hall := GW2Rd.claimAt_all_root0 Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ c r hr0
    h.2 (hcw Ω c r) l hord
  exact stageKernelExportLD_root0_ae Wire.T14Asm7.h12 Wire.T14Asm7.h13 c r l a hr0 hord h.2 hGT hA hV
    (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a) hu₀ hcount (GW2Ny.hVdE_stop cw Ω c r l hord h a n)
    (fun w => hall a hGT hA hV _ hu₀ hβm hE₀ hβ hσa w)
    (fun w => GW2Psm.ae_farR_srecX c r l a hGT hA hV _ (cw Ω c r) (length_historyProgram c r l)
      (candAngle c r l a) hβ w)

/-- **The export at the top's instances, at GEOM2's canonical counterflow word.** -/
theorem exportFamilyLD0_stop_canon :
    ExportFamilyLD0 (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) :=
  exportFamilyLD0_stop GW2Nw.cfWordCanon GW2Nw.isCfWordOf_cfWordCanon

end InteractingSLE.Theorem14.GW2Pv
