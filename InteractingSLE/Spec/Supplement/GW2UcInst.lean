/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UcStmt
import InteractingSLE.Spec.Supplement.GW2UbExh
import InteractingSLE.Spec.Supplement.GW2RpPkg
import InteractingSLE.Spec.Supplement.GW2PqRoot

/-!
# The guarded instances of the tip exclusion

Packet PROVE-GW2-RELDET (round 39, decision D84). The tip exclusion reads the stage law on the top's instances on the
guarded base: D75's family `Wire.T14Rp.oneVerS ψx` (a re-indexing of NOTHR's stop family) with the choice
`Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))`, whose instance inputs hold with no
hypotheses (`instInputsX_tip`). On a guarded history:

* `chL_guard`: the guarded choice is the unguarded one, so STAGEMEAN's premises
  (`GW2Pq.flowSwallow_premises_schedInstSX`) apply;
* `E₀_chL_guard`: its record event before the success and liveness is `launchBadRecᶜ`;
* **`srecX_mem_E`**: the stage record of a version alive at the stage start lies in the instance's record event (on the
  good record, the success, a positive life and the cap read by its path rule).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sde
  GW2Sdh

/-- **The instance inputs of the tip exclusion's family** (D75's family on the guarded base; no hypotheses). -/
theorem instInputsX_tip (ψx : GW2Bh.PsiFam.{u}) :
    InstInputsX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) :=
  Wire.T14Gd.instInputsX_guardBase GW2Bh.cwSrc (Wire.T14Rp.hmeanFGuarded_oneVerS ψx)
    (Wire.T14Rp.hnoGuarded_oneVerS ψx)

section Guard

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- On a guarded history the guarded choice is the unguarded one. -/
theorem chL_guard (cw : Wire.T14Cur.CfWord.{u}) (a : ℕ) (hg : Wire.T14Gd.Guard c r l) :
    Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw)) Ω c r l a =
      Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a := by
  unfold Wire.T14Cur.chL schedChoiceLinesX
  simp only [Wire.T14Gd.guardBase_of_guard _ a hg]

/-- On a guarded history the choice's record event is the complement of the zero-lifetime records. -/
theorem E₀_chL_guard (cw : Wire.T14Cur.CfWord.{u}) (a : ℕ) (hg : Wire.T14Gd.Guard c r l) :
    (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw)) Ω c r l a).E₀ = (launchBadRec c r l a)ᶜ := by
  rw [chL_guard cw a hg]
  unfold Wire.T14Cur.chL schedChoiceLinesX
  split_ifs <;> rfl

end Guard

section Rec

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The stage record of a version alive at the stage start lies in the instance's record event** (one sample: a good
record, the history's success, the record off the zero-lifetime set, the cap read by its path rule). -/
theorem srecX_mem_E (ψx : GW2Bh.PsiFam.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) (hx : 0 ≤ rootPt r.1) (hg : Wire.T14Gd.Guard c r l) {ξ : Ω}
    (hgx : cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s) (hold : oldSuccess c r l ξ)
    (hnot : (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx).srecX c r l
        (rootPt r.1) ξ ∉ launchBadRec c r l a)
    (hVρ : (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx).V ξ =
      (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
        (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx).ρ
        (cfRec c.s c.W c.ζ ξ, fun u => (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
          (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx).R u ξ))
    (hlt : (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
      ((Wire.T14Rp.oneVerS ψx Ω c r l a).V n) (historyTime c r l) ξ : ℝ≥0∞) <
        (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ) :
    (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx).srecX c r l
        (rootPt r.1) ξ ∈
      (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
        (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx).E := by
  have hA := (Wire.T14Rp.oneVerS ψx Ω c r l a).isA hx n
  refine ⟨⟨?_, (GW2Sdi.augRec_mem_succRec_iff c r l _ ξ).2 hold⟩, ?_⟩
  · show _ ∈ (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc)) Ω c r l a).E₀
    rw [E₀_chL_guard GW2Bh.cwSrc a hg]
    exact hnot
  · exact GW2Sdo.mem_aliveRecX hA.1.2.choose_spec.2.1 (stgRecDec_stageEncRec c r l ξ) (hA.1.1.2.1 ξ)
      (hA.1.1.2.2.1 ξ) hgx hVρ hlt

end Rec

end InteractingSLE.Theorem14.GW2Rd
