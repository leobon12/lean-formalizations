/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NxMean

/-!
# The stop property on the record event (for STAGEMEAN's family level)

Packet PROVE-GW2-NOTHR (round 7, decision D60). STAGEMEAN's `GW2Pw.stageKernelExportLD_root0` reads D49's stop
property `hVd` only at kernel samples on the record event `I.E`. A POINTWISE `hVd` (`∀ ω`) holds for no version family:
off the good set the physical clock is `0` while the version may be positive; at a zero lifetime the stop is `T`.
The stop-capped family satisfies it almost surely on the record event:

* **`hVdE_stop`**: at the top's instances `T14Cur.instC (GW2Nx.schedVerXStopFamily T14Asm7.h13) (baseWm cw)`, every
  cap is at most the root-`x` physical clock of `T + candStop` almost surely on the record event (`GW2Nx.hVd_stop`
  without the word type).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Ny

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd
  Sec5.Prop513Schedule Supp8 Supp8.Q3Stop GW2Psm GW2Sde GW2Nx

/-- **The stop-capped family is stopped at the candidate's stop on the record event of the top's instances**
(decision D49 (A), the form STAGEMEAN's export reads): on the record event the records are good, the history
succeeded and the record is off `launchBadRec`, so the lifetime is positive. -/
theorem hVdE_stop (cw : Wire.T14Cur.CfWord.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) → (h : GW2Rv.GoodRoot c r) → ∀ a n : ℕ,
      ∀ᵐ ω ∂c.P,
        (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h).srecX
            c r l (rootPt r.1) ω ∈
          (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h).E →
        (schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).V n ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ
          (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a) (historyTime c r l + candStop c r l a ω) ω := by
  intro Ω _ _ c r l hord h a n
  have hTO : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  set I := Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h
    with hI
  have hA := (schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).isA h.1 n
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ =>
      ne_top_of_le_ne_top ((schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).fin n ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hA.1.1 hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hGT := schedGTX_spec Wire.T14Asm7.h13 c r l a
  filter_upwards [hEgood, hGT.2.2, ae_life_pos_of_srecX_notMem Wire.T14Asm7.h13 c r l a I (rootPt r.1),
    ae_schedVerXStop_le_physClockX Wire.T14Asm7.h13 c r l a h.1 h.2 hTO hGT.1 n] with ω hE hGTω hpos hle hrecE
  have hgood := (hE hrecE).1
  have hold : oldSuccess c r l ω := (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).1 hrecE.1.2
  have hE₀ : I.srecX c r l (rootPt r.1) ω ∈ (Wire.T14Cur.baseWm cw Ω c r l a).E₀ := by
    have h1 := hrecE.1.1
    rwa [GW2Rd.schedChoiceLinesX_E₀] at h1
  exact hle (hGTω.2 hgood) hgood hold (hpos hold hE₀)

end InteractingSLE.Theorem14.GW2Ny
