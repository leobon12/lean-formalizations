/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PvDthE
import InteractingSLE.Spec.Supplement.GW2PvFam

/-!
# D46's death clause (datum form, positive lifetime) at the top's instances, root `0`

Packet PROVE-GW2-STAGEMEAN, R123 round (D46, D60, D67). `GW2Pv.StageDeathExportXDP` at every instance the top reads at
a root `0` and a strictly ordered history: NOTHR's stop-capped family `GW2Nx.schedVerXStopFamily` (caps below the
death clock `schedVerXStop_lt_deathClockX`, D27 below a finite death clock `schedVerXStop_exhausts_death`, the stop
property on the record event `GW2Ny.hVdE_stop`) and GEOM2's word map `Wire.T14Cur.baseWm cw` (record event off
`launchBadRec`, met at a positive lifetime by `GW2Rd.ae_mem_launchBadRec_iff`), with Claim(k) from RELDET's
`GW2Rd.claimAt_all_root0`:

* `DeathExportFamilyDP0`; **`deathExportFamilyDP0_stop`**, **`deathExportFamilyDP0_stop_canon`**.
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

/-- **D46's death clause family, datum form, positive lifetime**, at roots `0` and strictly ordered histories. -/
def DeathExportFamilyDP0 (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    (h : GW2Rv.GoodRoot c r) → rootPt r.1 = 0 → ∀ a j : ℕ,
      StageDeathExportXDP c r l a (Wire.T14Cur.instC ver base Ω c r l a j h) (ver Ω c r l a).R (ver Ω c r l a).V
        (rootPt r.1)

/-- **The death clause at the top's instances** (stop-capped family, GEOM2's word map; root `0`). -/
theorem deathExportFamilyDP0_stop (cw : Wire.T14Cur.CfWord.{u})
    (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r)) :
    DeathExportFamilyDP0 (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) := by
  intro Ω _ _ c r l hord h hr0 a j
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
  have hE₀eq : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ := by
    rw [GW2Rd.schedChoiceLinesX_E₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    rfl
  have hGT := schedGTX_spec Wire.T14Asm7.h13 c r l a
  set ver := schedVerXStopFamily Wire.T14Asm7.h13 with hver
  have hA := (ver Ω c r l a).isA h.1 j
  have hV := (ver Ω c r l a).fin j
  have hall := GW2Rd.claimAt_all_root0 Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ c r hr0
    h.2 (hcw Ω c r) l hord
  have hE₀pos : ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω →
      (GW2Rv.schedInstSX c r l a (schedGTX Wire.T14Asm7.h13 c r l a) hA
        (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a)).srecX c r l (rootPt r.1) ω ∈
        (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).E₀ := by
    filter_upwards [GW2Rd.ae_mem_launchBadRec_iff c r l a Wire.T14Asm7.h13] with ω hω hold hpos
    rw [hE₀eq]
    exact fun hbad => hpos.ne' ((hω hold _).1 hbad)
  exact stageDeathExportXDP_root0 Wire.T14Asm7.h12 Wire.T14Asm7.h13 c r l a hr0 hord h.2 hGT hA hV
    (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a) hu₀ hcount
    (ver Ω c r l a).R (ver Ω c r l a).V (fun n => (ver Ω c r l a).isA h.1 n) (ver Ω c r l a).fin j rfl rfl hE₀pos
    (schedVerXStop_lt_deathClockX Wire.T14Asm7.h13 c r l a h.1 h.2 hTO)
    ((schedVerXStop_exhausts_death Wire.T14Asm7.h13 c r l a h.1 h.2 hTO).mono fun _ hω hg ho hd => hω hg ho hd.ne)
    (GW2Ny.hVdE_stop cw Ω c r l hord h a j)
    (fun w => hall a hGT hA hV _ hu₀ hβm hE₀ hβ hσa w)
    (fun w => GW2Psm.ae_farR_srecX c r l a hGT hA hV _ (cw Ω c r) (length_historyProgram c r l)
      (candAngle c r l a) hβ w)

/-- **The death clause at the top's instances, at GEOM2's canonical counterflow word.** -/
theorem deathExportFamilyDP0_stop_canon :
    DeathExportFamilyDP0 (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) :=
  deathExportFamilyDP0_stop GW2Nw.cfWordCanon GW2Nw.isCfWordOf_cfWordCanon

end InteractingSLE.Theorem14.GW2Pv
