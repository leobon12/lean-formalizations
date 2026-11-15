/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TuFar
import InteractingSLE.Spec.Supplement.GW2SdsN3

/-!
# Decision D37 (with D43): the lower, rightward structure on every alive history

Packet PROVE-GW2-RELDET (round 32). Almost surely on the alive event of the scaled J32 with SDE's two-sided gap
`GW2Sdq.gapFam` (decision D43), the base word of any root-`x` version of a candidate whose stop passes the history's
clock (GEOM2's `GW2Wm.baseWordX` on the instance's stage record, with the source counterflow word `GW2Sds.cfWordSrc c`)
has ROOT2's LOWER (rightward) structure `NearStructBot` at the near scale `nearRootScale r.2 (nearLam l)`, in the
orientation `flipOf |l|` read by the near selection (`GW2Sdy.vwordsX_withNear*`):

* SDE's inputs (`GW2Sds.ae_baseWord_inputs`, `GW2Sds.ae_stageJunctions`): the base word is the stage word of the
  version's decoded past, the root word's side forms and far heights, the stage junctions strictly off the tip;
* the far junction (`GW2Rd.ae_farJunction`): both root junctions beyond `3√s` on the gap's cover, and the cumulative
  displacement after the root stage points away from the side read (J32's passed test, read by the version);
* `GW2Rd.nearStructBot_stageWord` (both orientations).

Result: **`ae_nearStructBot_junction`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.RootH10
  GW2Rz GW2Wm GW2Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **D37 on the junction-gap cover**: almost surely on the alive event of `J32S GW2Sdq.gapFam`, the base word of
any root-`x` version of a candidate whose stop passes the history's clock has ROOT2's lower (rightward) structure
`NearStructBot` at the near scale, in the orientation `flipOf |l|`. -/
theorem ae_nearStructBot_junction (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hfin : ∀ ω, V ω ≠ ⊤) :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V ω →
      GW2Sdy.NearStructBot c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
        (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
          (GW2Ru.length_historyProgram c r l)
          (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
            (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) V (historyTime c r l) R) ω)) := by
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  filter_upwards [GW2Sds.ae_baseWord_inputs h13 c r l a hx hs hA hfin, GW2Sds.ae_stageJunctions h13 c r l a hx hs hA,
    ae_farJunction h13 c r hx hs l a hA hfin] with ω hin hjun hfar halive hV
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hbase, ⟨hformL, hformR⟩, hpos, hneg⟩ := hin halive32 hV
  obtain ⟨hjL, hjR⟩ := hjun halive32 hV
  have hf := hfar halive hV
  rw [hbase]
  set n := (entryList l).length with hn
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (historyProgram c r l)
    (n + 1) (historyTime c r l) ω with hb
  set cf := cfRec c.s c.W c.ζ ω with hcf'
  have hroot := GW2Wm.pastRoot_pastOf cf (fun u => R u ω) b (n + 1)
  have hθ : ∀ j, progAngle (historyProgram c r l) j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    GW2Sds.progAngle_mem_Icc c r l
  have hs' : GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω) ≠ 0 :=
    GW2Sdh.nearRootScale_ne_zero r.2 (GW2Sdh.nearLam_ne Ω c r l ω)
  have hfarL : GW2Wm.FarL (GW2JDetR5.stageWord (κ := c.κ)
      (GW2Wm.rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s)
      (progAngle (historyProgram c r l)) (n + 1) (pastOf cf (fun u => R u ω) b (n + 1)))
      (-sleLambda (16 / c.κ) + Real.pi * chiC c.κ) :=
    GW2Wm.farL_stageWord c.hκ (progAngle (historyProgram c r l))
      (A₀ := {p : RecData | 0 < markPos (rdrv p) (rtime p) 0})
      (fun p hp => GW2Wm.farL_rootWordX c.hκ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s p hp) (n + 1) _
      (by rw [hroot]; exact hpos)
  have hfarR : GW2Wm.FarR (GW2JDetR5.stageWord (κ := c.κ)
      (GW2Wm.rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s)
      (progAngle (historyProgram c r l)) (n + 1) (pastOf cf (fun u => R u ω) b (n + 1)))
      (sleLambda (16 / c.κ) - Real.pi * chiC c.κ) :=
    GW2Wm.farR_stageWord c.hκ (progAngle (historyProgram c r l))
      (A₀ := {p : RecData | markPosL (rdrv p) (rtime p) 0 < 0})
      (fun p hp => GW2Wm.farR_rootWordX c.hκ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s p hp) (n + 1) _
      (by rw [hroot]; exact hneg)
  exact nearStructBot_stageWord c.hκ c.hκ4 _ _ hθ n _ hs' _ (by rw [hroot]; exact hformL)
    (by rw [hroot]; exact hformR) hfarL hfarR hjL hjR hf

end InteractingSLE.Theorem14.GW2Rd
