/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuExh
import InteractingSLE.Spec.Supplement.GW2BuBd
import InteractingSLE.Spec.Supplement.GW2RuShell
import InteractingSLE.Spec.Supplement.GW2RuLive

/-!
# The common stage data of a candidate's versions at one alive sample

Packet PROVE-GW2-BUF (round 18; the instance layer). Almost surely on an alive history, at every candidate's root-`x`
instance, every version whose cap passes the clock at the history time `T`:
* has the stage start `clockX T` (SDE's `GW2Sdo.stgStartX_eq_clockX`);
* has the same relative prefix record (SDE's `GW2Sdo.ae_stgPreRecX_sched_eq`);
* reads, on its augmented record, GEOM2's base word as the root word flowed through its own relative stage records
  between the stage boundaries `trueBdX` (`GW2Wm.baseWordX_augRecX`, with ROOTX's history side conditions as in
  `GW2Ru.ae_rightMark_ge`).

* **`ae_inst_common`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Wm GW2Schedule
  Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The common stage data of a candidate's versions at one alive sample.** -/
theorem ae_inst_common (h13 : Exist.Theorem13Statement.{u}) (gap : RootCv.GapFamily.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hg : GoodRoot c r)
    (ver : SchedVerXFamily.{u}) (κ : ℝ) (c' : BoundaryWord) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      ξ ∈ schedGTX h13 c r l a ∧ RootJ31.oldSuccess c r l ξ ∧ GW2Sdx.HistOrdered c r l ∧
      cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s ∧
      ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ∧
      (∀ j, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
          (ver Ω c r l a).V j ξ →
        stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
          (RootJ31.historyTime c r l) ξ =
            (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ).toNNReal) ∧
      (∀ j j', ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
          (ver Ω c r l a).V j ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
          (ver Ω c r l a).V j' ξ →
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
            (RootJ31.historyTime c r l) ((ver Ω c r l a).R j) ξ =
          stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j')
            (RootJ31.historyTime c r l) ((ver Ω c r l a).R j') ξ) ∧
      ∀ j, baseWordX κ c' (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
          (GW2Ru.length_historyProgram c r l) (augRec (stageEncRec c r l)
            (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
              (RootJ31.historyTime c r l) ((ver Ω c r l a).R j)) ξ) =
        GW2JDetR5.stageWord (κ := κ) (rootWordX κ c' (rootPt r.1) c.s) (progAngle (RootJ31.historyProgram c r l))
          ((entryList l).length + 1)
          (pastOf (cfRec c.s c.W c.ζ ξ) (fun u => (ver Ω c r l a).R j u ξ)
            (trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
              (RootJ31.historyProgram c r l) ((entryList l).length + 1) (RootJ31.historyTime c r l) ξ)
            ((entryList l).length + 1)) := by
  obtain ⟨hx, hs⟩ := hg
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  have hrec : ∀ᵐ ξ ∂c.P, ∀ j j', cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s →
      ((RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
          (ver Ω c r l a).V j ξ) →
      ((RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
          (ver Ω c r l a).V j' ξ) →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
          (RootJ31.historyTime c r l) ((ver Ω c r l a).R j) ξ =
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j')
          (RootJ31.historyTime c r l) ((ver Ω c r l a).R j') ξ :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun j' =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c r l a a hs hx ((ver Ω c r l a).isA hx j).1.1
        ((ver Ω c r l a).isA hx j').1.1
  filter_upwards [GW2Ru.ae_alive_goodEvent_scaled h13 gap c r, hGTae, hrec] with ξ hgood hGTξ hrecξ halive
  obtain ⟨hcf, hcon⟩ := hgood l halive
  have halive0 := GW2Sdz.alive_scaled_subset gap Ω c r l halive
  obtain ⟨-, hold, hord⟩ := RootJ32.alive_spec c r l ξ halive0
  have hξ : ξ ∈ schedGTX h13 c r l a := hGTξ.2 hcf
  refine ⟨hξ, hold, hord, hcf, hcon a, fun j hj => GW2Sdo.stgStartX_eq_clockX hGT hs hx hξ (hcon a) hj,
    fun j j' hj hj' => hrecξ j j' hcf ⟨hcon a, hj⟩ ⟨hcon a, hj'⟩, fun j => ?_⟩
  -- GEOM2's base word on the instance's record, with ROOTX's history side conditions
  set L := RootJ31.historyProgram c r l with hLdef
  set N := (entryList l).length + 1 with hNdef
  have hLN : L.length = N := GW2Ru.length_historyProgram c r l
  have hTj : ∀ k < N, schedTime 0 L k ≤ RootJ31.historyTime c r l := fun k hk =>
    GW2Ru.schedTime_le_historyTime c r l hord (by rw [hLN]; exact hk.le)
  have hjT : ∀ k < N, schedTime 0 L k ≤ lastTime 0 L := fun k hk => by
    rw [← GW2Sde.historyTime_eq_lastTime]
    exact hTj k hk
  have hconj : ∀ k, 0 < k → k < N → (schedTime 0 L k : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := fun k _ hk =>
    (ENNReal.coe_le_coe.2 (hTj k hk)).trans_lt (hcon a)
  have hagree : ∀ u ≤ RootJ31.historyTime c r l, RootJ31.joinedRead L
      (fun i => (fun k : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) k ξ) (Fin.cast hLN i)) u =
        schedW c r l a u ξ := fun u hu => by
    have e1 : schedW c r l a u ξ = Gm.futureJoined c r l a ξ u :=
      congrFun (schedW_of_oldSuccess c r l a hold) u
    rw [e1, GW2Bf.futureJoined_eq_histJoined c r l a ξ hu]
    rfl
  exact baseWordX_augRecX (x₀ := rootPt r.1) (sp := c.s) (W := schedW c r l a) (Wα := c.W) (ζα := c.ζ)
    (GT := schedGTX h13 c r l a) (V := (ver Ω c r l a).V j) (T := RootJ31.historyTime c r l)
    (R := (ver Ω c r l a).R j) (γ := schedTr c r l a) (α := c.α) κ c' hGT hs hx L N hLN (xr := stageEncRec c r l)
    (ω := ξ) (P := fun k : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) k ξ) rfl
    (((ver Ω c r l a).isA hx j).1.1.2.1 ξ) (((ver Ω c r l a).isA hx j).1.1.2.2.1 ξ) hξ ((ver Ω c r l a).fin j ξ)
    hTj hjT hconj hagree

end InteractingSLE.Theorem14.GW2Bh
