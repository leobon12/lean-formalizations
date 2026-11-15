/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjBd

/-!
# The slow stage variable of a sub-history at a passed test (decision D33)

PROVE-GW2-ROOTX round 9, pathwise. For D3's slow stage variable `n` of `(l, a)` (`slowVarG`, the root-`x` instance of
version `n + 1`):

* `slowVarG_record`, `slowVarG_β`, `slowVarG_E`, `slowVarG_R`, `slowVarG_V`: its fields;
* **`slowVarG_word`**: with GEOM2's word map, its word on its record is the raised stage word of its decoded past
  (`GW2Wm.baseWordX_augRecX`);
* **`slowVarG_mem_E`**: its record is on its record event at a passed test (D42, success, alive);
* **`jointShiftTip_mem_H_of_test`**: the passed test's tip puts the stage-1 trace of the version in `ℍ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rq GW2Rv GW2Rz GW2Sde GW2Sdh GW2Sdx GW2Wm
  GW2Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {h13 : Exist.Theorem13Statement.{u}}
  {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}} {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)} {a : ℕ} {hx : 0 ≤ rootPt r.1} {n : ℕ}

theorem slowVarG_record : (slowVarG h13 ver ch c r l a hx n).record =
    GW2Rd.augRec (GW2Rd.stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
      (schedGTX h13 c r l a) ((ver Ω c r l a).V (n + 1)) (RootJ31.historyTime c r l) ((ver Ω c r l a).R (n + 1))) :=
  rfl

theorem slowVarG_β : (slowVarG h13 ver ch c r l a hx n).β = (ch Ω c r l a).β := rfl

theorem slowVarG_E : (slowVarG h13 ver ch c r l a hx n).E =
    ((ch Ω c r l a).E₀ ∩ GW2Sdi.succRec c r l) ∩
      aliveRecX ((entryList l).length + 1) (rootPt r.1) c.s ((ver Ω c r l a).isA hx (n + 1)).1.2.choose := rfl

theorem slowVarG_R (t : ℝ≥0) (ω : Ω) : (slowVarG h13 ver ch c r l a hx n).R t ω =
    GW2Rd.stgDrv (fun u => (ver Ω c r l a).R (n + 1) u ω)
      (stgStartX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V (n + 1))
        (RootJ31.historyTime c r l) ω) t := rfl

theorem slowVarG_V (ω : Ω) : (slowVarG h13 ver ch c r l a hx n).V ω =
    (ver Ω c r l a).V (n + 1) ω -
      (stgStartX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V (n + 1))
        (RootJ31.historyTime c r l) ω : ℝ≥0∞) := rfl

/-- **The word of the slow record** is the raised stage word of its decoded past. -/
theorem slowVarG_word {cw : BoundaryWord}
    (hβ : (ch Ω c r l a).β = schedWordMapX c.κ cw (rootPt r.1) c.s (RootJ31.historyProgram c r l)
      ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l) (GW2Rd.candAngle c r l a))
    (hs : 0 < c.s) {ω : Ω} (hωG : ω ∈ schedGTX h13 c r l a)
    (hver : VersionAtX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (GW2Rd.schedTr c r l a) c.α
      ((ver Ω c r l a).R (n + 1)) ((ver Ω c r l a).V (n + 1)) ω)
    (hord : HistOrdered c r l) (hold : RootJ31.oldSuccess c r l ω)
    (hTc : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω) :
    (slowVarG h13 ver ch c r l a hx n).β ((slowVarG h13 ver ch c r l a hx n).record ω) =
      GW2Rd.upW (GW2Rd.candAngle c r l a * chiC c.κ) (GW2JDetR5.stageWord (κ := c.κ)
        (rootWordX c.κ cw (rootPt r.1) c.s) (progAngle (RootJ31.historyProgram c r l)) ((entryList l).length + 1)
        (pastOf (cfRec c.s c.W c.ζ ω) (fun u => (ver Ω c r l a).R (n + 1) u ω)
          (trueBdX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V (n + 1))
            (RootJ31.historyProgram c r l) ((entryList l).length + 1) (RootJ31.historyTime c r l) ω)
          ((entryList l).length + 1))) := by
  obtain ⟨hGT, -, -⟩ := schedGTX_spec h13 c r l a
  have hLN : (RootJ31.historyProgram c r l).length = (entryList l).length + 1 := GW2Ru.length_historyProgram c r l
  have hTj : ∀ i < (entryList l).length + 1, schedTime 0 (RootJ31.historyProgram c r l) i ≤
      RootJ31.historyTime c r l :=
    fun i hi => GW2Ru.schedTime_le_historyTime c r l hord (by rw [hLN]; exact hi.le)
  have hjT : ∀ i < (entryList l).length + 1,
      schedTime 0 (RootJ31.historyProgram c r l) i ≤ Sec5.Prop513Schedule.lastTime 0 (RootJ31.historyProgram c r l) :=
    fun i hi => by rw [← GW2Sde.historyTime_eq_lastTime]; exact hTj i hi
  have hcon : ∀ i, 0 < i → i < (entryList l).length + 1 →
      (schedTime 0 (RootJ31.historyProgram c r l) i : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω :=
    fun i _ hi => (ENNReal.coe_le_coe.2 (hTj i hi)).trans_lt hTc
  have hagree : ∀ u ≤ RootJ31.historyTime c r l, RootJ31.joinedRead (RootJ31.historyProgram c r l)
      (fun i => (fun j : Fin ((entryList l).length + 1) =>
        stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) (Fin.cast hLN i)) u =
        GW2Rd.schedW c r l a u ω := fun u hu => by
    have e1 : GW2Rd.schedW c r l a u ω = Gm.futureJoined c r l a ω u :=
      congrFun (GW2Rd.schedW_of_oldSuccess c r l a hold) u
    rw [e1, GW2Bf.futureJoined_eq_histJoined c r l a ω hu]
    rfl
  rw [slowVarG_β, slowVarG_record, hβ]
  unfold schedWordMapX
  congr 1
  exact baseWordX_augRecX (x₀ := rootPt r.1) (sp := c.s) (W := GW2Rd.schedW c r l a) (Wα := c.W) (ζα := c.ζ)
    (GT := schedGTX h13 c r l a) (V := (ver Ω c r l a).V (n + 1)) (T := RootJ31.historyTime c r l)
    (R := (ver Ω c r l a).R (n + 1)) (γ := GW2Rd.schedTr c r l a) (α := c.α) c.κ cw hGT hs hx
    (RootJ31.historyProgram c r l) ((entryList l).length + 1) hLN (xr := GW2Rd.stageEncRec c r l) (ω := ω)
    (P := fun j : Fin ((entryList l).length + 1) => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω)
    rfl hver.1 hver.2.1 hωG ((ver Ω c r l a).fin (n + 1) ω) hTj hjT hcon hagree

/-- **The slow record is on its record event** at a passed test of its history. -/
theorem slowVarG_mem_E (hE₀ : (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ) {ω : Ω}
    (hbad : ∀ y : Ω → RecData, GW2Rd.augRec (GW2Rd.stageEncRec c r l) y ω ∉ GW2Rd.launchBadRec c r l a)
    (hold : RootJ31.oldSuccess c r l ω) (hgood : cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s)
    (hver : VersionAtX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (GW2Rd.schedTr c r l a) c.α
      ((ver Ω c r l a).R (n + 1)) ((ver Ω c r l a).V (n + 1)) ω)
    (hrho : (ver Ω c r l a).V (n + 1) ω = ((ver Ω c r l a).isA hx (n + 1)).1.2.choose
      (cfRec c.s c.W c.ζ ω, fun u => (ver Ω c r l a).R (n + 1) u ω))
    (hlt : (stgStartX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a)
      ((ver Ω c r l a).V (n + 1)) (RootJ31.historyTime c r l) ω : ℝ≥0∞) < (ver Ω c r l a).V (n + 1) ω) :
    (slowVarG h13 ver ch c r l a hx n).record ω ∈ (slowVarG h13 ver ch c r l a hx n).E := by
  rw [slowVarG_E, slowVarG_record]
  refine ⟨⟨?_, (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).2 hold⟩, ?_⟩
  · rw [hE₀]
    exact hbad _
  · exact GW2Sdo.mem_aliveRecX ((ver Ω c r l a).isA hx (n + 1)).1.2.choose_spec.2.1
      (GW2Rd.stgRecDec_stageEncRec c r l ω) hver.1 hver.2.1 hgood hrho hlt

end InteractingSLE.Theorem14.GW2Rj
