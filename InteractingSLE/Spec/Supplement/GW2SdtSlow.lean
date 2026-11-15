/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdtLife
import InteractingSLE.Spec.Supplement.GW2RsShell
import InteractingSLE.Spec.Supplement.GW2SdoNear
import InteractingSLE.Spec.Supplement.GW2SdsWords
import InteractingSLE.Spec.Supplement.GW2SdiInst
import InteractingSLE.Spec.Supplement.GW2TpSets

/-!
# The slow words (`hslow`, D45 item 3)

Packet PROVE-GW2-SDE (round 19, decision D45 (3)). `FrameNSlowWordN` asks, at every alive history of even length
`2k + 4` and every candidate `a`, eventually in the version index `n`, that the slow slot's record lies in its record
event and that its word is presented by the package's slow shell at the root scale. The slow slot of `pkgX` (version
`n + 1` of `ver`) reads the candidate's stage record; once the version passes the history's clock, all versions of `a`
have the same prefix record (`GW2Sdo.ae_stgPreRecX_sched_eq`), so the slow word is eventually ONE word, the word map of
the candidate at that record. The slow shell is ROOTX's decomposition of that word (`GW2Rs.canonShell`, which presents
it exactly, `GW2Rs.presentsO_canonShell`), with start `histStart` (ROOTX's shell field).

* `slowPre`, `slowWordOf`, **`slowShellOf`**: the shell to put in the package's `slowShell` (for the package builder);
* **`frameNSlowWordN_slowShellOf`**: `FrameNSlowWordN` for every package whose slow slots are `pkgX`'s, with a choice
  family whose word is the root-`x` word map and whose record event contains `(launchBadRec c r l a)ᶜ`, and whose slow
  shells are `slowShellOf`, for a version family whose stops eventually pass the history's clock;
* `schedChoiceLinesX_β`, `schedChoiceLinesX_E₀`: RELDET's lines leave the word and the record event of a base family.

The record event: off `launchBadRec` by `ae_notMem_launchBadRec` (item 2), successful by `augRec_mem_succRec_iff`,
live by `GW2Sdo.mem_aliveRecX`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sdt

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Wm

section Defs

variable (h13 : Theorem13Statement.{u}) (ver : GW2Rv.SchedVerXFamily.{u})
  (cw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω), ScaledRootIdx c.Θ c.Q →
    BoundaryWord)
  (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

open Classical in
/-- **The candidate's slow prefix record**: the prefix record of the first version `n + 1` whose stop passes the
history's clock. -/
def slowPre (ω : Ω) : RecData :=
  if h : ∃ n : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
      (ver Ω c r l a).V (n + 1) ω then
    stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V (Nat.find h + 1))
      (historyTime c r l) ((ver Ω c r l a).R (Nat.find h + 1)) ω
  else default

/-- **The candidate's slow word**: the root-`x` word map of the candidate at the slow prefix record. -/
def slowWordOf (ω : Ω) : BoundaryWord :=
  schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
    (length_historyProgram c r l) (candAngle c r l a) (augRec (stageEncRec c r l) (slowPre h13 ver Ω c r l a) ω)

/-- **The slow shell of the candidate**: ROOTX's decomposition of the slow word, started at the history start. -/
def slowShellOf (ω : Ω) : GW2Sde.SlowShell :=
  GW2Rs.canonShell c.κ (slowWordOf h13 ver cw Ω c r l a ω) (candAngle c r l a) r.2 (GW2Bf.histStart c r l ω)

end Defs

/-- RELDET's lines leave the word of a base family. -/
theorem schedChoiceLinesX_β (h12 : Exist.Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (base : GW2Sdh.SchedChoiceFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (schedChoiceLinesX h12 h13 base Ω c r l a).β = (base Ω c r l a).β := by
  unfold schedChoiceLinesX
  split_ifs <;> rfl

/-- RELDET's lines leave the record event of a base family. -/
theorem schedChoiceLinesX_E₀ (h12 : Exist.Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (base : GW2Sdh.SchedChoiceFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (schedChoiceLinesX h12 h13 base Ω c r l a).E₀ = (base Ω c r l a).E₀ := by
  unfold schedChoiceLinesX
  split_ifs <;> rfl

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The slow words (`hslow`)** for a package with `pkgX`'s slow slots and the slow shells `slowShellOf`: for a
version family whose stops eventually pass the history's clock, and a choice family whose word is the root-`x` word
map of the candidate and whose record event contains `(launchBadRec c r l a)ᶜ` (the current top's base family
`T14Cur.baseWm cw` through RELDET's lines). -/
theorem frameNSlowWordN_slowShellOf (h13 : Theorem13Statement.{u}) (gap : RootCv.GapFamily.{u})
    (lam : GW2Sdh.NearDil.{u}) (ver : GW2Rv.SchedVerXFamily.{u})
    (cw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω), ScaledRootIdx c.Θ c.Q →
      BoundaryWord)
    (ch : GW2Sdh.SchedChoiceFamily.{u})
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
        (historyProgram c r l) ((entryList l).length + 1) (length_historyProgram c r l) (candAngle c r l a))
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      (launchBadRec c r l a)ᶜ ⊆ (ch Ω c r l a).E₀)
    (hcov : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
        cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω)
    (V : GW2Sdx.VPkgXFamily.{u})
    (hvar : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ),
      (V Ω c r).slowVar l a n = GW2Rv.slowSlotX h13 ver ch Ω c r l a n)
    (hsh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω),
      (V Ω c r).slowShell l a ω = slowShellOf h13 ver cw Ω c r l a ω) :
    GW2Sdx.FrameNSlowWordN (GW2Sdz.J32S gap) (fun n => (V.at n).frameN lam) := by
  intro Ω _ _ c r k l hlen a
  by_cases hg : GW2Rv.GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hgood halive
    exact absurd (hgood (GW2Sdz.alive_scaled_subset gap Ω c r l halive)) hg
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  have hpair : ∀ᵐ ω ∂c.P, ∀ n m : ℕ, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      ((historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω) →
      ((historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V m ω) →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V n)
          (historyTime c r l) ((ver Ω c r l a).R n) ω =
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V m)
          (historyTime c r l) ((ver Ω c r l a).R m) ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun m =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c r l a a hg.2 hg.1 ((ver Ω c r l a).isA hg.1 n).1.1
        ((ver Ω c r l a).isA hg.1 m).1.1
  have hρ : ∀ᵐ ω ∂c.P, ∀ n : ℕ, (ver Ω c r l a).V n ω =
      ((ver Ω c r l a).isA hg.1 n).1.2.choose (cfRec c.s c.W c.ζ ω, fun u => (ver Ω c r l a).R n u ω) :=
    ae_all_iff.2 fun n => ((ver Ω c r l a).isA hg.1 n).1.2.choose_spec.2.2
  filter_upwards [GW2Ru.ae_alive_goodEvent h13 c r, hGTae, hcov Ω c r l a hg, hpair, hρ,
    ae_notMem_launchBadRec h13 c r l] with ω hgood hGTω hcovω hpω hρω hbad halive
  have halive32 := GW2Sdz.alive_scaled_subset gap Ω c r l halive
  obtain ⟨hcf, hcon⟩ := hgood l halive32
  have hω := hGTω.2 hcf
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive32
  have hev1 : ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (historyTime c r l) ω) < (ver Ω c r l a).V (n + 1) ω :=
    (tendsto_add_atTop_nat 1).eventually (hcovω halive32 hcf (hcon a))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev1
  have hex : ∃ n : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (historyTime c r l) ω) < (ver Ω c r l a).V (n + 1) ω := ⟨N, hN N le_rfl⟩
  have hpre : slowPre h13 ver Ω c r l a ω =
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
        ((ver Ω c r l a).V (Nat.find hex + 1)) (historyTime c r l) ((ver Ω c r l a).R (Nat.find hex + 1)) ω := by
    unfold slowPre
    simp only [hex, ↓reduceDIte]
  have hflip : GW2Sdf.flipOf l.length = false := by
    rw [hlen]
    simp only [GW2Sdf.flipOf, decide_eq_false_iff_not, Nat.not_odd_iff_even]
    exact ⟨k + 2, by ring⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hVn := hN n hn
  have hslot : (V Ω c r).slowVar l a n = GW2Rv.slowStageVarX h13 c r l a ((ver Ω c r l a).isA hg.1)
      (fun _ => ch Ω c r l a) n := by
    rw [hvar]
    unfold GW2Rv.slowSlotX
    simp only [hg, ↓reduceDIte]
  have heqpre := hpω (n + 1) (Nat.find hex + 1) hcf ⟨hcon a, hVn⟩ ⟨hcon a, Nat.find_spec hex⟩
  change ((V Ω c r).slowVar l a n).record ω ∈ ((V Ω c r).slowVar l a n).E ∧
    GW2Sdf.PresentsO c.κ (((V Ω c r).slowVar l a n).β (((V Ω c r).slowVar l a n).record ω))
      (GW2Sdf.rootScale r.2) (GW2Sdf.flipOf l.length) ((V Ω c r).slowShell l a ω).xL
      (GW2TipSystem.RootL6.angleWordL c.κ ((V Ω c r).slowShell l a ω).φ ((V Ω c r).slowShell l a ω).mL
        ((V Ω c r).slowShell l a ω).ρL₀)
      ((V Ω c r).slowShell l a ω).xR
      (GW2TipSystem.RootL6.angleWordR c.κ ((V Ω c r).slowShell l a ω).φ ((V Ω c r).slowShell l a ω).mR
        ((V Ω c r).slowShell l a ω).ρR₀)
  rw [hslot, hsh, hflip]
  refine ⟨?_, ?_⟩
  · show augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
        ((ver Ω c r l a).V (n + 1)) (historyTime c r l) ((ver Ω c r l a).R (n + 1))) ω ∈
      ((ch Ω c r l a).E₀ ∩ GW2Sdi.succRec c r l) ∩
        aliveRecX ((entryList l).length + 1) (rootPt r.1) c.s ((ver Ω c r l a).isA hg.1 (n + 1)).1.2.choose
    refine ⟨⟨hE₀ Ω c r l a (hbad halive32 a _), (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).2 hold⟩, ?_⟩
    have hstart : (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
        ((ver Ω c r l a).V (n + 1)) (historyTime c r l) ω : ℝ≥0∞) < (ver Ω c r l a).V (n + 1) ω := by
      rw [GW2Sdo.stgStartX_eq_clockX hGT hg.2 hg.1 hω (hcon a) hVn]
      exact hVn
    exact GW2Sdo.mem_aliveRecX ((ver Ω c r l a).isA hg.1 (n + 1)).1.2.choose_spec.2.1
      (stgRecDec_stageEncRec c r l ω) ((((ver Ω c r l a).isA hg.1 (n + 1)).1.1).2.1 ω)
      ((((ver Ω c r l a).isA hg.1 (n + 1)).1.1).2.2.1 ω) hcf (hρω (n + 1)) hstart
  · show GW2Sdf.PresentsO c.κ ((ch Ω c r l a).β (augRec (stageEncRec c r l)
        (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V (n + 1)) (historyTime c r l) ((ver Ω c r l a).R (n + 1))) ω)) _ _ _ _ _ _
    have hrec : augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
        (schedGTX h13 c r l a) ((ver Ω c r l a).V (n + 1)) (historyTime c r l) ((ver Ω c r l a).R (n + 1))) ω =
        augRec (stageEncRec c r l) (slowPre h13 ver Ω c r l a) ω := by
      simp only [augRec, hpre, heqpre]
    rw [hrec, hβ]
    exact GW2Rs.presentsO_canonShell c.κ (slowWordOf h13 ver cw Ω c r l a ω) (candAngle c r l a) c.hκ c.hκ4 r.2
      (GW2Bf.histStart c r l ω)

/-- **The current top's base family** (the body of `Wire.T14Cur.baseWm cw`, at the Spec layer): GEOM2's root-`x` word
map at the history program and the candidate's angle, with record event off RELDET's `launchBadRec` (D26 (A′)). -/
def baseWmS (cw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω),
    ScaledRootIdx c.Θ c.Q → BoundaryWord) : GW2Sdh.SchedChoiceFamily.{u} := fun Ω _ _ c r l a =>
  GW2Wm.wmChoiceX c.κ (cw Ω c r) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
    (length_historyProgram c r l) (candAngle c r l a) (launchBadRec c r l a)ᶜ (fun _ => 0) (fun _ => ⊥)

/-- **The slow words for the current top's base family through RELDET's lines** (`hslow` with
`ch = schedChoiceLinesX h12 h13 (baseWmS cw)`). -/
theorem frameNSlowWordN_baseWm (h12 : Exist.Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (gap : RootCv.GapFamily.{u}) (lam : GW2Sdh.NearDil.{u}) (ver : GW2Rv.SchedVerXFamily.{u})
    (cw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω), ScaledRootIdx c.Θ c.Q →
      BoundaryWord)
    (hcov : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
        cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω)
    (V : GW2Sdx.VPkgXFamily.{u})
    (hvar : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ),
      (V Ω c r).slowVar l a n = GW2Rv.slowSlotX h13 ver (schedChoiceLinesX h12 h13 (baseWmS cw)) Ω c r l a n)
    (hsh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω),
      (V Ω c r).slowShell l a ω = slowShellOf h13 ver cw Ω c r l a ω) :
    GW2Sdx.FrameNSlowWordN (GW2Sdz.J32S gap) (fun n => (V.at n).frameN lam) :=
  frameNSlowWordN_slowShellOf h13 gap lam ver cw (schedChoiceLinesX h12 h13 (baseWmS cw))
    (fun Ω _ _ c r l a => by rw [schedChoiceLinesX_β]; rfl)
    (fun Ω _ _ c r l a => by rw [schedChoiceLinesX_E₀]; exact le_rfl) hcov V hvar hsh

end InteractingSLE.Theorem14.GW2Sdt
