/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RkSlow
import InteractingSLE.Spec.Supplement.GW2RlNear
import InteractingSLE.Spec.Supplement.GW2ReFact

/-!
# Guarded copies: the slow words for D33's shells and the near slots' words (D75 (3), option (G))

PROVE-GW2-ROOTX round 15. ROOTX's `GW2Rk.presentsO_rjShell`, `GW2Rk.frameNSlowWordN_rjShell` and
`GW2Rl.ae_nearSlotWords` with the record-event identity `E₀ = (launchBadRec)ᶜ` assumed only on guarded histories
(`Wire.T14Gd.Guard`). They read it at alive (hence guarded) histories (`GW2Re.guard_of_alive32`). Otherwise verbatim.

* `presentsO_rjShellG`, **`frameNSlowWordN_rjShellG`** (the slow part of `hwords` on the guarded base);
* **`ae_nearSlotWordsG`** (the near slots' words on the guarded base).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rk

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2Rq GW2Rv GW2Rz GW2Sde
  GW2Sdh GW2Sdx GW2Wm GW2Rj

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {h13 : Exist.Theorem13Statement.{u}}
  {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}} {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}

/-- **D33's shell presents the slow record's word** at a good sample, once a version passes the history clock. -/
theorem presentsO_rjShellG (h : GoodRoot c r) {cw : BoundaryWord}
    (hβ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ cw (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), Wire.T14Gd.Guard c r l →
      (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    {ω : Ω} (hω : GoodSample h13 ver ch c r h ω) {l : List (EntryIdx c.Θ c.Q)} (hl2 : 1 ≤ l.length)
    (halive : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l) (a : ℕ)
    (hex : ∃ n : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l a).V n ω) :
    GW2Sdf.PresentsO c.κ (schedWordMapX c.κ cw (rootPt r.1) c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l) (GW2Rd.candAngle c r l a)
        (slowRecV h13 ver c r l a (Nat.find hex) ω)) (GW2Sdf.rootScale r.2) false
      (rjShell h13 ver cw c r l a ω).xL
      (angleWordL c.κ (rjShell h13 ver cw c r l a ω).φ (rjShell h13 ver cw c r l a ω).mL
        (rjShell h13 ver cw c r l a ω).ρL₀)
      (rjShell h13 ver cw c r l a ω).xR
      (angleWordR c.κ (rjShell h13 ver cw c r l a ω).φ (rjShell h13 ver cw c r l a ω).mR
        (rjShell h13 ver cw c r l a ω).ρR₀) := by
  have e : rjShell h13 ver cw c r l a ω = optShell c.κ (schedWordMapX c.κ cw (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a) (slowRecV h13 ver c r l a (Nat.find hex) ω)) (GW2Rd.candAngle c r l a) r.2
      (GW2Bf.histStart c r l ω) := by
    unfold rjShell
    simp only [hex, ↓reduceDIte]
  rw [e]
  have hgood := (hω.good l halive).1
  have hTc := (hω.good l halive).2 a
  have hωG := (hω.gt l a).2 hgood
  have hver := hω.vat l a (Nat.find hex) hgood
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive
  have hdec := baseWordX_slowRecV (n := Nat.find hex) h cw hωG hver hord hold hTc
  obtain ⟨hsplit, hL, hR⟩ := splitFree_signs_of_goodSampleG hβ hE₀ h hω hl2 halive a (Nat.find hex)
    (Nat.find_spec hex)
  exact (optShell_schedWordMapX c.hκ c.hκ4 hdec (GW2Sds.progAngle_mem_Icc c r l)
    (candAngle_mem_Icc c r l a) hsplit hL hR r.2 (GW2Bf.histStart c r l ω)).1

/-- **The slow words for D33's shells** (`hslow`): for every package whose slow slots are `pkgX`'s and whose slow
shells are `rjShell`, with a choice family carrying GEOM2's word map and D42's record event, instance inputs, and a
version family whose stops eventually pass the history clock. -/
theorem frameNSlowWordN_rjShellG (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hI : InstInputsX h13 ver ch) (gap : RootCv.GapFamily.{u}) (lam : NearDil.{u}) (cw : CfWordFam.{u})
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
        (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
        (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), Wire.T14Gd.Guard c r l →
      (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (hcov : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
        cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
          (RootJ31.historyTime c r l) ω) < (ver Ω c r l a).V n ω)
    (V : VPkgXFamily.{u})
    (hvar : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ),
      (V Ω c r).slowVar l a n = slowSlotX h13 ver ch Ω c r l a n)
    (hsh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω),
      (V Ω c r).slowShell l a ω = rjShell h13 ver (cw Ω c r) c r l a ω) :
    FrameNSlowWordN (GW2Sdz.J32S gap) (fun n => (V.at n).frameN lam) := by
  intro Ω _ _ c r k l hlen a
  by_cases hg : GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hgood halive
    exact absurd (hgood (GW2Sdz.alive_scaled_subset gap Ω c r l halive)) hg
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  have hpair : ∀ᵐ ω ∂c.P, ∀ n m : ℕ, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      ((RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
          (ver Ω c r l a).V n ω) →
      ((RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
          (ver Ω c r l a).V m ω) →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V n)
          (RootJ31.historyTime c r l) ((ver Ω c r l a).R n) ω =
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V m)
          (RootJ31.historyTime c r l) ((ver Ω c r l a).R m) ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun m =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c r l a a hg.2 hg.1 ((ver Ω c r l a).isA hg.1 n).1.1
        ((ver Ω c r l a).isA hg.1 m).1.1
  have hρ : ∀ᵐ ω ∂c.P, ∀ n : ℕ, (ver Ω c r l a).V n ω =
      ((ver Ω c r l a).isA hg.1 n).1.2.choose (cfRec c.s c.W c.ζ ω, fun u => (ver Ω c r l a).R n u ω) :=
    ae_all_iff.2 fun n => ((ver Ω c r l a).isA hg.1 n).1.2.choose_spec.2.2
  filter_upwards [ae_goodSample h12p h12p₀ h13₀ hI c r hg, GW2Ru.ae_alive_goodEvent h13 c r, hGTae,
    hcov Ω c r l a hg, hpair, hρ, GW2Sdt.ae_notMem_launchBadRec h13 c r l] with ω hgs hgood hGTω hcovω hpω hρω hbad
    halive
  have halive32 := GW2Sdz.alive_scaled_subset gap Ω c r l halive
  obtain ⟨hcf, hcon⟩ := hgood l halive32
  have hω := hGTω.2 hcf
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive32
  have hev := hcovω halive32 hcf (hcon a)
  have hex : ∃ n : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l a).V n ω := hev.exists
  have hpres := presentsO_rjShellG hg (hβ Ω c r) (hE₀ Ω c r) hgs (by omega) halive32 a hex (cw := cw Ω c r)
  have hev1 : ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l a).V (n + 1) ω :=
    (tendsto_add_atTop_nat 1).eventually hev
  have hflip : GW2Sdf.flipOf l.length = false := by
    rw [hlen]
    simp only [GW2Sdf.flipOf, decide_eq_false_iff_not, Nat.not_odd_iff_even]
    exact ⟨k + 2, by ring⟩
  filter_upwards [hev1] with n hVn
  have hslot : (V Ω c r).slowVar l a n = slowStageVarX h13 c r l a ((ver Ω c r l a).isA hg.1)
      (fun _ => ch Ω c r l a) n := by
    rw [hvar]
    unfold slowSlotX
    simp only [hg, ↓reduceDIte]
  have heqpre := hpω (n + 1) (Nat.find hex) hcf ⟨hcon a, hVn⟩ ⟨hcon a, Nat.find_spec hex⟩
  change ((V Ω c r).slowVar l a n).record ω ∈ ((V Ω c r).slowVar l a n).E ∧
    GW2Sdf.PresentsO c.κ (((V Ω c r).slowVar l a n).β (((V Ω c r).slowVar l a n).record ω))
      (GW2Sdf.rootScale r.2) (GW2Sdf.flipOf l.length) ((V Ω c r).slowShell l a ω).xL
      (angleWordL c.κ ((V Ω c r).slowShell l a ω).φ ((V Ω c r).slowShell l a ω).mL
        ((V Ω c r).slowShell l a ω).ρL₀)
      ((V Ω c r).slowShell l a ω).xR
      (angleWordR c.κ ((V Ω c r).slowShell l a ω).φ ((V Ω c r).slowShell l a ω).mR
        ((V Ω c r).slowShell l a ω).ρR₀)
  rw [hslot, hsh, hflip]
  refine ⟨?_, ?_⟩
  · show GW2Rd.augRec (GW2Rd.stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
        (schedGTX h13 c r l a) ((ver Ω c r l a).V (n + 1)) (RootJ31.historyTime c r l)
        ((ver Ω c r l a).R (n + 1))) ω ∈
      ((ch Ω c r l a).E₀ ∩ GW2Sdi.succRec c r l) ∩
        aliveRecX ((entryList l).length + 1) (rootPt r.1) c.s ((ver Ω c r l a).isA hg.1 (n + 1)).1.2.choose
    refine ⟨⟨?_, (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).2 hold⟩, ?_⟩
    · rw [hE₀ Ω c r l a (GW2Re.guard_of_alive32 c r l halive32)]
      exact hbad halive32 a _
    have hstart : (stgStartX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a)
        ((ver Ω c r l a).V (n + 1)) (RootJ31.historyTime c r l) ω : ℝ≥0∞) < (ver Ω c r l a).V (n + 1) ω := by
      rw [GW2Sdo.stgStartX_eq_clockX hGT hg.2 hg.1 hω (hcon a) hVn]
      exact hVn
    exact GW2Sdo.mem_aliveRecX ((ver Ω c r l a).isA hg.1 (n + 1)).1.2.choose_spec.2.1
      (GW2Rd.stgRecDec_stageEncRec c r l ω) ((((ver Ω c r l a).isA hg.1 (n + 1)).1.1).2.1 ω)
      ((((ver Ω c r l a).isA hg.1 (n + 1)).1.1).2.2.1 ω) hcf (hρω (n + 1)) hstart
  · show GW2Sdf.PresentsO c.κ ((ch Ω c r l a).β (GW2Rd.augRec (GW2Rd.stageEncRec c r l)
        (stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V (n + 1)) (RootJ31.historyTime c r l) ((ver Ω c r l a).R (n + 1))) ω)) _ _ _ _ _ _
    have hrec : GW2Rd.augRec (GW2Rd.stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ
        (GW2Rd.schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V (n + 1)) (RootJ31.historyTime c r l)
        ((ver Ω c r l a).R (n + 1))) ω = slowRecV h13 ver c r l a (Nat.find hex) ω := by
      simp only [GW2Rd.augRec, slowRecV, heqpre]
    rw [hrec, hβ]
    exact hpres

end InteractingSLE.Theorem14.GW2Rk

namespace InteractingSLE.Theorem14.GW2Rl

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

variable {h13 : Exist.Theorem13Statement.{u}}

/-- **The near slots' words** of ROOTX's package for a uniformly covering version family and the reference near
base (any choice family with GEOM2's word map and D42's `E₀`, any base package). -/
theorem ae_nearSlotWordsG (ver : SchedVerXFamily.{u}) {ch : SchedChoiceFamily.{u}} (cw : GW2Rj.CfWordFam.{u})
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = GW2Wm.schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
        (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
        (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), Wire.T14Gd.Guard c r l →
      (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (hU : UnifCover ver) (K : PkgFamily.{u}) (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ Wire.T14Cur.aliveS gap Ω c r l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ a : ℕ,
      ((pkgX h13 ver ch K Ω c r).nearVar l n m a).record ω ∈ ((pkgX h13 ver ch K Ω c r).nearVar l n m a).E ∧
      ((pkgX h13 ver ch K Ω c r).nearVar l n m a).β (((pkgX h13 ver ch K Ω c r).nearVar l n m a).record ω) =
        GW2Rd.upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ) (refNb h13 ver cw Ω c r l ω) := by
  classical
  by_cases hg : GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hω halive
    exact absurd (hω (GW2Sdz.alive_scaled_subset gap Ω c r l halive)) hg
  obtain ⟨hx, hs⟩ := hg
  have hpair : ∀ᵐ ω ∂c.P, ∀ p q : ℕ × ℕ, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l p.1) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) (RootJ31.historyTime c r l) ω) <
          (ver Ω c r l p.1).V p.2 ω) →
      (((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l q.1) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l q.1) (RootJ31.historyTime c r l) ω) <
          (ver Ω c r l q.1).V q.2 ω) →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) (schedGTX h13 c r l p.1) ((ver Ω c r l p.1).V p.2)
          (RootJ31.historyTime c r l) ((ver Ω c r l p.1).R p.2) ω =
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l q.1) (schedGTX h13 c r l q.1) ((ver Ω c r l q.1).V q.2)
          (RootJ31.historyTime c r l) ((ver Ω c r l q.1).R q.2) ω :=
    ae_all_iff.2 fun p => ae_all_iff.2 fun q =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c r l p.1 q.1 hs hx ((ver Ω c r l p.1).isA hx p.2).1.1
        ((ver Ω c r l q.1).isA hx q.2).1.1
  have hρ : ∀ᵐ ω ∂c.P, ∀ p : ℕ × ℕ, (ver Ω c r l p.1).V p.2 ω =
      ((ver Ω c r l p.1).isA hx p.2).1.2.choose (cfRec c.s c.W c.ζ ω, fun u => (ver Ω c r l p.1).R p.2 u ω) :=
    ae_all_iff.2 fun p => ((ver Ω c r l p.1).isA hx p.2).1.2.choose_spec.2.2
  have hGTall : ∀ᵐ ω ∂c.P, ∀ a, ω ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s :=
    ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2
  filter_upwards [hpair, hρ, hGTall, GW2Sdt.ae_notMem_launchBadRec h13 c r l,
    GW2Ru.ae_alive_goodEvent_scaled h13 gap c r, hU Ω c r l ⟨hx, hs⟩]
    with ω hpω hρω hGTω hlaunch hgoodEv hUω halive n
  have halive32 := GW2Sdz.alive_scaled_subset gap Ω c r l halive
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive32
  filter_upwards [hUω halive32] with m hm a
  have hslot := hm a
  have hex0 : ∃ p : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair p).1)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l (Nat.unpair p).1).V (Nat.unpair p).2 ω :=
    ⟨Nat.pair a m, by rw [Nat.unpair_pair]; exact hslot⟩
  have hpre : stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V m)
      (RootJ31.historyTime c r l) ((ver Ω c r l a).R m) ω = refPreV h13 ver Ω c r l ω := by
    simp only [refPreV, hex0, ↓reduceDIte]
    exact hpω (a, m) ((Nat.unpair (Nat.find hex0)).1, (Nat.unpair (Nat.find hex0)).2) hcf ⟨hcon a, hslot⟩
      ⟨hcon _, Nat.find_spec hex0⟩
  rw [pkgX_nearVar_eq K c r ⟨hx, hs⟩ l n m a]
  have hA := (ver Ω c r l a).isA hx m
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · show augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((ver Ω c r l a).V m) (RootJ31.historyTime c r l) ((ver Ω c r l a).R m)) ω ∈ (ch Ω c r l a).E₀
    rw [hE₀ Ω c r l a (GW2Re.guard_of_alive32 c r l halive32)]
    exact hlaunch halive32 a _
  · exact (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).2 hold
  · have hstart : (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V m)
        (RootJ31.historyTime c r l) ω : ℝ≥0∞) < (ver Ω c r l a).V m ω := by
      rw [GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx ((hGTω a).2 hcf) (hcon a) hslot]
      exact hslot
    exact GW2Sdo.mem_aliveRecX hA.1.2.choose_spec.2.1 (stgRecDec_stageEncRec c r l ω) (hA.1.1.2.1 ω)
      (hA.1.1.2.2.1 ω) hcf (hρω (a, m)) hstart
  · show (ch Ω c r l a).β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (schedGTX h13 c r l a) ((ver Ω c r l a).V m) (RootJ31.historyTime c r l) ((ver Ω c r l a).R m)) ω) = _
    rw [hβ]
    unfold GW2Wm.schedWordMapX refNb
    rw [GW2Rj.candAngle_eq]
    congr 2
    simp only [augRec, hpre]

end InteractingSLE.Theorem14.GW2Rl
