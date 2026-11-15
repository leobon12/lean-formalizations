/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjCertB
import InteractingSLE.Spec.Supplement.GW2RwStart
import InteractingSLE.Spec.Supplement.GW2RootK32Retained
import InteractingSLE.Spec.Supplement.GW2SdzPair

/-!
# The slow shell of D33 and its drift bound at every alive history (decision D33)

PROVE-GW2-ROOTX round 9, the shell field. **`rjShell`**: at `(l, a)`, the optimal shell (round 8's `optShell`) of the
raised stage word of the slow record of the least version of `ver` beyond the history's clock, started at
`GW2Bf.histStart` (the trivial shell if no version reaches the clock). **`rjShell_fact`**: almost surely at every
alive history of length `2k + 4`, for every candidate, the shell satisfies `ShellFactLe κ (Cstar …)` and starts at
`histStart`:

* the slow record decodes to the decoded past of the version (`baseWordX_slowRecV`);
* the past is split-free with `junctionL < 0 < junctionR` (`splitFreePast_of_certs`, `junction_signs_of_certs`, from
  the window certificates at a good sample, `winCert_of_goodSample`);
* round 8's `optShell_schedWordMapX` gives the presentation, the separated angles and `drift ≤ Cstar`; round 6's
  `ae_startsU_of_presentsO` the start clause.
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

section Shell

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The slow record of version `n`** at `(l, a)`. -/
abbrev slowRecV (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) : Ω → RecData :=
  GW2Rd.augRec (GW2Rd.stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
    (schedGTX h13 c r l a) ((ver Ω c r l a).V n) (RootJ31.historyTime c r l) ((ver Ω c r l a).R n))

/-- **The trivial shell** at a start: no marks but the right seed at `0`. -/
def trivShell (start : ℝ) : SlowShell where
  nL₀ := 0
  nR₀ := 0
  ρL₀ := fun _ => 0
  ρR₀ := fun _ => 0
  mL := 0
  mR := 0
  φ := fun _ => 0
  xL := fun _ => 0
  xR := fun _ => 0
  start := start

open Classical in
/-- **The slow shell of D33** at `(l, a)`. -/
def rjShell (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) [StandardBorelSpace Ω]
    (cw : BoundaryWord) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ω : Ω) : SlowShell :=
  if hex : ∃ n : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l a).V n ω then
    optShell c.κ (schedWordMapX c.κ cw (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
      (GW2Rd.length_historyProgram c r l) (GW2Rd.candAngle c r l a) (slowRecV h13 ver c r l a (Nat.find hex) ω))
      (GW2Rd.candAngle c r l a) r.2 (GW2Bf.histStart c r l ω)
  else trivShell (GW2Bf.histStart c r l ω)

theorem rjShell_start (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) [StandardBorelSpace Ω]
    (cw : BoundaryWord) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ω : Ω) : (rjShell h13 ver cw c r l a ω).start = GW2Bf.histStart c r l ω := by
  unfold rjShell
  split_ifs <;> rfl

/-- **The trivial shell's facts**, for an admissible start. -/
theorem shellFactLe_trivShell {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {start : ℝ}
    (hst : start ∈ Ioo (-(9 / 4)) (-(7 / 4))) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) :
    GW2Sdy.ShellFactLe κ (Cstar κ c' x s) (trivShell start) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hlam : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  refine ⟨fun _ => ?_, ⟨hst.1, hst.2, ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩,
    fun k hk => ?_⟩, ?_⟩
  · show (0 : ℝ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
    constructor <;> linarith [Real.pi_pos]
  · exact absurd hk (by have := k.isLt; simp only [trivShell] at this; omega)
  · have hM : 0 ≤ max (rootM κ c' x s) (sleLambda κ + Real.pi / 2 * chiC κ) + Real.pi / 2 * chiC κ := by
      have h1 : 0 ≤ sleLambda κ + Real.pi / 2 * chiC κ := by positivity
      have h2 : 0 ≤ Real.pi / 2 * chiC κ := by positivity
      linarith [le_max_right (rootM κ c' x s) (sleLambda κ + Real.pi / 2 * chiC κ)]
    have hD : 0 ≤ 4 * ((rootN₀ κ c' x s : ℝ) + 1) *
        (max (rootM κ c' x s) (sleLambda κ + Real.pi / 2 * chiC κ) + Real.pi / 2 * chiC κ) / sleLambda κ :=
      div_nonneg (mul_nonneg (by positivity) hM) hlam.le
    show Sec5.Prop59Stage.stageDriftBound κ (trivShell start).ρL₀ (trivShell start).ρR₀ ≤ Cstar κ c' x s
    unfold Sec5.Prop59Stage.stageDriftBound Cstar driftC
    simp only [trivShell, abs_zero, Finset.sum_const_zero, add_zero, mul_zero]
    linarith

end Shell

section Fact

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {h13 : Exist.Theorem13Statement.{u}}
  {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}}

/-- **The slow record of version `n` decodes to its decoded past.** -/
theorem baseWordX_slowRecV {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} (h : GoodRoot c r)
    {l : List (EntryIdx c.Θ c.Q)} {a n : ℕ} (cw : BoundaryWord) {ω : Ω} (hωG : ω ∈ schedGTX h13 c r l a)
    (hver : VersionAtX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (GW2Rd.schedTr c r l a) c.α
      ((ver Ω c r l a).R n) ((ver Ω c r l a).V n) ω)
    (hord : HistOrdered c r l) (hold : RootJ31.oldSuccess c r l ω)
    (hTc : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω) :
    baseWordX c.κ cw (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
        (GW2Rd.length_historyProgram c r l) (slowRecV h13 ver c r l a n ω) =
      GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ cw (rootPt r.1) c.s) (progAngle (RootJ31.historyProgram c r l))
        ((entryList l).length + 1)
        (pastOf (cfRec c.s c.W c.ζ ω) (fun u => (ver Ω c r l a).R n u ω) (bdX h13 ver c r l a n ω)
          ((entryList l).length + 1)) := by
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
  exact baseWordX_augRecX (x₀ := rootPt r.1) (sp := c.s) (W := GW2Rd.schedW c r l a) (Wα := c.W) (ζα := c.ζ)
    (GT := schedGTX h13 c r l a) (V := (ver Ω c r l a).V n) (T := RootJ31.historyTime c r l)
    (R := (ver Ω c r l a).R n) (γ := GW2Rd.schedTr c r l a) (α := c.α) c.κ cw hGT h.2 h.1
    (RootJ31.historyProgram c r l) ((entryList l).length + 1) hLN (xr := GW2Rd.stageEncRec c r l) (ω := ω)
    (P := fun j : Fin ((entryList l).length + 1) => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω)
    rfl hver.1 hver.2.1 hωG ((ver Ω c r l a).fin n ω) hTj hjT hcon hagree

/-- **The decoded past at a good sample is split-free, with nonempty junction regions.** -/
theorem splitFree_signs_of_goodSample {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {cw : BoundaryWord}
    (hβ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ cw (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (h : GoodRoot c r) {ω : Ω} (hω : GoodSample h13 ver ch c r h ω) {l : List (EntryIdx c.Θ c.Q)}
    (hl2 : 1 ≤ l.length)
    (hl : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l) (a n : ℕ)
    (hV : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
      (ver Ω c r l a).V n ω) :
    SplitFreePast ((entryList l).length + 1)
        (pastOf (cfRec c.s c.W c.ζ ω) (fun u => (ver Ω c r l a).R n u ω) (bdX h13 ver c r l a n ω)
          ((entryList l).length + 1)) ∧
      GW2Sdp.junctionL ((entryList l).length + 1)
          (pastOf (cfRec c.s c.W c.ζ ω) (fun u => (ver Ω c r l a).R n u ω) (bdX h13 ver c r l a n ω)
            ((entryList l).length + 1)) < 0 ∧
      0 < GW2Sdp.junctionR ((entryList l).length + 1)
          (pastOf (cfRec c.s c.W c.ζ ω) (fun u => (ver Ω c r l a).R n u ω) (bdX h13 ver c r l a n ω)
            ((entryList l).length + 1)) := by
  have hs : 0 < c.s := h.2
  have hx : 0 ≤ rootPt r.1 := h.1
  have hgood := (hω.good l hl).1
  have hTc := (hω.good l hl).2 a
  have hωG := (hω.gt l a).2 hgood
  obtain ⟨hGT, -, -⟩ := schedGTX_spec h13 c r l a
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω hl
  have hver := hω.vat l a n hgood
  have hLN : (RootJ31.historyProgram c r l).length = (entryList l).length + 1 := GW2Ru.length_historyProgram c r l
  have hTL : schedTime 0 (RootJ31.historyProgram c r l) ((entryList l).length + 1) = RootJ31.historyTime c r l := by
    rw [← hLN]; rfl
  have hbmono : Monotone (bdX h13 ver c r l a n ω) := trueBdX_mono hGT hs hx hLN hTL hord hωG hTc hV
  have hcert : ∀ j, 1 ≤ j → j < (entryList l).length + 1 →
      WinCert (fun u => (ver Ω c r l a).R n u ω) (bdX h13 ver c r l a n ω) (cfRec c.s c.W c.ζ ω) j :=
    fun j hj1 hjN => winCert_of_goodSample hβ hE₀ h hω hl a n hV hj1 hjN
  have hsplit := (splitFreePast_of_certs hver.1 hbmono (cfRec c.s c.W c.ζ ω) hcert _ le_rfl).1
  -- the last window has positive length
  have hlenl : (entryList l).length = l.length := by simp [entryList]
  obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
    rcases l with _ | ⟨x, l'⟩
    · simp at hl2
    · exact ⟨x, l', rfl⟩
  obtain ⟨a', -, ht⟩ := exists_test_of_alive_cons c r hl
  have hT'q := (RootJ32.test_spec c r l' a' x.2 ω ht).1
  have hxq : RootJ31.historyTime c r (x :: l') = (x.2 : ℝ≥0) := by
    obtain ⟨θ, q'⟩ := x
    exact Gm.historyTime_cons c r l' θ q'
  obtain ⟨hst1, -⟩ := schedTime_of_drop c r (l := x :: l') (k := 0) rfl
  have hbd : ∀ i : ℕ, 1 ≤ i → i ≤ (entryList (x :: l')).length + 1 →
      bdX h13 ver c r (x :: l') a n ω i =
        (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r (x :: l') a)
          (schedTime 0 (RootJ31.historyProgram c r (x :: l')) i) ω).toNNReal :=
    fun i h1 hiN => trueBdX_eq_clock (V := (ver Ω c r (x :: l') a).V n) hGT hs hx hLN hTL hord hωG hTc hV h1 hiN
  have hN1 : (entryList (x :: l')).length + 1 - 1 = l'.length + 1 := by simp [entryList]
  have hlast : bdX h13 ver c r (x :: l') a n ω ((entryList (x :: l')).length + 1 - 1) <
      bdX h13 ver c r (x :: l') a n ω ((entryList (x :: l')).length + 1) := by
    rw [hN1, hbd _ (by omega) (by simp [entryList]), hbd _ (by omega) le_rfl, hst1, hTL]
    have hsm := clockX_strictMonoOn hGT hs hx hωG
    have hc := hsm ((ENNReal.coe_lt_coe.2 (hT'q.trans_le hxq.symm.le)).trans hTc) hTc (hT'q.trans_le hxq.symm.le)
    exact (Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt (RootJ32.forwardCapacity_nonneg _ _ _ _) hc)).2 hc
  have hsigns := junction_signs_of_certs hver.1 hbmono (cfRec c.s c.W c.ζ ω)
    (N := (entryList (x :: l')).length + 1) (by simp [entryList]) hcert hlast
  exact ⟨hsplit, hsigns.1, hsigns.2⟩

end Fact

end InteractingSLE.Theorem14.GW2Rj
