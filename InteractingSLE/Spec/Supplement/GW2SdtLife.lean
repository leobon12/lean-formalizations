/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdtSeed
import InteractingSLE.Spec.Supplement.GW2SdsPhys
import InteractingSLE.Spec.Supplement.GW2TnExport

/-!
# Every candidate launched at an alive history has a positive lifetime (D45 item 2)

Packet PROVE-GW2-SDE (round 19, decision D45 (2): the near slots off `launchBadRec`). Almost surely, at every alive
history of J32 and for every candidate `a`, the candidate's lifetime is positive. Hence its stage record is off RELDET's
zero-lifetime set `launchBadRec` (decision D26 (A′)), so the near slots' records lie in the record event
`E₀ = (launchBadRec c r l a)ᶜ` of the current top's base family. Proof:

* the last history piece stops at an interior point (STAGEMEAN's `GW2Omx.ae_switchTips_cur`), so its record has both
  junctions strictly off the tip (`junctions_strict_of_interiorStop`, GEOM2's `Gm.ae_launched_rdrv_trace`);
* the canonical launch word agrees, off finite sets, with the explicit stop word of that piece
  (`ae_canonWord_fn_eq_stopWord`), whose one-sided limits at `0` are the piece's sides (`lims_stopWord_zero`);
* so the seed is not at a threshold for any candidate angle (`badDist_ne_zero_of_lims`), and RELDET's
  `GW2Rd.ae_life_pos_of_launch_good` gives the positive lifetime.

Results: **`ae_candLife_pos`**, **`ae_notMem_launchBadRec`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sdt

open Exist Exist.Staged Exist.StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The instruction angles of a schedule are its entries' angles. -/
theorem instrAngle_schedSpec (x : ℝ) {L : List (ℝ × ℝ≥0)} {j : ℕ} (hj : j < L.length) :
    instrAngle (schedSpec x L) j = schedAngle L j := by
  have hi := isFlowProg_scheduleProgram 0 L j (by rw [GW2Schedule.length_scheduleProgram]; exact hj)
  simp only [instrAngle, schedSpec, hi]

/-- **Every candidate launched at an alive history has a positive lifetime**, almost surely. -/
theorem ae_candLife_pos (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      0 < GW2Rd.candLife c r l a ω := by
  classical
  set x := rootPt r.1 with hx
  set Lh := historyProgram c r l with hLh
  set Lf := futureProgram c r l a with hLf
  set n := (entryList l).length with hn
  have hk : GW2Olm.curIdx c r l = n + 1 := GW2Ru.length_historyProgram c r l
  have hLhn : Lh.length = n + 1 := hk
  have hLfn : Lf.length = n + 2 := by
    simp only [hLf, futureProgram, List.length_append, List.length_singleton, ← hLh, hLhn]
  have hn1 : n + 1 < (scheduleProgram 0 Lf).length := by
    rw [GW2Schedule.length_scheduleProgram, hLfn]; omega
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 Lf⟩ with hspec
  set θ := specAngle spec with hθ
  set Δ := specDelta spec with hΔ
  set C := canonFam c.hκ c.h12p c.βA c.c₀ θ Δ x c.h with hC
  have hprog : IsFlowProg spec.2.2 θ Δ := isFlowProg_spec x true Lf
  have hΔt : ∀ j, Δ j ≠ ⊤ := specDelta_ne_top spec
  by_cases hpw : Lh.Pairwise (fun p q => p.2 < q.2)
  swap
  · exact Eventually.of_forall fun ω halive =>
      absurd (RootJ32.pairwise_lt_historyProgram_of_alive c r l ω halive) hpw
  filter_upwards [GW2Rd.ae_life_pos_of_launch_good h13 c r l a,
    ae_canonWord_fn_eq_stopWord c.hκ c.h12p h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh x Lf n hn1,
    GW2Omx.ae_switchTips_cur h13 c r l a hpw, Gm.ae_launched_rdrv_trace h13 c x Lf]
    with ω hlife hexpl hsw htr halive
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive
  -- the pieces of the future schedule succeed up to the candidate
  have hs : AllSucc Δ (fun j => C j ω) (n + 1) := by
    have h := Gm.allSucc_future_of_oldSuccess c r l a ω hold
    rw [← hLh, hLhn] at h
    exact h
  have hsn : Δ n < (C n ω).2 := hs n (Nat.lt_succ_self n)
  refine hlife hold ?_
  show GW2Rd.badDist c.κ (specAngle spec (GW2Olm.curIdx c r l))
    (canonWord c.hκ c.h12p c.βA c.c₀ θ Δ c.κ c.b c.jumps spec c.h (GW2Olm.curIdx c r l) ω) 0 ≠ 0
  rw [hk]
  -- the record of the last history piece
  set rn := pastMap c.κ c.b c.jumps spec C (n + 1) ω (Fin.last n) with hrn
  have hrn' : rn = recOf (Δ n) (C n ω) := by
    have h := congrFun (GW2Schedule.pastMap_of_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl hprog hΔt C
      (k := n + 1) (by rw [GW2Schedule.length_scheduleProgram, hLfn]; omega) hs) (Fin.last n)
    rw [hrn, h]
    simp only [Fin.val_last]
  set Δn : ℝ≥0 := (Δ n).toNNReal with hΔn
  have hΔe : (Δn : ℝ≥0∞) = Δ n := ENNReal.coe_toNNReal (hΔt n)
  rw [← hΔe] at hrn' hsn
  -- the last piece's stop is interior
  have hfs : AllSucc (schedDelta 0 Lf) (fun i => GW2Olm.futFam c r l a i ω) (GW2Olm.curIdx c r l) := by
    intro i hi
    have h1 := hs i (by rw [hk] at hi; exact hi)
    have h2 : Δ i = schedDelta 0 Lf i := Gm.specDelta_schedSpec x (by rw [hk] at hi; omega)
    rw [h2] at h1
    exact h1
  have hint := hsw hfs n (by rw [hk]; exact Nat.lt_succ_self n)
  have hinstr : instrTime (GW2Olm.futSpec c r l a) n = Δ n :=
    GW2Schedule.instrTime_eq (θ := θ) (Δ := Δ) hprog (by show n < (scheduleProgram 0 Lf).length; omega)
  have hstop : GW2aMulti.pieceStop (GW2Olm.futSpec c r l a) (fun i => GW2Olm.futFam c r l a i ω) n =
      (Δn : ℝ≥0∞) := by
    unfold GW2aMulti.pieceStop
    rw [hinstr, ← hΔe]
    show min (Δn : ℝ≥0∞) (C n ω).2 = Δn
    exact min_eq_left hsn.le
  change GW2Later.IsInteriorStop (C n ω).1
    (GW2aMulti.pieceStop (GW2Olm.futSpec c r l a) (fun i => GW2Olm.futFam c r l a i ω) n) at hint
  rw [hstop] at hint
  obtain ⟨-, η, hη⟩ := htr n (by rw [hLfn]; omega) (hs.mono (Nat.le_succ n))
  have hreg := isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ θ Δ x c.h n ω
  have hη' : IsGeneratingTrace (fun t : ℝ≥0 => rdrv (recOf (Δn : ℝ≥0∞) (C n ω)) t) ⊤ η := by
    rw [hΔe]; exact hη
  obtain ⟨hjL, hjR⟩ := junctions_strict_of_interiorStop hreg hsn hη' hint
  rw [← hrn'] at hjL hjR
  -- the launch word's one-sided limits at the tip
  have hlims0 := lims_stopWord_zero c.hκ
    (canonWord c.hκ c.h12p c.βA c.c₀ θ Δ c.κ c.b c.jumps spec c.h n ω) (instrAngle spec n) rn hjL hjR
  have hoff := hexpl hs
  have hlims := GW1.lims_eq_of_eq_off_finset _ hoff 0
  -- the angles
  have hθn : instrAngle spec n ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [show spec = schedSpec x Lf from rfl, instrAngle_schedSpec x (by rw [hLfn]; omega)]
    exact GW2Later.schedAngle_mem_Icc (GW2Olm.mem_Icc_futureProgram c r l a) (by rw [hLfn]; omega)
  have hθa : specAngle spec (n + 1) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [show specAngle spec (n + 1) = instrAngle (schedSpec x Lf) (n + 1) from rfl,
      instrAngle_schedSpec x (by rw [hLfn]; omega)]
    exact GW2Later.schedAngle_mem_Icc (GW2Olm.mem_Icc_futureProgram c r l a) (by rw [hLfn]; omega)
  exact badDist_ne_zero_of_lims c.hκ c.hκ4 _ hθa hθn (hlims.1.trans hlims0.1) (hlims.2.trans hlims0.2)

/-- **The near slots' records are off `launchBadRec`**: almost surely, at every alive history, every stage record of
every candidate (any second component) is outside RELDET's zero-lifetime set, i.e. in the base family's record
event `E₀ = (launchBadRec c r l a)ᶜ`. -/
theorem ae_notMem_launchBadRec (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ∀ (a : ℕ) (y : Ω → RecData), GW2Rd.augRec (GW2Rd.stageEncRec c r l) y ω ∉ GW2Rd.launchBadRec c r l a := by
  have : ∀ᵐ ω ∂c.P, ∀ a : ℕ, (ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      0 < GW2Rd.candLife c r l a ω) ∧ (RootJ31.oldSuccess c r l ω → ∀ y : Ω → RecData,
        (GW2Rd.augRec (GW2Rd.stageEncRec c r l) y ω ∈ GW2Rd.launchBadRec c r l a ↔
          GW2Rd.candLife c r l a ω = 0)) :=
    ae_all_iff.2 fun a => (ae_candLife_pos h13 c r l a).and (GW2Rd.ae_mem_launchBadRec_iff c r l a h13)
  filter_upwards [this] with ω hω halive a y hmem
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive
  have h0 := ((hω a).2 hold y).1 hmem
  exact (lt_irrefl 0) (h0 ▸ (hω a).1 halive)

end InteractingSLE.Theorem14.GW2Sdt
