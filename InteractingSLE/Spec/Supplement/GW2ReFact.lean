/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjFact
import InteractingSLE.Spec.Supplement.GW2ReCert

/-!
# Guarded copies: split-free signs and D33's shell field (D75 (3), option (G))

PROVE-GW2-ROOTX round 15. ROOTX's `GW2Rj.splitFree_signs_of_goodSample`, `shellFact_of_version`, `rjShell_fact` and
`rjShell_fact_scaled` with the record-event identity `E₀ = (launchBadRec)ᶜ` assumed only on guarded histories
(`Wire.T14Gd.Guard`). They read it only through `winCert_of_subG`, at alive (hence guarded) sub-histories. Otherwise
verbatim.

* `splitFree_signs_of_goodSampleG`, `shellFact_of_versionG`, `rjShell_factG`, **`rjShell_fact_scaledG`** (`hshell` on
  the guarded base).
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

section ShellG

open GW2Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {h13 : Exist.Theorem13Statement.{u}}
  {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}}

/-- **The decoded past at a good sample is split-free, with nonempty junction regions.** -/
theorem splitFree_signs_of_goodSampleG {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {cw : BoundaryWord}
    (hβ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ cw (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), Wire.T14Gd.Guard c r l →
      (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
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
    fun j hj1 hjN => winCert_of_goodSampleG hβ hE₀ h hω hl a n hV hj1 hjN
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

end ShellG

section FactG

variable {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}}
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}

/-- **The shell of a version beyond the clock**, at a good sample. -/
theorem shellFact_of_versionG (h : GoodRoot c r) {cw : BoundaryWord}
    (hβ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ cw (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), Wire.T14Gd.Guard c r l →
      (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    {ω : Ω} (hω : GoodSample h13 ver ch c r h ω) {l : List (EntryIdx c.Θ c.Q)} (hl2 : 1 ≤ l.length)
    (halive : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l) (a n : ℕ)
    (hn : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
      (ver Ω c r l a).V n ω)
    (hsU : ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
      GW2Sdf.PresentsO c.κ (schedWordMapX c.κ cw (rootPt r.1) c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l) (GW2Rd.candAngle c r l a)
        (slowRecV h13 ver c r l a n ω)) (GW2Sdf.rootScale r.2) false xL ρL xR ρR →
      (GW2Bf.histStart c r l ω, xL, xR) ∈ Sec5.Prop59Stage.startsU) :
    GW2Sdy.ShellFactLe c.κ (Cstar c.κ cw (rootPt r.1) c.s)
      (optShell c.κ (schedWordMapX c.κ cw (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
        (GW2Rd.length_historyProgram c r l) (GW2Rd.candAngle c r l a) (slowRecV h13 ver c r l a n ω))
        (GW2Rd.candAngle c r l a) r.2 (GW2Bf.histStart c r l ω)) := by
  have hgood := (hω.good l halive).1
  have hTc := (hω.good l halive).2 a
  have hωG := (hω.gt l a).2 hgood
  have hver := hω.vat l a n hgood
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive
  have hdec := baseWordX_slowRecV (n := n) h cw hωG hver hord hold hTc
  obtain ⟨hsplit, hL, hR⟩ := splitFree_signs_of_goodSampleG hβ hE₀ h hω hl2 halive a n hn
  obtain ⟨hpres, hang, hdrift⟩ := optShell_schedWordMapX c.hκ c.hκ4 hdec (GW2Sds.progAngle_mem_Icc c r l)
    (candAngle_mem_Icc c r l a) hsplit hL hR r.2 (GW2Bf.histStart c r l ω)
  exact ⟨hang, hsU hpres, hdrift⟩

/-- **D33's shell field at every alive history.** -/
theorem rjShell_factG (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hI : InstInputsX h13 ver ch) (cw : CfWordFam.{u})
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
        (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
        (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), Wire.T14Gd.Guard c r l →
      (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (k : ℕ)
    (l : List (EntryIdx c.Θ c.Q)) (hl : l.length = 2 * k + 4) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      GW2Sdy.ShellFactLe c.κ (Cstar c.κ (cw Ω c r) (rootPt r.1) c.s) (rjShell h13 ver (cw Ω c r) c r l a ω) ∧
        (rjShell h13 ver (cw Ω c r) c r l a ω).start = GW2Bf.histStart c r l ω := by
  by_cases h : GoodRoot c r
  swap
  · filter_upwards [ae_goodRoot_of_gate h13 c r l] with ω hG halive
    have hcov : ω ∈ RootCv.coverEvent c r := GW2JDetR12.aliveTests_subset _ _ _ l halive
    exact absurd (hG ⟨hcov, RootJ32.oldSuccess_of_alive c r l ω halive⟩) h
  have heven : Even l.length := ⟨k + 2, by omega⟩
  have hsU : ∀ᵐ ω ∂c.P, ∀ n : ℕ,
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l → 2 ≤ l.length →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
        (ver Ω c r l a).V n ω →
      ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
        GW2Sdf.PresentsO c.κ (schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l) (GW2Rd.candAngle c r l a)
          (slowRecV h13 ver c r l a n ω)) (GW2Sdf.rootScale r.2) false xL ρL xR ρR →
        (GW2Bf.histStart c r l ω, xL, xR) ∈ Sec5.Prop59Stage.startsU :=
    ae_all_iff.2 fun n => GW2Ru.ae_startsU_of_presentsO h13 c r h.1 l heven a
      ((ver Ω c r l a).isA h.1 n).1.1 ((ver Ω c r l a).fin n) c.κ (cw Ω c r) (GW2Rd.candAngle c r l a)
  filter_upwards [ae_goodSample h12p h12p₀ h13₀ hI c r h, hsU, GW2Rw.ae_histStart_mem_of_alive h13 c r]
    with ω hω hsU hband halive
  refine ⟨?_, rjShell_start h13 ver (cw Ω c r) c r l a ω⟩
  have hl2 : 1 ≤ l.length := by omega
  unfold rjShell
  split_ifs with hex
  · exact shellFact_of_versionG h (hβ Ω c r) (hE₀ Ω c r) hω hl2 halive a (Nat.find hex) (Nat.find_spec hex)
      (hsU (Nat.find hex) halive (by omega) (Nat.find_spec hex))
  · obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
      rcases l with _ | ⟨x, l'⟩
      · simp at hl2
      · exact ⟨x, l', rfl⟩
    exact shellFactLe_trivShell c.hκ c.hκ4 (hband x l' halive) (cw Ω c r) (rootPt r.1) c.s

/-- **D33's shell field on SDE's scaled cover.** -/
theorem rjShell_fact_scaledG (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hI : InstInputsX h13 ver ch) (cw : CfWordFam.{u})
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
        (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
        (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), Wire.T14Gd.Guard c r l →
      (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)) (hl : l.length = 2 * k + 4) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      GW2Sdy.ShellFactLe c.κ (Cstar c.κ (cw Ω c r) (rootPt r.1) c.s) (rjShell h13 ver (cw Ω c r) c r l a ω) ∧
        (rjShell h13 ver (cw Ω c r) c r l a ω).start = GW2Bf.histStart c r l ω := by
  filter_upwards [rjShell_factG h12p h12p₀ h13₀ hI cw hβ hE₀ Ω c r k l hl a] with ω hω halive
  exact hω (GW2Sdz.alive_scaled_subset gap Ω c r l halive)

end FactG

end InteractingSLE.Theorem14.GW2Rj
