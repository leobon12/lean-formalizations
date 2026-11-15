/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjShell

/-!
# The shell field: `ShellFactLe κ C*` at every alive history (decision D33)

PROVE-GW2-ROOTX round 9. **`rjShell_fact`**: for the instance inputs of a version family `ver` and a choice family
`ch` whose word map is GEOM2's (`hβ`) and whose record event is D42's `E₀ = (launchBadRec)ᶜ` (`hE₀`), almost surely at
every alive history of length `2k + 4`, for every candidate, D33's shell `rjShell` satisfies
`ShellFactLe κ (Cstar κ c' x s)` and starts at `histStart`. **`rjShell_fact_scaled`**: the same on SDE's scaled cover.
At roots that are not good the alive event is null (`ae_goodRoot_of_gate`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rq GW2Rv GW2Rz GW2Sde GW2Sdh GW2Sdx GW2Wm

/-- **A counterflow word for every source setup and root.** -/
abbrev CfWordFam : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω), ScaledRootIdx c.Θ c.Q → BoundaryWord

variable {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}}
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}

/-- **The shell of a version beyond the clock**, at a good sample. -/
theorem shellFact_of_version (h : GoodRoot c r) {cw : BoundaryWord}
    (hβ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ cw (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
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
  obtain ⟨hsplit, hL, hR⟩ := splitFree_signs_of_goodSample hβ hE₀ h hω hl2 halive a n hn
  obtain ⟨hpres, hang, hdrift⟩ := optShell_schedWordMapX c.hκ c.hκ4 hdec (GW2Sds.progAngle_mem_Icc c r l)
    (candAngle_mem_Icc c r l a) hsplit hL hR r.2 (GW2Bf.histStart c r l ω)
  exact ⟨hang, hsU hpres, hdrift⟩

/-- **D33's shell field at every alive history.** -/
theorem rjShell_fact (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hI : InstInputsX h13 ver ch) (cw : CfWordFam.{u})
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
        (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
        (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
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
  · exact shellFact_of_version h (hβ Ω c r) (hE₀ Ω c r) hω hl2 halive a (Nat.find hex) (Nat.find_spec hex)
      (hsU (Nat.find hex) halive (by omega) (Nat.find_spec hex))
  · obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
      rcases l with _ | ⟨x, l'⟩
      · simp at hl2
      · exact ⟨x, l', rfl⟩
    exact shellFactLe_trivShell c.hκ c.hκ4 (hband x l' halive) (cw Ω c r) (rootPt r.1) c.s

/-- **D33's shell field on SDE's scaled cover.** -/
theorem rjShell_fact_scaled (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hI : InstInputsX h13 ver ch) (cw : CfWordFam.{u})
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
        (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
        (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)) (hl : l.length = 2 * k + 4) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      GW2Sdy.ShellFactLe c.κ (Cstar c.κ (cw Ω c r) (rootPt r.1) c.s) (rjShell h13 ver (cw Ω c r) c r l a ω) ∧
        (rjShell h13 ver (cw Ω c r) c r l a ω).start = GW2Bf.histStart c r l ω := by
  filter_upwards [rjShell_fact h12p h12p₀ h13₀ hI cw hβ hE₀ Ω c r k l hl a] with ω hω halive
  exact hω (GW2Sdz.alive_scaled_subset gap Ω c r l halive)

end InteractingSLE.Theorem14.GW2Rj
