/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Data
import InteractingSLE.Spec.Supplement.GW2RootH29Causal
import InteractingSLE.Spec.Supplement.GW2TmZero
import InteractingSLE.Spec.Supplement.GW2TpRoot
import InteractingSLE.Spec.Supplement.GW2SdzPair

/-!
# Decision D42: the records of an alive history's sub-histories avoid `launchBadRec`

PROVE-GW2-ROOTX round 9. The top's base family `Wire.T14Cur.baseWm` has the record event
`E₀ = (launchBadRec c r l a)ᶜ` (D26 (A′)). At an alive history every earlier entry `x` was added by a passed test of
the sub-history `l'` before it, with some candidate `a` of angle `x.1`:

* **`candLife_pos_of_test`**: a passed test gives the candidate a positive lifetime (`RootJ32.next_piece_live_of_test`,
  read at the candidate's own cap by `RootH29.canonical_next_independent_time`);
* **`ae_augRec_notMem_launchBadRec_of_test`**: so, almost surely, at every passed test every stage record of the
  sub-history (any second component, e.g. every instance's `srecX`) lies in `E₀` (RELDET's
  `GW2Rd.ae_mem_launchBadRec_iff`, on the success of the sub-history: `RootJ32.oldSuccess_of_test`);
* **`ae_alive_drop_notMem_launchBadRec`** (and `_scaled` on SDE's scaled cover): almost surely, at every alive history
  `l` and every split `l.drop k = x :: l'`, some candidate of angle `x.1` passed its test at `(l', x.2)` and every stage
  record of `l'` for it lies in `E₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Tip GW2Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **A passed test gives the candidate a positive lifetime.** -/
theorem candLife_pos_of_test (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (q : c.Q) (ω : Ω) (ht : ω ∈ (RootJ32.experiment c r).data.tests l a q) : 0 < GW2Rd.candLife c r l a ω := by
  have h := RootJ32.next_piece_live_of_test c r l a q ω ht
  have e := RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h (rootPt r.1)
    ((RootJ31.candidateAngle c r a : ℝ)) (RootJ31.historyProgram c r l) (q : ℝ≥0)
    (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) ω
  have hc : GW2Rd.candLife c r l a ω = (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
      (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ),
        RootJ31.historyTime c r l + RootJ31.candidateCap c r a)])) (RootJ31.historyProgram c r l).length ω).2 :=
    rfl
  rw [hc, ← e]
  exact lt_of_le_of_lt zero_le h

/-- **D42 at a passed test**: almost surely, at every passed test of `(l, a)` every stage record of `l` (any second
component) lies outside `launchBadRec c r l a`. -/
theorem ae_augRec_notMem_launchBadRec_of_test (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ∀ q : c.Q, ω ∈ (RootJ32.experiment c r).data.tests l a q → ∀ y : Ω → RecData,
      GW2Rd.augRec (GW2Rd.stageEncRec c r l) y ω ∉ GW2Rd.launchBadRec c r l a := by
  filter_upwards [GW2Rd.ae_mem_launchBadRec_iff c r l a h13] with ω hω q ht y hmem
  have hold := RootJ32.oldSuccess_of_test c r l a q ω ht
  exact (candLife_pos_of_test c r l a q ω ht).ne' (((hω hold) y).1 hmem)

/-- **D42 for the root-`x` stage record of any instance** at a passed test. -/
theorem ae_srecX_notMem_launchBadRec_of_test (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (I : GW2Sde.StageInst Ω) (x₀ : ℝ) :
    ∀ᵐ ω ∂c.P, ∀ q : c.Q, ω ∈ (RootJ32.experiment c r).data.tests l a q →
      I.srecX c r l x₀ ω ∉ GW2Rd.launchBadRec c r l a := by
  filter_upwards [ae_augRec_notMem_launchBadRec_of_test h13 c r l a] with ω hω q ht
  exact hω q ht _

/-- J32-alive histories stay alive when their latest entries are dropped. -/
theorem mem_alive_drop (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {ω : Ω} :
    ∀ (k : ℕ) (l : List (EntryIdx c.Θ c.Q)),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) (l.drop k)
  | 0, _, h => h
  | _ + 1, [], h => h
  | k + 1, _ :: l, h => mem_alive_drop c r k l h.1

/-- **The latest entry of an alive history was added by a passed test** of the history before it. -/
theorem exists_test_of_alive_cons (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {x : EntryIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} {ω : Ω}
    (h : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) (x :: l)) :
    ∃ a : ℕ, RootJ31.candidateAngle c r a = x.1 ∧ ω ∈ (RootJ32.experiment c r).data.tests l a x.2 := by
  obtain ⟨-, ht⟩ := h
  obtain ⟨a, ht⟩ := mem_iUnion.1 ht
  obtain ⟨hang, ht⟩ := mem_iUnion.1 ht
  exact ⟨a, hang, ht⟩

/-- **D42 at alive histories**: almost surely, at every alive history `l` and every split `l.drop k = x :: l'`, a
candidate of angle `x.1` passed its test at `(l', x.2)`, and every stage record of `l'` (any second component) lies
outside `launchBadRec c r l' a`. -/
theorem ae_alive_drop_notMem_launchBadRec (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ l : List (EntryIdx c.Θ c.Q),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ∀ (k : ℕ) (x : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)), l.drop k = x :: l' →
        ∃ a : ℕ, RootJ31.candidateAngle c r a = x.1 ∧ ω ∈ (RootJ32.experiment c r).data.tests l' a x.2 ∧
          ∀ y : Ω → RecData, GW2Rd.augRec (GW2Rd.stageEncRec c r l') y ω ∉ GW2Rd.launchBadRec c r l' a := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hall : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q),
      ω ∈ (RootJ32.experiment c r).data.tests l' a q → ∀ y : Ω → RecData,
        GW2Rd.augRec (GW2Rd.stageEncRec c r l') y ω ∉ GW2Rd.launchBadRec c r l' a := by
    refine ae_all_iff.2 fun l' => ae_all_iff.2 fun a => ?_
    exact ae_augRec_notMem_launchBadRec_of_test h13 c r l' a
  filter_upwards [hall] with ω hω l hl k x l' hk
  have hl' := mem_alive_drop c r k l hl
  rw [hk] at hl'
  obtain ⟨a, hang, ht⟩ := exists_test_of_alive_cons c r hl'
  exact ⟨a, hang, ht, hω l' a x.2 ht⟩

/-- **D42 at alive histories on SDE's scaled cover** (`GW2Sdz.J32S gap`). -/
theorem ae_alive_drop_notMem_launchBadRec_scaled (h13 : Exist.Theorem13Statement.{u})
    (gap : RootCv.GapFamily.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ l : List (EntryIdx c.Θ c.Q),
      ω ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      ∀ (k : ℕ) (x : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)), l.drop k = x :: l' →
        ∃ a : ℕ, RootJ31.candidateAngle c r a = x.1 ∧ ω ∈ (RootJ32.experiment c r).data.tests l' a x.2 ∧
          ∀ y : Ω → RecData, GW2Rd.augRec (GW2Rd.stageEncRec c r l') y ω ∉ GW2Rd.launchBadRec c r l' a := by
  filter_upwards [ae_alive_drop_notMem_launchBadRec h13 c r] with ω hω l hl
  exact hω l (GW2Sdz.alive_scaled_subset gap Ω c r l hl)

end InteractingSLE.Theorem14.GW2Rj
