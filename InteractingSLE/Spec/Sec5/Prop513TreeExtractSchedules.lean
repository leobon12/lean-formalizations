/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TreeExtractVersion
import InteractingSLE.Frozen.Spec.scheduleProgram

/-!
# Enumerating finite extreme-angle schedules and their descendants

Switching and terminal times are positive rationals in increasing order. The
enumeration is deterministic and covers every such nonempty finite schedule.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Real NNReal

namespace InteractingSLE.Sec5.Prop513TreeExtract

/-- A nonempty finite extreme-angle schedule with positive ordered rational times. -/
def Schedule := {l : List (Bool × ℚ) // l ≠ [] ∧
  (∀ p ∈ l, 0 < p.2) ∧ l.Pairwise (fun p r => p.2 < r.2)}

instance : Countable Schedule := inferInstanceAs (Countable (Subtype _))

def basicSchedule : Schedule := ⟨[(false, 1)], by simp⟩

def enumType (α : Type*) [Countable α] (a : α) (n : ℕ) : α :=
  @Option.getD α (@Encodable.decode α (Encodable.ofCountable α) n) a

theorem enumType_surjective (α : Type*) [Countable α] (a : α) :
    Function.Surjective (enumType α a) :=
  @Encodable.surjective_decode_getD α (Encodable.ofCountable α) a

def scheduleAt : ℕ → Schedule := enumType Schedule basicSchedule

theorem scheduleAt_surjective : Function.Surjective scheduleAt :=
  enumType_surjective Schedule basicSchedule

def scheduleIndex (s : Schedule) : ℕ := by
  classical
  exact Nat.find (scheduleAt_surjective s)

theorem scheduleAt_index (s : Schedule) : scheduleAt (scheduleIndex s) = s := by
  classical
  exact Nat.find_spec (scheduleAt_surjective s)

def terminalRat (s : Schedule) : ℚ := (s.1.getLast s.2.1).2

theorem terminalRat_pos (s : Schedule) : 0 < terminalRat s :=
  s.2.2.1 _ (List.getLast_mem _)

def terminal (s : Schedule) : ℝ≥0 := (terminalRat s : ℝ).toNNReal

theorem terminal_pos (s : Schedule) : 0 < terminal s :=
  Real.toNNReal_pos.2 (by exact_mod_cast terminalRat_pos s)

/-- The real-angle, nonnegative-time list used by the staged carrier. -/
def scheduleList (s : Schedule) : List (ℝ × ℝ≥0) :=
  s.1.map fun p => (if p.1 then Real.pi / 2 else -(Real.pi / 2), (p.2 : ℝ).toNNReal)

/-- The enumerated syntax gives actual schedules at the two extreme angles. -/
theorem isSchedule_scheduleList (s : Schedule) :
    IsSchedule {-(Real.pi / 2), Real.pi / 2}
      {t | ∃ q : ℚ, 0 < q ∧ t = (q : ℝ).toNNReal} (scheduleList s) := by
  constructor
  · rintro p hp
    obtain ⟨⟨b, q⟩, hmem, rfl⟩ := List.mem_map.1 hp
    refine ⟨?_, q, s.2.2.1 _ hmem, rfl⟩
    cases b <;> simp
  · rw [scheduleList, List.pairwise_map]
    exact s.2.2.2.imp_of_mem fun {p r} hp hr hpr => by
      change (p.2 : ℝ).toNNReal < (r.2 : ℝ).toNNReal
      have hp0 : 0 ≤ (p.2 : ℝ) := by exact_mod_cast (s.2.2.1 _ hp).le
      have hr0 : 0 ≤ (r.2 : ℝ) := by exact_mod_cast (s.2.2.1 _ hr).le
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hp0, Real.coe_toNNReal _ hr0]
      exact_mod_cast hpr

def scheduleSpec (s : Schedule) : ExplSpec := ⟨0, true, scheduleProgram 0 (scheduleList s)⟩

/-- Descendants extend the whole finite prefix and have no earlier terminal time. -/
def Descendant (s : Schedule) := {r : Schedule // s.1.IsPrefix r.1 ∧ terminal s ≤ terminal r}

instance (s : Schedule) : Countable (Descendant s) :=
  inferInstanceAs (Countable (Subtype _))

def descendantAt (s : Schedule) : ℕ → Descendant s :=
  enumType (Descendant s) ⟨s, ⟨[], by simp⟩, le_rfl⟩

theorem descendantAt_surjective (s : Schedule) : Function.Surjective (descendantAt s) :=
  enumType_surjective (Descendant s) _

def descendantIndex (n m : ℕ) : ℕ := scheduleIndex (descendantAt (scheduleAt n) m).1

theorem terminal_descendant_le (n m : ℕ) :
    terminal (scheduleAt n) ≤ terminal (scheduleAt (descendantIndex n m)) := by
  rw [descendantIndex, scheduleAt_index]
  exact (descendantAt (scheduleAt n) m).2.2

theorem schedule_descendant_prefix (n m : ℕ) :
    (scheduleAt n).1.IsPrefix (scheduleAt (descendantIndex n m)).1 := by
  rw [descendantIndex, scheduleAt_index]
  exact (descendantAt (scheduleAt n) m).2.1

/-- Every descendant occurs in the deterministic child enumeration. -/
theorem descendantIndex_covers (n : ℕ) (s : Descendant (scheduleAt n)) :
    ∃ m, scheduleAt (descendantIndex n m) = s.1 := by
  obtain ⟨m, hm⟩ := descendantAt_surjective (scheduleAt n) s
  refine ⟨m, ?_⟩
  rw [descendantIndex, hm, scheduleAt_index]

end InteractingSLE.Sec5.Prop513TreeExtract
