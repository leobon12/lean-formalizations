/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkSched
import InteractingSLE.Spec.Supplement.GW2OmxContact

/-!
# The root-`x` kernel port (D38): the retained prefix of the current launch at a root `x`

Packet PROVE-GW2-GEOM2, round 11 (STAGEMEAN's `GW2Omx.ae_contactSet_eq_trace` at a root `x`):

* **`ae_contactSet_eq_traceX`**: for a time-ordered history, almost surely on the history's success, the launch
  datum's retained prefix (`contactSet`) is the explored trace on `[0, T]` translated to the root `x` (STAGEMEAN's
  proof without the final identification `x = 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Xk

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Schedule GW2Tip Exist Exist.Staged Exist.StagedLaw
  GW2Rd

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The retained prefix of the current launch is the translated explored trace on `[0, T]`** (any root, almost surely
on the history's success). -/
theorem ae_contactSet_eq_traceX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hord : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω →
      contactSet c.κ c.b c.jumps (GW2Olm.futSpec c r l a) (fun j => GW2Olm.futFam c r l a j ω)
        (GW2Olm.curIdx c r l) =
        (fun z : ℂ => ((rootPt r.1 : ℝ) : ℂ) + z) '' (schedTr c r l a ω '' Icc 0 (historyTime c r l)) := by
  filter_upwards [Gm.ae_futureJoined_trace h13 c r, ae_schedW_trace c r l a h13] with ω hfut htr hωE
  set x := rootPt r.1 with hx
  set Lh := historyProgram c r l with hLh
  set y : ℝ × ℝ≥0 := ((candidateAngle c r a : ℝ), historyTime c r l + candidateCap c r a) with hy
  have hrun := RootC11.run_schedSpec_append c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x y ω
    (l := Lh) (n := Lh.length) le_rfl
  have hlen : (schedSpec x Lh).2.2.length = Lh.length := length_scheduleProgram 0 Lh
  have hγ : IsGeneratingTrace (Gm.futureJoined c r l a ω) ⊤ (schedTr c r l a ω) := by
    rw [← schedW_of_oldSuccess c r l a hωE]
    exact htr.1
  have hP := Gm.prefixSet_history_eq c r l a ω hord hωE (hfut l a hωE).1 hγ
  -- the arcs of the history's run are empty
  have hsh : AllSucc (specDelta (schedSpec x Lh))
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω) Lh.length :=
    (oldSuccess_iff_allSucc c r l ω).mp hωE
  obtain ⟨-, harcs⟩ := Swc.run_pieces_arcs (κ := c.κ) (b := c.b) (jumps := c.jumps)
    (D := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω) rfl
    (isFlowProg_spec x true Lh) (specDelta_ne_top _) Lh.length (by rw [hlen]) hsh
  have hphys : prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x Lh ω =
      contactSet c.κ c.b c.jumps (GW2Olm.futSpec c r l a) (fun j => GW2Olm.futFam c r l a j ω)
        (GW2Olm.curIdx c r l) := by
    change ExplState.physSet c.κ c.b c.jumps (schedSpec x Lh)
      (fun k => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) k ω) = _
    unfold ExplState.physSet contactSet
    simp only []
    rw [hlen, harcs, ← hrun]
    simp only [List.not_mem_nil, iUnion_of_empty, iUnion_empty, union_empty]
    rfl
  rw [← hphys, hP]

end InteractingSLE.Theorem14.GW2Xk
