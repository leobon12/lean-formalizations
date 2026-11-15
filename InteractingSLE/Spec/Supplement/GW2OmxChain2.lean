/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxSti
import InteractingSLE.Spec.Supplement.GW2OmxChain
import InteractingSLE.Spec.Supplement.GW2GmNest

/-!
# GW2's open lines: the kernel chain without the interior-tips premise

Packet PROVE-GW2-STAGEMEAN, R120 round. `GW2Omx.ae_of_kernel_curX` asks for the conclusion under the kernel at every
sample with GB6's datum, which is given only where the earlier switching tips are interior. Those tips are interior
almost surely (`GW2Omx.ae_switchTipsInterior`), so the chain needs the datum only on success:

* `schedDelta_pos_of_pairwise`, `pos_futureProgram`: the pieces of the actual schedule have positive durations;
* **`ae_switchTips_cur`**: the switching tips of the actual schedule are interior almost surely, on success;
* **`ae_of_kernel_curS`**: the kernel chain at every admissible root with the datum `HasLaunchPairEq` given on success.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Exist Exist.Staged Exist.StagedLaw GW2Schedule GW2Olm
  GW2Tip

/-- Strictly increasing positive times give positive durations. -/
theorem schedDelta_pos_of_pairwise {L : List (ℝ × ℝ≥0)} (hord : L.Pairwise (fun p q => p.2 < q.2))
    (h0 : ∀ p ∈ L, 0 < p.2) {j : ℕ} (hj : j < L.length) : 0 < schedDelta 0 L j := by
  unfold schedDelta
  rw [List.getD_eq_getElem _ _ hj]
  rcases j with _ | i
  · simp only [schedTime, tsub_zero]
    exact ENNReal.coe_pos.2 (h0 _ (List.getElem_mem hj))
  · simp only [schedTime]
    rw [List.getD_eq_getElem _ _ (Nat.lt_of_succ_lt hj)]
    have hlt := List.pairwise_iff_getElem.1 hord i (i + 1) (Nat.lt_of_succ_lt hj) hj (Nat.lt_succ_self i)
    exact ENNReal.coe_pos.2 (tsub_pos_of_lt hlt)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The times of the future program are positive. -/
theorem pos_futureProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ p ∈ futureProgram c r l a, 0 < p.2 := by
  intro p hp
  simp only [futureProgram, historyProgram, schedOf, entryList, List.mem_append, List.mem_cons,
    List.mem_reverse, List.mem_map, List.not_mem_nil, or_false] at hp
  rcases hp with (h | ⟨x, -, h⟩) | h
  · rw [h]
    exact c.hQpos _ r.1.2.2.2
  · rw [← h]
    exact c.hQpos _ x.2.2
  · rw [h]
    exact lt_of_lt_of_le (candidateCap_pos c r a) le_add_self

variable [StandardBorelSpace Ω]

/-- **The switching tips of the actual schedule are interior almost surely, on success.** -/
theorem ae_switchTips_cur (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) :
    ∀ᵐ ω ∂c.P, AllSucc (schedDelta 0 (futureProgram c r l a)) (fun j => futFam c r l a j ω) (curIdx c r l) →
      GW2Later.SwitchTipsInterior (futSpec c r l a) (fun j => futFam c r l a j ω) (curIdx c r l) := by
  set x := rootPt r.1 with hx
  set L := futureProgram c r l a with hL
  set spec := futSpec c r l a with hspec
  set E := futFam c r l a with hEdef
  set k := curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hordL := pairwise_lt_futureProgram c r l a hord
  refine ae_switchTipsInterior h13 c.hκ c.hκ4 (spec := spec) rfl (isFlowProg_scheduleProgram 0 L)
    (schedDelta_ne_top 0 L) (fun j hj => ?_) (fun j hj => ?_) hS hR hreg (k := k) (by omega)
  · have hjL : j < L.length := by omega
    exact schedDelta_pos_of_pairwise hordL (pos_futureProgram c r l a) hjL
  · have hjL : j < L.length := by omega
    exact GW2Later.schedAngle_mem_Icc (mem_Icc_futureProgram c r l a) hjL

/-- **The kernel chain at every admissible root, with GB6's datum on success.** -/
theorem ae_of_kernel_curS (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) {A : Set Ω} (hA : MeasurableSet A)
    (htop : ∀ᵐ ω₀ ∂c.P, (AllSucc (schedDelta 0 (futureProgram c r l a)) (fun j => futFam c r l a j ω₀)
        (curIdx c r l) → HasLaunchPairEq c.κ c.b c.jumps c.P c.h c.W (futSpec c r l a) (futFam c r l a)
          (curIdx c r l) ω₀) →
      ∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ω ∈ A) :
    ∀ᵐ ω ∂c.P, ω ∈ A := by
  refine ae_of_kernel_curX h12 h13 h12₀ h13₀ c r l a hx hord hA ?_
  filter_upwards [htop, ae_switchTips_cur h13 c r l a hord] with ω₀ h1 h2 hint
  exact h1 fun hs => hint hs (h2 hs)

end InteractingSLE.Theorem14.GW2Omx
