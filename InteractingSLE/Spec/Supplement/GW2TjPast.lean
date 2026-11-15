/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmMarks
import InteractingSLE.Spec.Supplement.GW2TfAsm

/-!
# The σ-algebra of the earlier pieces lies in the retained σ-algebra of the history

Packet PROVE-GW2-RELDET, ruling R117(b), item (T2) (`GW2Olm.KernelMarksAgree`): the raw kernel marks must contain the
σ-algebra `GW2Olm.pastG` of the earlier pieces (the retained past of the first `curIdx` instructions of the future
program). Here it is shown to lie in `c.sigma r l`, the σ-algebra of the counterflow record and the history pieces'
stopped records, which the stage filtration contains.

* **`exists_measurable_pastMap_eq`**: for a GW2 schedule program, the retained past of the first `k` instructions is a
  measurable function of the `k` stopped records `recOf (instrTime spec i) (E i ω)`. The retained record of a piece
  is its stopped record if all earlier pieces succeeded, and the default record otherwise; success is read off the
  earlier retained flags (`allSucc_iff_flags`, `launches_run_gw2`).
* **`pastG_le_sigma`**: `pastG c r l a ≤ c.sigma r l`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31

/-- The retained past after one more instruction, as a function of the earlier retained past and the new record. -/
def pastStep {k : ℕ} (p : PastData k) (x : RecData) : PastData (k + 1) :=
  WalkLaw.pastSucc p (if ∀ i : Fin k, (p i).2.2 = false then x else readRec (fun _ => 0, 0, false))

theorem measurable_pastStep_uncurry (k : ℕ) :
    Measurable fun q : PastData k × RecData => pastStep q.1 q.2 := by
  classical
  have hS : MeasurableSet {q : PastData k × RecData | ∀ i : Fin k, (q.1 i).2.2 = false} := by
    have e : {q : PastData k × RecData | ∀ i : Fin k, (q.1 i).2.2 = false} =
        ⋂ i : Fin k, (fun q : PastData k × RecData => (q.1 i).2.2) ⁻¹' {false} := by
      ext q
      simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_singleton_iff]
    rw [e]
    exact MeasurableSet.iInter fun i =>
      ((measurable_snd.comp measurable_snd).comp ((measurable_pi_apply i).comp measurable_fst))
        (measurableSet_singleton false)
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : (i : ℕ) < k
  · have e : (fun q : PastData k × RecData => pastStep q.1 q.2 i) = fun q => q.1 ⟨i, hi⟩ := by
      funext q
      simp only [pastStep, WalkLaw.pastSucc, hi, ↓reduceDIte]
    rw [e]
    exact (measurable_pi_apply _).comp measurable_fst
  · have e : (fun q : PastData k × RecData => pastStep q.1 q.2 i) = fun q =>
        if q ∈ {q : PastData k × RecData | ∀ i : Fin k, (q.1 i).2.2 = false} then q.2
        else readRec (fun _ => 0, 0, false) := by
      funext q
      simp only [pastStep, WalkLaw.pastSucc, hi, ↓reduceDIte, mem_ofPred_eq]
    rw [e]
    exact Measurable.ite hS measurable_snd measurable_const

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The retained past of a GW2 schedule program is a measurable function of the stopped records.** -/
theorem exists_measurable_pastMap_eq {spec : ExplSpec} {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞} (hgw : spec.2.1 = true)
    (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ k ≤ spec.2.2.length, ∃ Φ : (Fin k → RecData) → PastData k, Measurable Φ ∧
      ∀ ω, pastMap κ b jumps spec E k ω = Φ fun i => recOf (instrTime spec i) (E i ω) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => fun i => i.elim0, measurable_const, fun ω => ?_⟩
    funext i
    exact i.elim0
  | succ k ih =>
    intro hk
    obtain ⟨Φ, hΦ, hpast⟩ := ih (Nat.le_of_succ_le hk)
    refine ⟨fun x => pastStep (Φ (Fin.init x)) (x (Fin.last k)),
      (measurable_pastStep_uncurry k).comp ((hΦ.comp (measurable_pi_iff.2 fun i =>
        measurable_pi_apply (Fin.castSucc i))).prodMk (measurable_pi_apply (Fin.last k))), fun ω => ?_⟩
    have hinit : (Fin.init fun i : Fin (k + 1) => recOf (instrTime spec i) (E i ω)) =
        fun i : Fin k => recOf (instrTime spec i) (E i ω) := rfl
    simp only [hinit]
    rw [WalkLaw.pastMap_succ_eq, ← hpast ω]
    have hl := launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun j => E j ω)
      (Nat.lt_of_succ_le hk)
    have hfl := allSucc_iff_flags (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ E (Nat.le_of_succ_le hk) ω
    unfold pastStep
    congr 1
    by_cases hs : AllSucc Δ (fun j => E j ω) k
    · have hc : ∀ i : Fin k, (pastMap κ b jumps spec E k ω i).2.2 = false := hfl.1 hs
      rw [hl.1 hs]
      simp only [hc, implies_true, ↓reduceIte, reduceCtorEq, Fin.val_last]
    · have hc : ¬ ∀ i : Fin k, (pastMap κ b jumps spec E k ω i).2.2 = false := fun h => hs (hfl.2 h)
      rw [hl.2 hs]
      simp only [hc, ↓reduceIte]

/-- **The earlier pieces' σ-algebra lies in the retained σ-algebra of the history.** -/
theorem pastG_le_sigma {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : GW2Olm.pastG c r l a ≤ c.sigma r l := by
  set x := rootPt r.1
  set L := futureProgram c r l a with hL
  set spec := schedSpec x L with hspec
  set m := (historyProgram c r l).length with hm
  have hlenL : L.length = m + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = m + 1 := (length_scheduleProgram 0 L).trans hlenL
  obtain ⟨Φ, hΦ, hpast⟩ := exists_measurable_pastMap_eq (κ := c.κ) (b := c.b) (jumps := c.jumps)
    (spec := spec) rfl (isFlowProg_spec x true L) (specDelta_ne_top _)
    (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec) m (by omega)
  -- the stopped records of the first `m` instructions are history records
  have hrec : ∀ (i : Fin m) (ω : Ω), recOf (instrTime spec i) (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec i ω) =
      stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) i ω := by
    intro i ω
    have hiL : (i : ℕ) < L.length := by omega
    have hT : instrTime spec i ≠ ⊤ := RootU19.instrTime_sched_ne_top x L hiL
    have hd : instrTime spec i = specDelta spec i := by simp only [specDelta, hT, ↓reduceIte]
    rw [hd]
    change stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x (historyProgram c r l ++ _)) i ω = _
    exact stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h x _ i.2 ω
  have hmn : m = (entryList l).length + 1 := by
    simp only [hm, historyProgram, schedOf, List.length_cons, List.length_reverse]
  -- the record map factors through the stage map
  have hR : Measurable[c.sigma r l] fun ω (i : Fin m) =>
      stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) i ω := by
    refine @measurable_pi_iff _ _ _ (c.sigma r l) _ _ |>.2 fun i => ?_
    have h1 : Measurable[c.sigma r l]
        (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ (schedSpecOf r.1 l) ((entryList l).length + 1)) :=
      comap_measurable _
    exact (measurable_pi_apply (⟨i, by omega⟩ : Fin ((entryList l).length + 1))).comp
      (measurable_snd.comp h1)
  change MeasurableSpace.comap (pastMap c.κ c.b c.jumps spec (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec) m)
    inferInstance ≤ c.sigma r l
  have e : pastMap c.κ c.b c.jumps spec (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec) m =
      Φ ∘ fun ω (i : Fin m) => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) i ω := by
    funext ω
    rw [hpast ω]
    simp only [Function.comp_apply, hrec]
  rw [e]
  exact (hΦ.comp hR).comap_le

end InteractingSLE.Theorem14.GW2Rd
