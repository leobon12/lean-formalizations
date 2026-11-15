/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmDil
import InteractingSLE.Spec.Supplement.GW2StmStep
import InteractingSLE.Spec.Supplement.BR4aInWord
import InteractingSLE.Spec.Supplement.GW2SdePrefix
import InteractingSLE.Spec.Supplement.GW2SchedRuleGB6
import InteractingSLE.Spec.Exist.StagedLaw3Main
import InteractingSLE.Spec.Exist.StagedLaw2Main
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# GW2's open lines: the kernel chain of the earlier pieces at the actual schedule

Packet PROVE-GW2-STAGEMEAN, R119 round. The launch datum `HasLaunchPairEq` of the current piece is available only in
kernel-chain form (SCHED's `GW2TipSystem.ae_of_gb6StagedEqStep`). This file instantiates the chain at the actual
schedule `futSpec c r l a` (the history program followed by the candidate piece), for strictly time-ordered histories
(R119/D1: alive histories are strictly time-ordered, `Gm.pairwise_lt_historyProgram_of_alive`):

* `chainFam`: a staged family over all histories, canonical (`GW2Tip.canonSpecFam`) on GW2 flow programs and a
  constructed regular staged history (`Exist.regularStagedHistoryConstructionStatement_of_inputs`) elsewhere;
  `isStagedHistory_chainFam`, `stagedPiecesRegular_chainFam`, `chainFam_futSpec` (it is `futFam` at the schedule);
* the schedule facts: angles in `[−π/2, π/2]` (`mem_Icc_futureProgram`) and strictly increasing times
  (`pairwise_lt_futureProgram`, from the history's order and the positive candidate cap);
* **`ae_of_kernel_cur`**: a measurable event that is almost sure under the conditional kernel of the earlier pieces
  whenever the launch datum holds there is `P`-almost sure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Olm

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Exist Exist.Staged Exist.StagedLaw GW2Schedule

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-! ### The schedule -/

theorem le_last_of_pairwise {L : List (ℝ × ℝ≥0)} (hL : L.Pairwise (fun p q => p.2 < q.2)) (hne : L ≠ [])
    {p : ℝ × ℝ≥0} (hp : p ∈ L) : p.2 ≤ (L.getLast hne).2 := by
  have e := List.dropLast_append_getLast hne
  rw [← e] at hL hp
  rcases List.mem_append.1 hp with h | h
  · exact (List.pairwise_append.1 hL).2.2 p h _ (List.mem_singleton_self _) |>.le
  · rw [List.mem_singleton.1 h]

/-- The times of the future program increase strictly when those of the history do. -/
theorem pairwise_lt_futureProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) :
    (futureProgram c r l a).Pairwise (fun p q => p.2 < q.2) := by
  have hne : historyProgram c r l ≠ [] := by
    simp only [historyProgram, schedOf, ne_eq, reduceCtorEq, not_false_eq_true]
  have hT : historyTime c r l = ((historyProgram c r l).getLast hne).2 := by
    rw [GW2Sde.historyTime_eq_lastTime, Sec5.Prop513Schedule.lastTime_eq_getLast 0 _ hne]
  rw [futureProgram, List.pairwise_append]
  refine ⟨hord, List.pairwise_singleton _ _, fun p hp q hq => ?_⟩
  rw [List.mem_singleton.1 hq]
  have h1 := le_last_of_pairwise hord hne hp
  rw [← hT] at h1
  exact lt_of_le_of_lt h1 (lt_add_of_pos_right _ (candidateCap_pos c r a))

/-- The angles of the future program lie in `[−π/2, π/2]`. -/
theorem mem_Icc_futureProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) : ∀ p ∈ futureProgram c r l a, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hΘ : ∀ θ : c.Θ, (θ : ℝ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := fun θ =>
    Ioo_subset_Icc_self (c.hΘ θ.2)
  intro p hp
  simp only [futureProgram, historyProgram, schedOf, entryList, List.mem_append, List.mem_cons,
    List.mem_reverse, List.mem_map, List.not_mem_nil, or_false] at hp
  rcases hp with (h | ⟨x, -, h⟩) | h
  · rw [h]
    exact hΘ _
  · rw [← h]
    exact hΘ _
  · rw [h]
    exact hΘ _

/-! ### A staged family over all histories, canonical on GW2 flow programs -/

/-- GW2 flow histories: GW2-type, every instruction a flow instruction read by `specAngle`/`specDelta`. -/
def IsGWFlowSpec (spec : ExplSpec) : Prop :=
  spec.2.1 = true ∧ IsFlowProg spec.2.2 (GW2Tip.specAngle spec) (GW2Tip.specDelta spec)

open Classical in
/-- **The staged family of the kernel chain**: the canonical pieces on GW2 flow histories, a constructed regular staged
history on the other boundary-continued programs. -/
def chainFam [StandardBorelSpace Ω] (c : SourceData Ω) (hC : RegularStagedHistoryConstructionStatement.{u}) :
    ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun spec =>
  if IsGWFlowSpec spec then GW2Tip.canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec
  else if hs : IsBoundaryContinuedProgram spec.2.2 then
    (hC c.κ c.hκ c.hκ4 c.b c.jumps c.hb c.P c.h c.hh spec hs).choose
  else GW2Tip.canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec

theorem isStagedHistory_chainFam [StandardBorelSpace Ω] (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (hC : RegularStagedHistoryConstructionStatement.{u}) (spec : ExplSpec) (hs : IsBoundaryContinuedProgram spec.2.2) :
    IsStagedHistory c.κ c.b c.jumps c.P c.h spec (chainFam c hC spec) ∧
      ∀ k ω, IsRegularDriver (chainFam c hC spec k ω) := by
  classical
  unfold chainFam
  by_cases hf : IsGWFlowSpec spec
  · simp only [hf, ↓reduceIte]
    exact ⟨isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀ (GW2Tip.specAngle spec) (GW2Tip.specDelta spec) h13
      c.hβA c.hb c.hc₀J c.hc₀ c.hh hf.1 hf.2 (GW2Tip.specDelta_ne_top spec),
      fun k ω => isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ spec.1 c.h k ω⟩
  · simp only [hf, ↓reduceIte, hs, ↓reduceDIte]
    exact (hC c.κ c.hκ c.hκ4 c.b c.jumps c.hb c.P c.h c.hh spec hs).choose_spec

theorem chainFam_futSpec [StandardBorelSpace Ω] (c : SourceData Ω) (hC : RegularStagedHistoryConstructionStatement.{u})
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    chainFam c hC (futSpec c r l a) = futFam c r l a := by
  classical
  unfold chainFam
  have hf : IsGWFlowSpec (futSpec c r l a) := ⟨rfl, GW2Tip.isFlowProg_spec _ _ _⟩
  simp only [hf, ↓reduceIte]
  rfl

/-- The construction of regular staged histories (Theorem 1.2's parameter form, Theorem 1.3, the stop law). -/
theorem regularConstruction (h13 : Theorem13Statement.{u}) (h12p : Theorem12ParamStatement.{u}) :
    RegularStagedHistoryConstructionStatement.{u} :=
  regularStagedHistoryConstructionStatement_of_inputs h12p h13 (stagedCondLawStatement_of_stopLaw stopLawStatement)

/-! ### The kernel chain at the current piece -/

/-- **A measurable event that is almost sure under the conditional kernel of the earlier pieces whenever the launch
datum holds there is `P`-almost sure** (strictly time-ordered histories, root `0`). -/
theorem ae_of_kernel_cur [StandardBorelSpace Ω] (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) {A : Set Ω} (hA : MeasurableSet A)
    (htop : ∀ᵐ ω₀ ∂c.P, HasLaunchPairEqInt c.κ c.b c.jumps c.P c.h c.W (futSpec c r l a)
        (schedDelta 0 (futureProgram c r l a)) (futFam c r l a) (curIdx c r l) ω₀ →
      ∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ω ∈ A) :
    ∀ᵐ ω ∂c.P, ω ∈ A := by
  have hC := regularConstruction h13 c.h12p
  have hE := fun spec hs => (isStagedHistory_chainFam h13 c hC spec hs).1
  have hER := fun spec hs => stagedPiecesRegular_of_regular h13 c.hκ c.hb
    (isStagedHistory_chainFam h13 c hC spec hs).1 (isStagedHistory_chainFam h13 c hC spec hs).2
  have hfs : chainFam c hC ⟨rootPt r.1, true, scheduleProgram 0 (futureProgram c r l a)⟩ = futFam c r l a :=
    chainFam_futSpec c hC r l a
  refine ae_of_gb6StagedEqStep (GW2Stm.gb6StagedEqStepStatement_of_thm12_thm13 h12 h13 h12₀ h13₀)
    (BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀) h13 h13₀ c.hκ c.hκ4 c.hb c.hh c.hcf c.hζ hE hER
    (Or.inl hr0) (mem_Icc_futureProgram c r l a) (pairwise_lt_futureProgram c r l a hord) hA (curIdx c r l) ?_
  rw [hfs]
  exact htop

end InteractingSLE.Theorem14.GW2Olm
