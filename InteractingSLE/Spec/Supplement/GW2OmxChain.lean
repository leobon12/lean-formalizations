/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmChain
import InteractingSLE.Spec.Supplement.GW2RootI30Initial

/-!
# GW2's open lines at a root of the first low right arc: the kernel chain

Packet PROVE-GW2-STAGEMEAN, R120 round (decision D8: the stage instance takes the root point as a parameter). The
kernel route conditions on the earlier pieces; it sees the root only at the first launch. SCHED's launch-pair chain
already starts there: `GW2TipSystem.hasLaunchPairEq_zero` covers `x = 0` (Theorem 1.3) and every `x ∈ lowerArcRoots`
(BR4a, `ae_hasLaunchPairEq_zero_root_arc`), so no retargeting base case is needed.

* **`rootPt_cases_of_seedOK`**: an admissible root (`RootCv.RootSeedOK`) is `0` or a root of the first low right arc;
* **`coverEvent_eq_empty_of_not_seedOK`**: the cover event of a root that is not admissible is empty (so J32's alive
  event there is empty, and nothing is asked of the kernel route at such roots);
* **`ae_of_kernel_curX`**: `GW2Olm.ae_of_kernel_cur` at every root `0` or of the first low right arc.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Exist Exist.Staged Exist.StagedLaw GW2Schedule GW2Olm

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **An admissible root is `0` or a root of the first low right arc.** -/
theorem rootPt_cases_of_seedOK (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hseed : RootCv.RootSeedOK c r.1) :
    rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps :=
  (RootI30.schedAdm_nil_of_seedOK c r hseed).1

/-- **The cover event of a root that is not admissible is empty.** -/
theorem coverEvent_eq_empty_of_not_seedOK (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hseed : ¬ RootCv.RootSeedOK c r.1) : RootCv.coverEvent c r = ∅ :=
  eq_empty_of_forall_notMem fun _ hω => hseed hω.1

/-- **The kernel chain at the current piece, at every root `0` or of the first low right arc** (strictly time-ordered
histories): a measurable event that is almost sure under the conditional kernel of the earlier pieces whenever the
launch datum holds is `P`-almost sure. -/
theorem ae_of_kernel_curX [StandardBorelSpace Ω] (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
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
    hx (mem_Icc_futureProgram c r l a) (pairwise_lt_futureProgram c r l a hord) hA (curIdx c r l) ?_
  rw [hfs]
  exact htop

/-- **At an admissible root, the kernel chain at the current piece.** -/
theorem ae_of_kernel_cur_seedOK [StandardBorelSpace Ω] (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hseed : RootCv.RootSeedOK c r.1)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) {A : Set Ω} (hA : MeasurableSet A)
    (htop : ∀ᵐ ω₀ ∂c.P, HasLaunchPairEqInt c.κ c.b c.jumps c.P c.h c.W (futSpec c r l a)
        (schedDelta 0 (futureProgram c r l a)) (futFam c r l a) (curIdx c r l) ω₀ →
      ∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ω ∈ A) :
    ∀ᵐ ω ∂c.P, ω ∈ A :=
  ae_of_kernel_curX h12 h13 h12₀ h13₀ c r l a (rootPt_cases_of_seedOK c r hseed) hord hA htop

end InteractingSLE.Theorem14.GW2Omx
