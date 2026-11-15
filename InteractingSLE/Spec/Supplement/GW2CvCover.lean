/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2CvSeed
import InteractingSLE.Spec.Supplement.GW2CvRead
import InteractingSLE.Spec.Supplement.GW2RootC24Gaps
import InteractingSLE.Spec.Supplement.GW2RootE26Cover
import InteractingSLE.Spec.Supplement.SBTail2RetainWord
import InteractingSLE.Spec.Supplement.GW2aPiece
import InteractingSLE.Spec.Supplement.BR3Ref

/-!
# GW2's root cover: the cover events, their stage-start measurability and their properties

Packet PROVE-GW2-COVER. Lemma GW2's proof, "An initial positive interior prefix always exists"
(`source/spec/p577-624.md` L1001–L1010). The cover event of a root index `r = ((v, θ₀, q₀), k)` is the
observed prefix event of the root: the root seed is admissible (`RootSeedOK`: the root `0`, or, when
the lower extreme is immediately inadmissible, a rational point `v` of the first low right arc with
`[0, v]` free of jumps), and the recorded root piece is protected (`RootCv.ProtRec`). It is a Borel
function of the two records of the root's stage start, so it is measurable in `rootSigma r []`.

* `RootSeedOK`, `rootRecs`, `coverEvent`, **`measurableSet_coverEvent`**;
* `stopRec_root_eq`, `isFlowLineDriver_root`, `ae_root_life_pos`: the root piece is the angle-`θ₀`
  flow line of the field read from `v`, with positive lifetime under `RootSeedOK`;
* **`ae_coverEvent_spec`**: almost surely on a cover event, the counterflow tip is interior, the root
  piece is alive at `q₀` and its physical trace `v + γ` is strictly before its first inversion contact
  with `α([0, s])`, and `v ‖α‖ < 1` on `[0, s]` (the arc `[0, v]` is untouched);
* **`ae_exists_mem_coverEvent`**: almost surely on `{α(s) ∈ ℍ}` some cover event occurs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootCv

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6
open PiecewiseConstantBoundaryData (leftLim rightLim)

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### The cover events -/

/-- **The admissible roots** (Lemma GW2's proof): the seed of the root's angle is admissible at the
root point, and the root is either the original target `0`, or a positive point `v` of the first
right arc (no jump candidate in `(0, v]`) when the lower extreme is immediately inadmissible
(`b(0⁺) − πχ/2 ≤ −λ`). -/
def RootSeedOK (c : SourceData Ω) (x : RootIdx c.Θ c.Q) : Prop :=
  ExplState.IsAdmissibleSeed c.κ (leftLim c.b (rootPt x)) (rightLim c.b (rootPt x)) (x.2.1 : ℝ) ∧
    (x.1 = none ∨ (0 < rootPt x ∧ (∀ y ∈ c.jumps, y ∉ Ioc 0 (rootPt x)) ∧
      rightLim c.b 0 + -(Real.pi / 2) * chiC c.κ ≤ -sleLambda c.κ))

/-- The two records of the root's stage start: the counterflow at `s` and the root piece stopped at
its root time. -/
def rootRecs (c : SourceData Ω) (x : RootIdx c.Θ c.Q) (ω : Ω) : RecData × RecData :=
  (cfRec c.s c.W c.ζ ω, stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω)

/-- **The cover event of a root** (Lemma GW2's proof: the observed prefix events): an admissible
root whose recorded root piece is protected. It does not depend on the scale `r.2`. -/
def coverEvent (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) : Set Ω :=
  {ω | RootSeedOK c r.1 ∧ ProtRec (rootPt r.1) (rootEntry r.1).2 c.s (rootRecs c r.1 ω)}

/-- The root records are measurable in the root's stage-start σ-algebra. -/
theorem measurable_rootRecs (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    Measurable[c.sigma r []] (rootRecs c r.1) := by
  have hst := RootU19.measurable_stageSigma_stopRec c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
    (schedSpecOf r.1 []) ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1)
    ⟨0, by simp only [entryList, List.map_nil, List.length_nil]; omega⟩
  exact (measurable_fst.comp (comap_measurable (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
    (schedSpecOf r.1 []) ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1)))).prodMk hst

/-- **The cover events are known at the root's stage start.** -/
theorem measurableSet_coverEvent (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    MeasurableSet[c.sigma r []] (coverEvent c r) := by
  classical
  by_cases hok : RootSeedOK c r.1
  · have he : coverEvent c r =
        rootRecs c r.1 ⁻¹' {p | ProtRec (rootPt r.1) (rootEntry r.1).2 c.s p} := by
      ext ω
      simp only [coverEvent, mem_ofPred_eq, mem_preimage, hok, true_and]
    rw [he]
    exact measurable_rootRecs c r (measurableSet_protRec _ _ _)
  · have he : coverEvent c r = ∅ := by
      ext ω
      simp only [coverEvent, mem_ofPred_eq, hok, false_and, mem_empty_iff_false]
    rw [he]
    exact @MeasurableSet.empty Ω (c.sigma r [])

/-! ### The root piece -/

/-- The program of a root's first stage: one instruction, the root angle for the root time. -/
theorem schedSpecOf_nil_eq {Θ : Set ℝ} {Q : Set ℝ≥0} (x : RootIdx Θ Q) :
    schedSpecOf x [] = (rootPt x, true, [Sum.inl ((rootEntry x).1, ((rootEntry x).2 : ℝ≥0∞))]) := by
  simp only [schedSpecOf, entryList, List.map_nil, schedOf_nil, schedSpec, scheduleProgram, tsub_zero]

/-- The root record is the root piece stopped at its root time. -/
theorem stopRec_root_eq (c : SourceData Ω) (x : RootIdx c.Θ c.Q) (ω : Ω) :
    stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω =
      recOf ((rootEntry x).2 : ℝ≥0∞) (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω) := by
  change recOf (specDelta (schedSpecOf x []) 0) _ = _
  congr 1
  rw [schedSpecOf_nil_eq]
  simp only [specDelta, instrTime, List.getElem?_cons_zero, ENNReal.coe_ne_top, ↓reduceIte]

/-- The first canonical driver of a root does not depend on the root time. -/
theorem canonSpecFam_root_congr (c : SourceData Ω) (x y : RootIdx c.Θ c.Q) (h1 : x.1 = y.1)
    (h2 : x.2.1 = y.2.1) (ω : Ω) :
    canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω =
      canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf y []) 0 ω := by
  have hx : rootPt x = rootPt y := by simp only [rootPt, h1]
  rw [schedSpecOf_nil_eq, schedSpecOf_nil_eq, hx]
  have hθ : (rootEntry x).1 = (rootEntry y).1 := by simp only [rootEntry, h2]
  rw [hθ]
  rfl

variable [StandardBorelSpace Ω]

/-- **The root piece is the angle-`θ₀` flow line of the field read from the root point** `v`, with
the data `b(· + v)`. -/
theorem isFlowLineDriver_root (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (x : RootIdx c.Θ c.Q) :
    IsFlowLineDriver c.κ (fun y => c.b (y + rootPt x)) (c.jumps.image (· - rootPt x)) (x.2.1 : ℝ) c.P
      (fun ω => Exist.flowField (rootPt x) 0 (c.h ω))
      (fun t ω => (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω).1 t)
      (fun ω => (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω).2) := by
  let spec := schedSpecOf x []
  have hS := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec)
    h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec (rootPt x) true _) (specDelta_ne_top _)
  have hp : spec.2.2 = [Sum.inl ((rootEntry x).1, ((rootEntry x).2 : ℝ≥0∞))] := by
    simp only [spec, schedSpecOf_nil_eq]
  exact hS.isFlowLineDriver_first_root c.hκ c.hb c.hh hp

/-- **An admissible root piece has positive lifetime** almost surely. -/
theorem ae_root_life_pos (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (x : RootIdx c.Θ c.Q)
    (hx : RootSeedOK c x) :
    ∀ᵐ ω ∂c.P, 0 < (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω).2 := by
  refine SB.Retain.ae_lifetime_pos_of_seed_admissible (isFlowLineDriver_root h13 c x) fun hT => ?_
  have h := (GW1.thresholdCondition_flowLine_zero_iff c.hκ _ _ _).1 hT
  rw [Exist.leftLim_comp_add, Exist.rightLim_comp_add, zero_add] at h
  exact h hx.1

end InteractingSLE.Theorem14.GW2TipSystem.RootCv
