/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8NativeWord

/-!
# Positive-time reference collars on surviving incoming sides

PROVE-SIDE-COLLAR2. A single local driver represents the actual original
visit chart and the later current chart. A surviving initial real trajectory
then supplies the incident collar and exact word identity between them,
including arbitrary phases and the fixed common offset.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- The actual earlier original reference and current chart have a
surviving incident half-disc and equal native words at the corresponding
incoming accesses. No collar, transition, lift limit or word equation is
assumed. The old and current mean heights are not asserted here. -/
theorem reference_incoming_geometry_and_word {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) (e : Late.SideData Ω) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) (s q : ℝ≥0)
    (hOrder : (j.visitCapacity d ω s).toNNReal ≤ q)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q' : ℝ} (hqq' : (q : ℝ) < q')
    (hEq : EqOn (fun r : ℝ => segDriver ((j.target i d).curve ω) r.toNNReal) W (Icc 0 q'))
    {x : ℝ} {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol W x q a)
    (hx : x ∉ forceJumpSet ((j.target i d).marksL ω) ((j.target i d).marksR ω))
    (hOldJump : (a (j.visitCapacity d ω s).toNNReal).re ∉
      (j.target i d).jumps (j.visitCapacity d ω s).toNNReal ω)
    (hNowJump : (a q).re ∉ (j.target i d).jumps q ω) :
    let p := (j.visitCapacity d ω s).toNNReal
    let old := j.referenceVisitChart i d ω s
    let current := relChart (j.target i d).baseChart (j.target i d).curve q ω
    ∃ ε : ℝ, 0 < ε ∧
      old.2.1 '' (H ∩ ball ((a p).re : ℂ) ε) ⊆ (current.dom : Set ℂ) ∧
      Tendsto (fun z => old.1 (current.2.1 z))
        (𝓝[H] ((a q).re : ℂ)) (𝓝 ((a p).re : ℂ)) ∧
      Tendsto (fun z => current.2.2 (current.2.1 z) - old.2.2 (current.2.1 z))
        (𝓝[H] ((a q).re : ℂ)) (𝓝 0) ∧
      j.nativeSideWord i d e p ω (a p).re = j.nativeSideWord i d e q ω (a q).re := by
  intro p old current
  have hpq : (p : ℝ) ≤ q := by exact_mod_cast hOrder
  have hpq' := hpq.trans_lt hqq'
  have hOld : old = ((j.target i d).baseChart ω).loewner W p :=
    loewner_congr ((j.target i d).baseChart ω) p.coe_nonneg hpq' hEq
  have hNow : current = ((j.target i d).baseChart ω).loewner W q :=
    loewner_congr ((j.target i d).baseChart ω) q.coe_nonneg hqq' hEq
  obtain ⟨ε, hε, hCollar, hTransition, hLift⟩ := exists_own_collar_of_surviving_real
    (isDomainChart_baseChart hj hRc hLc hω).1 hW hW0 p.coe_nonneg hpq ha
  refine ⟨ε, hε, ?_, ?_, ?_, ?_⟩
  · rwa [hOld, hNow]
  · rwa [hOld, hNow]
  · rwa [hOld, hNow]
  · have hEqP : EqOn (fun r : ℝ => segDriver ((j.target i d).curve ω) r.toNNReal) W
        (Icc 0 (p : ℝ)) := fun r hr => hEq ⟨hr.1, hr.2.trans hpq'.le⟩
    have hEqQ : EqOn (fun r : ℝ => segDriver ((j.target i d).curve ω) r.toNNReal) W
        (Icc 0 (q : ℝ)) := fun r hr => hEq ⟨hr.1, hr.2.trans hqq'.le⟩
    have hP := nativeSideWord_of_surviving_real j i d e hW hW0 hEqP
      (QuantumZipper.isForwardSol_restrict ha p.coe_nonneg hpq) hx hOldJump
    have hQ := nativeSideWord_of_surviving_real j i d e hW hW0 hEqQ ha hx hNowJump
    exact hP.trans hQ.symm

end InteractingSLE.Wire.Current.SideTest
