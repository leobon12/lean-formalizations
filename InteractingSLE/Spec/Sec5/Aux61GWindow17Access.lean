/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Geometry
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextExit
import InteractingSLE.Spec.Sec5.Aux61SlitWYAccess

/-! # Actual access and inverse extension for the canonical family

All source hypotheses needed to use the existing deterministic capture
theorem are proved for the time-indexed normalized family.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData LawUnique
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The actual continuation satisfies every basic restart clause. -/
theorem canonicalFamily_restartPoint : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (canonicalFamily C).event i →
    Aux61SlitWX.RestartPoint
      (sourceChart (canonicalFamily C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
      (recordPath S ((canonicalFamily C).start i) p) ((canonicalFamily C).contact i p) := by
  intro i
  let t : GoodTime S := ⟨C.q i.1, i.2⟩
  let B := baseChoices S t.1
  have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
  filter_upwards [Aux61SlitWY.ae_restartPoint R B.hasChart (baseIndex S t)] with p hp he
  exact hp (show p ∈ B.toR1Restart.event (baseIndex S t) from ⟨mem_univ _, he.2⟩)

/-- The physical inverse has its continuous extension on all of Hbar. -/
theorem canonicalFamily_inverse_continuous : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (canonicalFamily C).event i →
    ContinuousOn (Aux61GInst.boundedInverse (sourceChart (canonicalFamily C)
      (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) Hbar := by
  intro i
  let t : GoodTime S := ⟨C.q i.1, i.2⟩
  let B := baseChoices S t.1
  have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
  filter_upwards [Aux61GCaptureNext.normalized_boundedInverse_continuous
    B.toR1Restart B.hasChart R (baseIndex S t)] with p hp he
  exact hp (show p ∈ B.toR1Restart.event (baseIndex S t) from ⟨mem_univ _, he.2⟩)

/-- Every finite actual contact has a nonzero real selected endpoint. -/
theorem canonicalFamily_real_endpoint : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (canonicalFamily C).event i →
    (canonicalFamily C).contact i p < ⊤ → ∃ y : ℝ, y ≠ 0 ∧ Tendsto
      (inPath ((canonicalFamily C).event i)
        (sourceChart (canonicalFamily C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((canonicalFamily C).path i) ((canonicalFamily C).contact i) p)
      (𝓝[<] ((canonicalFamily C).contact i p).toNNReal) (𝓝 (y : ℂ)) := by
  intro i
  let t : GoodTime S := ⟨C.q i.1, i.2⟩
  let B := baseChoices S t.1
  have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
  filter_upwards [Aux61SlitWY.ae_real_accessEndpoint R B.hasChart (baseIndex S t)] with p hp he
  have hb : p ∈ B.toR1Restart.event (baseIndex S t) := ⟨mem_univ _, he.2⟩
  intro hfin
  obtain ⟨y, hy, hl⟩ := hp hb hfin
  refine ⟨y, hy, hl.congr' (Eventually.of_forall fun v => ?_)⟩
  simp only [inPath, hb, he, true_and]
  rfl

end InteractingSLE.Sec5.Aux61GWindow17
