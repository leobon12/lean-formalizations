/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1DetUnique
import InteractingSLE.Spec.Sec7.CounterflowProb2Coding
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The Borel graph needed for deterministic retargeting

Packet PROVE-GW1-DET. Uniqueness is unconditional in `GW1DetUnique`.
This file reduces the remaining Borel assertion to measurability of the exact
retargeting graph on countable rational path codes. Lusin--Souslin, not a
measurable choice assumption, supplies both the measurable existence set and
the jointly measurable driver once this graph is known to be Borel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Theorem14.GW1Det

open GW1Path

/-- A continuous normalized driver is recovered by the existing regularization
of its rational-time code. -/
theorem regQ_restrict {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    (fun t => Sec7.Coding.regQ t (fun q : ℚ≥0 => w q)) = w := by
  funext t
  have ht := congrFun (Sec7.Coding.drive_regQ hw hw0) (t : ℝ)
  simpa only [QuantumZipper.drive, Real.sqrt_one, one_mul, Real.toNNReal_coe] using ht

/-- The exact retargeting graph on rational path codes. The output code is
required to be the rational restriction of its regularization, so projection
to the source code and target is injective. Its measurability is not asserted
by this definition. -/
def retargetGraph : Set (((ℚ≥0 → ℝ) × ℝ) × (ℚ≥0 → ℝ)) :=
  {p | (∀ q : ℚ≥0, p.2 q = Sec7.Coding.regQ q p.2) ∧
    IsRegCf (fun t => Sec7.Coding.regQ t p.1.1) ∧ p.1.2 ≠ 0 ∧
    (p.1.2 : ℂ) ∈ infinitySourceChart.tipSet (fun t => Sec7.Coding.regQ t p.1.1) ⊤ ∧
    IsRetargetOf (fun t => Sec7.Coding.regQ t p.2) (fun t => Sec7.Coding.regQ t p.1.1) p.1.2}

/-- The source code and target determine a point of the retargeting graph. -/
theorem retargetGraph_fst_injective :
    Function.Injective (fun x : retargetGraph => x.1.1) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext hxy
  have he : (fun t => Sec7.Coding.regQ t x.1.2) = fun t => Sec7.Coding.regQ t y.1.2 := by
    apply isRetargetOf_unique (Sec7.Coding.continuous_regQ _) (Sec7.Coding.continuous_regQ _)
      x.2.2.2.2.2
    simpa only [← hxy] using y.2.2.2.2.2
  funext q
  exact (x.2.1 q).trans ((congrFun he q).trans (y.2.1 q).symm)

/-- **Conditional Borel construction.** The exact missing proposition is
`MeasurableSet retargetGraph`. Given it, all of `DetRetargetStatement`, including
the measurable existence set and joint driver map, follows from the proved
uniqueness theorem and Mathlib's Lusin--Souslin theorem. -/
theorem detRetargetStatement_of_measurableSet_retargetGraph
    (hgraph : MeasurableSet retargetGraph) : DetRetargetStatement := by
  let : StandardBorelSpace retargetGraph := hgraph.standardBorel
  let j : retargetGraph → (ℚ≥0 → ℝ) × ℝ := fun x => x.1.1
  have hjm : Measurable j := measurable_fst.comp measurable_subtype_coe
  have hj : MeasurableEmbedding j := hjm.measurableEmbedding retargetGraph_fst_injective
  have hsm : Measurable (fun x : retargetGraph => x.1.2) := measurable_snd.comp measurable_subtype_coe
  obtain ⟨g, hgm, hgj⟩ := hj.exists_measurable_extend hsm (fun _ => inferInstance)
  let code : ((ℝ≥0 → ℝ) × ℝ) → (ℚ≥0 → ℝ) × ℝ := fun p => ((fun q => p.1 q), p.2)
  have hres : Measurable (fun p : ((ℝ≥0 → ℝ) × ℝ) => fun q : ℚ≥0 => p.1 q) :=
    measurable_pi_iff.2 fun q => (measurable_pi_apply (q : ℝ≥0)).comp measurable_fst
  have hcode : Measurable code := hres.prodMk measurable_snd
  let R : (ℝ≥0 → ℝ) → ℝ → ℝ≥0 → ℝ := fun Q v t => Sec7.Coding.regQ t (g (code (Q, v)))
  refine ⟨R, code ⁻¹' range j, fun t => (Sec7.Coding.measurable_regQ t).comp (hgm.comp hcode),
    hj.measurableSet_range.preimage hcode, ?_⟩
  intro Q v hQ
  have hQc : (fun t => Sec7.Coding.regQ t (fun q : ℚ≥0 => Q q)) = Q := regQ_restrict hQ.1 hQ.2.1
  have hmem : code (Q, v) ∈ range j ↔ v ≠ 0 ∧ (v : ℂ) ∈ infinitySourceChart.tipSet Q ⊤ ∧
      ∃ U : ℝ≥0 → ℝ, Continuous U ∧ IsRetargetOf U Q v := by
    constructor
    · rintro ⟨x, hx⟩
      have hxp : x.1.1 = ((fun q : ℚ≥0 => Q q), v) := hx
      have hxv := x.2.2
      rw [hxp, hQc] at hxv
      exact ⟨hxv.2.1, hxv.2.2.1, _, Sec7.Coding.continuous_regQ _, hxv.2.2.2⟩
    · rintro ⟨hv, hvis, U, hUc, hret⟩
      obtain ⟨γ, hγ, -⟩ := hret.1
      have hU0 := Sec7.SideHeight.w_zero_of_isGeneratingTrace hγ (by simp)
      have hUr := regQ_restrict hUc hU0
      let x : retargetGraph := ⟨(((fun q : ℚ≥0 => Q q), v), fun q : ℚ≥0 => U q), by
        refine ⟨fun q => (congrFun hUr q).symm, ?_⟩
        change IsRegCf (fun t => Sec7.Coding.regQ t (fun q : ℚ≥0 => Q q)) ∧ v ≠ 0 ∧
          (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => Sec7.Coding.regQ t (fun q : ℚ≥0 => Q q)) ⊤ ∧
          IsRetargetOf (fun t => Sec7.Coding.regQ t (fun q : ℚ≥0 => U q))
            (fun t => Sec7.Coding.regQ t (fun q : ℚ≥0 => Q q)) v
        rw [hQc, hUr]
        exact ⟨hQ, hv, hvis, hret⟩⟩
      exact ⟨x, rfl⟩
  refine ⟨hmem, ?_⟩
  intro hG
  obtain ⟨x, hx⟩ := hG
  have hxp : x.1.1 = ((fun q : ℚ≥0 => Q q), v) := hx
  have hRx : R Q v = fun t => Sec7.Coding.regQ t x.1.2 := by
    change (fun t => Sec7.Coding.regQ t (g (code (Q, v)))) = _
    rw [← hx]
    exact congrArg (fun f t => Sec7.Coding.regQ t f) (congrFun hgj x)
  have hRc : Continuous (R Q v) := hRx ▸ Sec7.Coding.continuous_regQ _
  have hretR : IsRetargetOf (R Q v) Q v := by
    rw [hRx]
    have hxret := x.2.2.2.2.2
    rw [hxp, hQc] at hxret
    exact hxret
  refine ⟨hRc, fun U hUc => ⟨fun hret => isRetargetOf_unique hUc hRc hret hretR, ?_⟩⟩
  rintro rfl
  exact hretR

end InteractingSLE.Theorem14.GW1Det
