/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61UnionKLocal
import InteractingSLE.Spec.Sec5.Aux61GlueKMem

/-!
# The live chart hull is a raw code event: measurability of the chart kernel's covariance

Packet PROVE-AUX61-CHARTLOC. The leaf `Aux61UnionK.IsChartLocalAt` conditions on the marks
`σ(Z) ∨ σ(raw code at q) ∨ σ(h₁)` and asserts that the conditional characteristic functional of the chart field minus
`h₁` is `exp(−½ ‖φ‖²_{H⁻¹(ℍ ∖ K_q)})` on `{Z ∈ B, q < life}`. To obtain it from a conditional decomposition given a
larger σ-algebra (tower property), the right side must be measurable for the marks. This file proves it:

* **`aliveHull q s`**: the hull at time `q` of the decoded driver of a code `s`, if `q < life`, and `∅` otherwise;
* **`measurable_aliveHull`**: it is measurable from the raw code σ-algebra at `q` (`codeFiltration q`) to the hitting
  σ-algebra (an open `U ⊆ ℍ` is hit iff some finite family of rational closed balls inside `U` is not safe; the safe
  events are raw code events, `Aux61GlueK.measurableSet_safeEv_fib`);
* **`measurableSet_lt_life`**: `{q < life}` is a raw code event at `q`;
* on a glued space with a history `Z` and a code `Y`: **`measurableSet_live`** (the live event `{Z ∈ B, q < life}` is
  measurable for any σ-algebra containing the history and the raw code at `q`), **`relClosureH_aliveHull`** (on the live
  event the relative closure of the alive hull is the chart hull), and **`measurable_cov_aliveHull`** (the covariance
  `zeroGFFTestCov (ℍ ∖ relClosureH (aliveHull q (Y x))) φ ψ` is measurable for any σ-algebra containing the raw code at
  `q`).

Generic; replaces no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Function
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61ChLoc

open Aux61Fib (FibCode fibW fibU)
open Aux61FibK (codeFiltration)
open Aux61UnionK (chartHull)
open LocalSets (relClosureH)
open Restart.DomainMarkov (safeEv)

universe u

/-! ### The alive hull of a code -/

open scoped Classical in
/-- **The alive hull** of a code at time `q`: the hull of its decoded driver at `q` if `q < life`, else `∅`. -/
def aliveHull (q : ℝ≥0) (s : ULift.{u} FibCode) : Set ℂ :=
  if (q : ℝ≥0∞) < s.down.life then fwdHull (fun r : ℝ => FibCode.driver r.toNNReal s.down) q else ∅

theorem aliveHull_of_lt {q : ℝ≥0} {s : ULift.{u} FibCode} (hq : (q : ℝ≥0∞) < s.down.life) :
    aliveHull q s = fwdHull (fun r : ℝ => FibCode.driver r.toNNReal s.down) q := by
  simp [aliveHull, hq]

theorem aliveHull_of_not_lt {q : ℝ≥0} {s : ULift.{u} FibCode} (hq : ¬ (q : ℝ≥0∞) < s.down.life) :
    aliveHull q s = ∅ := by
  simp [aliveHull, hq]

/-- **`{q < life}` is a raw code event at `q`** (the safe event of the empty family). -/
theorem measurableSet_lt_life (q : ℝ≥0) :
    MeasurableSet[codeFiltration.{u} q] {s : ULift.{u} FibCode | (q : ℝ≥0∞) < s.down.life} := by
  have hFH : Coupling.ballsK (∅ : Finset (ℚ × ℚ × ℚ)) ⊆ H := by simp [Coupling.ballsK]
  have e : {s : ULift.{u} FibCode | (q : ℝ≥0∞) < s.down.life} = safeEv fibW.{u} fibU ∅ q := by
    ext s
    simp [safeEv, Coupling.ballsK]
  rw [e]
  exact Aux61GlueK.measurableSet_safeEv_fib hFH q

/-- An open `U ⊆ ℍ` meets a set `K` iff some finite family of rational closed balls inside `U` meets `K`. -/
theorem nonempty_inter_iff_exists_ballsK {U K : Set ℂ} (hU : IsOpen U) :
    (K ∩ U).Nonempty ↔ ∃ F : Finset (ℚ × ℚ × ℚ), Coupling.ballsK F ⊆ U ∧ ¬ Disjoint (Coupling.ballsK F) K := by
  constructor
  · rintro ⟨z, hzK, hzU⟩
    obtain ⟨F, hzF, hFU⟩ := Coupling.exists_rationalBalls (K := {z}) isCompact_singleton hU
      (singleton_subset_iff.2 hzU)
    refine ⟨F, hFU, Set.not_disjoint_iff.2 ⟨z, Coupling.ballsU_subset_ballsK F (hzF rfl), hzK⟩⟩
  · rintro ⟨F, hFU, hF⟩
    obtain ⟨z, hzF, hzK⟩ := Set.not_disjoint_iff.1 hF
    exact ⟨z, hzK, hFU hzF⟩

/-- **The alive hull is measurable from the raw code σ-algebra at `q` to the hitting σ-algebra.** -/
theorem measurable_aliveHull (q : ℝ≥0) :
    Measurable[codeFiltration.{u} q, hittingSigma] (aliveHull.{u} q) := by
  refine @measurable_generateFrom _ _ (codeFiltration.{u} q) _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : aliveHull.{u} q ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ⋃ F : Finset (ℚ × ℚ × ℚ), ⋃ (_ : Coupling.ballsK F ⊆ U),
        {s : ULift.{u} FibCode | (q : ℝ≥0∞) < s.down.life} \ safeEv fibW.{u} fibU F q := by
    ext s
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, Set.mem_sdiff, safeEv, not_and, exists_prop]
    by_cases hq : (q : ℝ≥0∞) < s.down.life
    · rw [aliveHull_of_lt hq, nonempty_inter_iff_exists_ballsK hU]
      exact ⟨fun ⟨F, hFU, hF⟩ => ⟨F, hFU, hq, fun _ hd => hF hd⟩,
        fun ⟨F, hFU, _, hF⟩ => ⟨F, hFU, fun hd => hF hq hd⟩⟩
    · rw [aliveHull_of_not_lt hq]
      simp only [empty_inter, Set.not_nonempty_empty, false_iff, not_exists, not_and]
      exact fun F _ h => absurd h hq
  rw [e]
  refine MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun hFU => ?_
  exact (measurableSet_lt_life q).diff (Aux61GlueK.measurableSet_safeEv_fib (hFU.trans hUH) q)

/-! ### On a glued space with a history and a code -/

section Glued

variable {X : Type u} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]

omit mX in
/-- On `{q < life}`, the chart hull of the code is the alive hull. -/
theorem chartHull_eq_aliveHull {Y : X → FibCode} {q : ℝ≥0} {x : X} (hq : (q : ℝ≥0∞) < (Y x).life) :
    chartHull Y q x = aliveHull.{u} q (ULift.up (Y x)) :=
  (aliveHull_of_lt (s := ULift.up (Y x)) hq).symm

omit mX in
/-- On `{q < life}`, the relative closure in `ℍ` of the alive hull is the chart hull. -/
theorem relClosureH_aliveHull {Y : X → FibCode} {q : ℝ≥0} {x : X} (hq : (q : ℝ≥0∞) < (Y x).life) :
    relClosureH (aliveHull.{u} q (ULift.up (Y x))) = chartHull Y q x := by
  rw [← chartHull_eq_aliveHull hq]
  exact LocalSets.relClosureH_eq (fun _ hz => hz.1) (Aux61UnionK.isOpen_H_diff_chartHull Y hq)

omit mX in
/-- **The live event is measurable** for any σ-algebra containing the history and the raw code at `q`. -/
theorem measurableSet_live {m : MeasurableSpace X} {Z : X → β} (hZ : mβ.comap Z ≤ m) {Y : X → FibCode} {q : ℝ≥0}
    (hY : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ m) {B : Set β} (hB : MeasurableSet B) :
    MeasurableSet[m] {x | Z x ∈ B ∧ (q : ℝ≥0∞) < (Y x).life} := by
  have h1 : MeasurableSet[m] (Z ⁻¹' B) := hZ _ ⟨B, hB, rfl⟩
  have h2 : MeasurableSet[m] ((fun x => ULift.up.{u} (Y x)) ⁻¹'
      {s : ULift.{u} FibCode | (q : ℝ≥0∞) < s.down.life}) := hY _ ⟨_, measurableSet_lt_life q, rfl⟩
  exact h1.inter h2

omit mX in
/-- **The covariance of the complement of the alive hull is measurable** for any σ-algebra containing the raw code
at `q`. -/
theorem measurable_cov_aliveHull {m : MeasurableSpace X} {Y : X → FibCode} {q : ℝ≥0}
    (hY : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ m) (φ ψ : TestOn upperHalfPlaneOpens) :
    Measurable[m] fun x => zeroGFFTestCov (H \ relClosureH (aliveHull.{u} q (ULift.up (Y x)))) φ ψ := by
  have hA : Measurable[m, hittingSigma] fun x => aliveHull.{u} q (ULift.up (Y x)) :=
    (measurable_aliveHull.{u} q).comp (Measurable.of_comap_le hY)
  exact (LocalSets.measurable_zeroGFFTestCov_compl φ ψ).comp hA

end Glued

end InteractingSLE.Sec5.Aux61ChLoc
