/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineSet
import InteractingSLE.Spec.Supplement.SB2ZsKer

/-!
# SB2ZsSet: `SB2DrvLineSet` for the lifetime-generic line version `SB2LineVersionG`

Packet PROVE-T14-SB2DRV (round 15, decision D4: SB2(1) at announced stops). The declarations of `SB2DrvLineSet` that
depend on the line version, for `SB2LineVersionG` (guards `a t < Λ w` in place of `a t < thr`), with the suffix `G`.
The proofs are the landed ones with the guard replaced. No source theorem is replaced.
-/
/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/

/-!
# SB2(1)'s line kernels, part 2: the line sets

Packet PROVE-T14-SB2DRV (round 4). The line sets of `hasSafeLaw_hasSafeMembers_of_lineSets` are chosen so that the hull
identity holds by definition: on the live cell `{a t < V}` of the type `w`, `B t = ℍ \ c(ℍ \ K_{a t})` (the complement
of the chart image of the relative hull's complement), elsewhere `B t = ℍ`. Here:

* `isHistoryAvoidanceLocal_of_ae_enlargement` (generic): an almost-sure enlargement with mark-measurable avoidance
  events of a history-marked local set is history-marked local;
* `chartImage c K = c(ℍ \ K)`, `mem_chartImage_iff`, `isOpen_chartImage`;
* **`measurableSet_inter_subset_chartImage`** (generic): for a measurable random chart and relatively closed random
  sets whose rational-ball avoidance events on `S` are measurable, `S ∩ {U ⊆ c(ℍ \ K)}` is measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open LocalSets Coupling

/-! ### Almost-sure enlargements -/

section Enlarge

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

end Enlarge

/-! ### Chart images of complements -/

/-! ### Measurability of the chart-image containment -/

section Meas

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω}

end Meas

/-! ### SB2(1)'s line sets -/

section SB2

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ} {I : K2LaunchInputs κ b jumps P h E k u ψ} {u₀ : ℂ → ℝ}
  {D : EntranceUnion κ b jumps P h E k u η ζ u₀}

/-- The relative hull at physical time `t` after `T_L`. -/
def relHullG (Vd : SB2LineVersionG HP I D) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
/-- The live part of the type cell `w` at physical time `t`: below the relative lifetime. -/
def lineLiveG (Vd : SB2LineVersionG HP I D) (w : WordType) (t : ℝ≥0) : Set Ω :=
  seedCell κ ψ I.word D.event w ∩
    {ω | Vd.a t ω < Vd.Λ w ω}
open Classical in
/-- **The line set** at physical time `t`: on the live cell the complement of the chart image of the relative hull's
complement, elsewhere all of `ℍ`. -/
def lineBG (Vd : SB2LineVersionG HP I D) (w : WordType) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  if ω ∈ lineLiveG Vd w t then H \ chartImage (I.chart ω) (relHullG Vd t ω) else H
theorem isOpen_H_sdiff_relHullG (Vd : SB2LineVersionG HP I D) (t : ℝ≥0) (ω : Ω) :
    IsOpen (H \ relHullG Vd t ω) :=
  QuantumZipper.FwdHolo.isOpen_compl_fwdHull ((Vd.W_cont ω).comp continuous_real_toNNReal) (NNReal.coe_nonneg _)
theorem lineB_subset_HG (Vd : SB2LineVersionG HP I D) (w : WordType) (t : ℝ≥0) (ω : Ω) : lineBG Vd w t ω ⊆ H := by
  unfold lineBG
  split_ifs
  · exact sdiff_subset
  · exact subset_rfl
theorem isOpen_H_sdiff_lineBG (Vd : SB2LineVersionG HP I D) (w : WordType) (t : ℝ≥0) (ω : Ω) :
    IsOpen (H \ lineBG Vd w t ω) := by
  unfold lineBG
  split_ifs
  · rw [Set.sdiff_sdiff_cancel_left (chartImage_subset_H (isConformal_chart I ω) _)]
    exact isOpen_chartImage (isConformal_chart I ω) (isOpen_H_sdiff_relHullG Vd t ω)
  · simp
/-- **The hull identity holds by construction.** -/
theorem H_sdiff_lineB_of_liveG (Vd : SB2LineVersionG HP I D) (w : WordType) (t : ℝ≥0) {ω : Ω}
    (hω : ω ∈ lineLiveG Vd w t) : H \ lineBG Vd w t ω = (I.chart ω).2.1 '' (H \ relHullG Vd t ω) := by
  unfold lineBG
  rw [ite_eq_left hω, Set.sdiff_sdiff_cancel_left (chartImage_subset_H (isConformal_chart I ω) _)]
  rfl
theorem measurableSet_lineLiveG (Vd : SB2LineVersionG HP I D) {w : WordType} (hw : w ∈ I.types) (t : ℝ≥0) :
    MeasurableSet[D.lineFiltC HP t] (lineLiveG Vd w t) := by
  have hF : MeasurableSet[D.lineFiltC HP t] (seedCell κ ψ I.word D.event w) :=
    (D.marks_le_lineFiltC HP t) _ (measurableSet_seedCell (I.word_measurable.mono D.past_le_marks le_rfl)
      (D.measurableSet_event HP) w)
  have h1 := Vd.safeL w hw ∅ t
  have e : {ω | Vd.a t ω < Vd.Λ w ω ∧
      Disjoint (ballsK ∅) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal)} =
      {ω | Vd.a t ω < Vd.Λ w ω} := by
    ext ω
    simp [ballsK]
  rw [e] at h1
  exact hF.inter h1
/-- The avoidance events of the line set are events of the line filtration. -/
theorem measurableSet_disjoint_lineBG (Vd : SB2LineVersionG HP I D) {w : WordType} (hw : w ∈ I.types) (t : ℝ≥0)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) :
    MeasurableSet[D.lineFiltC HP t] {ω | Disjoint (lineBG Vd w t ω) U} := by
  classical
  have hpast : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ D.lineFiltC HP t :=
    D.past_le_marks.trans (D.marks_le_lineFiltC HP t)
  obtain ⟨hc, -, -, hdom, hfwd, hCm, -⟩ := I.chart_measurable
  have hlive := measurableSet_lineLiveG Vd hw t
  have hS : ∀ Fb : Finset (ℚ × ℚ × ℚ), MeasurableSet[D.lineFiltC HP t]
      (lineLiveG Vd w t ∩ {ω | Disjoint (ballsK Fb) (relHullG Vd t ω)}) := by
    intro Fb
    have hF : MeasurableSet[D.lineFiltC HP t] (seedCell κ ψ I.word D.event w) :=
      (D.marks_le_lineFiltC HP t) _ (measurableSet_seedCell (I.word_measurable.mono D.past_le_marks le_rfl)
        (D.measurableSet_event HP) w)
    have e : lineLiveG Vd w t ∩ {ω | Disjoint (ballsK Fb) (relHullG Vd t ω)} = seedCell κ ψ I.word D.event w ∩
        {ω | Vd.a t ω < Vd.Λ w ω ∧
          Disjoint (ballsK Fb) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal)} := by
      ext ω
      simp only [lineLiveG, relHullG, mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [e]
    exact hF.inter (Vd.safeL w hw Fb t)
  have hmain := measurableSet_inter_subset_chartImage (𝒢 := D.lineFiltC HP t) hc (fun z => hpast _ (hdom z))
    (fun z => (hfwd z).mono hpast le_rfl) (fun z ε => hpast _ (hCm z ε))
    (fun ω _ => isOpen_H_sdiff_relHullG Vd t ω) hS U.isOpen
  have e : {ω | Disjoint (lineBG Vd w t ω) U} =
      (lineLiveG Vd w t ∩ {ω | (U : Set ℂ) ⊆ chartImage (I.chart ω) (relHullG Vd t ω)}) ∪
        ((lineLiveG Vd w t)ᶜ ∩ {_ω | Disjoint H (U : Set ℂ)}) := by
    ext ω
    by_cases hω : ω ∈ lineLiveG Vd w t
    · simp only [lineBG, mem_ofPred_eq, mem_union, mem_inter_iff, hω, true_and, mem_compl_iff,
        not_true_eq_false, false_and, or_false]
      constructor
      · intro hd z hz
        by_contra hn
        exact Set.disjoint_left.1 hd ⟨hUH hz, hn⟩ hz
      · intro hs
        exact Set.disjoint_left.2 fun z hz hzU => hz.2 (hs hzU)
    · simp only [lineBG, mem_ofPred_eq, mem_union, mem_inter_iff, hω, false_and, mem_compl_iff,
        not_false_eq_true, true_and, false_or, ↓reduceIte]
  rw [e]
  exact hmain.union (hlive.compl.inter (MeasurableSet.const _))
end SB2

end InteractingSLE.Theorem14.SB.Lv

