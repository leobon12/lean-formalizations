/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineSet
import InteractingSLE.Spec.Supplement.SB2DrvLineFill
import InteractingSLE.Spec.Supplement.SB2LcdKer
import InteractingSLE.Spec.Sec7.R5SameLate
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Filled versions of history-marked local sets

Packet PROVE-SB2-LCMEAN, round 3 (feeding SB2(2)'s union mean through B's stage chart,
`Ln.ae_chartTransport_eq_couplingMean_of_stagePullback`). The stage-chart pull-back needs the retained and explored
sets to contain the complement of B's run-chart domain, i.e. the FILLED earlier walk (`ℍ ∖ D = fill B_{<ℓ}`); the
landed locality results give history-marked local stage sets and their line versions (`Lcd.exists_lineVersion`).
Here a relatively closed, mark-measurable, marked-local set `B` is replaced by its filled version, which keeps every
one of these properties:

* `fillVer B ω`: `fill (closure (B ω))` where `B ω` is bounded, `B ω` elsewhere;
* `subset_fillVer`, `fillVer_subset_H`, `isOpen_H_diff_fillVer`, **`measurable_fillVer`**;
* **`fillVer_package`**: for marks `𝓜 ≤ mΩ` and a zero-boundary GFF `X`, the filled version is mark-measurable,
  relatively closed, history-marked local and a local set of `X`.

Generic and R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.SB.Mf

open LocalSets

variable {Ω : Type*}

open Classical in
/-- **The filled version** of a random set: the filled closure where bounded, the set itself elsewhere. -/
def fillVer (B : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  if Bornology.IsBounded (B ω) then fillH (closure (B ω)) else B ω

theorem fillVer_of_bounded {B : Ω → Set ℂ} {ω : Ω} (hb : Bornology.IsBounded (B ω)) :
    fillVer B ω = fillH (closure (B ω)) := by
  simp only [fillVer, hb, ↓reduceIte]

theorem fillVer_of_not_bounded {B : Ω → Set ℂ} {ω : Ω} (hb : ¬ Bornology.IsBounded (B ω)) :
    fillVer B ω = B ω := by
  simp only [fillVer, hb, ↓reduceIte]

theorem subset_fillVer {B : Ω → Set ℂ} (hB : ∀ ω, B ω ⊆ H) (ω : Ω) : B ω ⊆ fillVer B ω := by
  by_cases hb : Bornology.IsBounded (B ω)
  · rw [fillVer_of_bounded hb]
    intro z hz
    exact ⟨hB ω hz, Or.inl (subset_closure (subset_closure hz))⟩
  · rw [fillVer_of_not_bounded hb]

theorem fillVer_subset_H {B : Ω → Set ℂ} (hB : ∀ ω, B ω ⊆ H) (ω : Ω) : fillVer B ω ⊆ H := by
  by_cases hb : Bornology.IsBounded (B ω)
  · rw [fillVer_of_bounded hb]; exact fillH_subset_H _
  · rw [fillVer_of_not_bounded hb]; exact hB ω

theorem isOpen_H_diff_fillVer {B : Ω → Set ℂ} (hBo : ∀ ω, IsOpen (H \ B ω)) (ω : Ω) :
    IsOpen (H \ fillVer B ω) := by
  by_cases hb : Bornology.IsBounded (B ω)
  · rw [fillVer_of_bounded hb]; exact isOpen_H_diff_fillH hb.closure
  · rw [fillVer_of_not_bounded hb]; exact hBo ω

/-- **The filled version is measurable for the marks** of the set. -/
theorem measurable_fillVer {ℋ : MeasurableSpace Ω} {B : Ω → Set ℂ} (hB : ∀ ω, B ω ⊆ H)
    (hBm : Measurable[ℋ, hittingSigma] B) : Measurable[ℋ, hittingSigma] (fillVer B) := by
  have hav : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (B ω) U} :=
    fun U hUH => hBm (measurableSet_avoid U.isOpen hUH)
  have hbd : MeasurableSet[ℋ] {ω | Bornology.IsBounded (B ω)} := Lv.measurableSet_isBounded_of_avoid hB hav
  have hfm : Measurable[ℋ, hittingSigma] fun ω => fillH (Lv.cptClosure B ω) := Lv.measurable_fillH_cptClosure hB hav
  refine Sec7.R5Same.measurable_hitting_of_disjoint fun V hV hVH => ?_
  have e : {ω | Disjoint (fillVer B ω) V} =
      ({ω | Bornology.IsBounded (B ω)} ∩ {ω | Disjoint (fillH (Lv.cptClosure B ω)) V}) ∪
        ({ω | Bornology.IsBounded (B ω)}ᶜ ∩ {ω | Disjoint (B ω) V}) := by
    ext ω
    by_cases hb : Bornology.IsBounded (B ω)
    · have hc : Lv.cptClosure B ω = closure (B ω) := by simp only [Lv.cptClosure, hb, ↓reduceIte]
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, hb, fillVer_of_bounded hb, hc,
        true_and, not_true_eq_false, false_and, or_false]
    · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, hb, fillVer_of_not_bounded hb,
        false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  exact (hbd.inter (hfm (measurableSet_avoid hV hVH))).union (hbd.compl.inter (hBm (measurableSet_avoid hV hVH)))

/-- **The filled version of a marked local set**: mark-measurable, relatively closed, history-marked local, and a
local set of the field. -/
theorem fillVer_package {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P) (h𝓜 : 𝓜 ≤ mΩ) {B : Ω → Set ℂ}
    (hB : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hBm : Measurable[𝓜, hittingSigma] B) (hloc : WholeField.IsHistoryAvoidanceLocal 𝓜 B X P) :
    Measurable[𝓜, hittingSigma] (fillVer B) ∧ (∀ ω, fillVer B ω ⊆ H ∧ IsOpen (H \ fillVer B ω)) ∧
      WholeField.IsHistoryAvoidanceLocal 𝓜 (fillVer B) X P ∧ IsLocalSet (fillVer B) X P := by
  have hm := measurable_fillVer (fun ω => (hB ω).1) hBm
  have hc : ∀ ω, fillVer B ω ⊆ H ∧ IsOpen (H \ fillVer B ω) :=
    fun ω => ⟨fillVer_subset_H (fun ω => (hB ω).1) ω, isOpen_H_diff_fillVer (fun ω => (hB ω).2) ω⟩
  have hloc' : WholeField.IsHistoryAvoidanceLocal 𝓜 (fillVer B) X P :=
    Restart.RetAux79.isHistoryAvoidanceLocal_of_enlargement hloc
      (fun ω z hz => subset_fillVer (fun ω => (hB ω).1) ω hz.1) hm
  have hmΩ : Measurable[mΩ, hittingSigma] (fillVer B) := hm.mono h𝓜 le_rfl
  refine ⟨hm, hc, hloc', ?_⟩
  exact ((isLocalSet_tfae hX hmΩ (Eventually.of_forall hc)).out 4 1).2 hloc'.isAvoidanceLocal

end InteractingSLE.Theorem14.SB.Mf
