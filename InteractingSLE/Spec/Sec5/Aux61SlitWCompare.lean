/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSelected
import InteractingSLE.Spec.Sec5.Aux61SlitWLocal
import InteractingSLE.Spec.Sec5.Aux61NestMarks
import InteractingSLE.Spec.Sec5.GlueCond

/-! # The recorded comparison union and its retained initial germ -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open LawUnique Aux61ULoc GlueCond LocalSets WholeField Aux61ChLoc

variable {X : Type*}

/-- The later physical union is contained in the current union together
with the deterministic comparison hull. No path regularity is used. -/
theorem unionAt_max_subset_union {A : X → Set ℂ} {K : ℝ≥0 → X → Set ℂ}
    {T : X → ℝ≥0∞} (q : ℝ≥0) (x : X) :
    unionAt A K (fun x => max (T x) (q : ℝ≥0∞)) x ⊆ unionAt A K T x ∪ K q x := by
  by_cases hq : (q : ℝ≥0∞) ≤ T x
  · rw [unionAt_max_eq hq]
    exact subset_union_left
  have hT : T x < ⊤ := (not_le.1 hq).trans ENNReal.coe_lt_top
  have he : max (T x) (q : ℝ≥0∞) = q := max_eq_right (not_le.1 hq).le
  simp only [unionAt, he, ENNReal.coe_lt_top, hT, ↓reduceIte, ENNReal.toNNReal_coe]
  rintro z ⟨hzH, hzA | hzK⟩
  · exact Or.inl ⟨hzH, Or.inl hzA⟩
  · exact Or.inr hzK

/-- Deterministic hull reading commutes with retaining a later own prefix. -/
theorem hullAt_stopRec {nL nR : ℕ} (g : HistorySpace nL nR) {q t : ℝ≥0} (hqt : q ≤ t) :
    hullAt q (stopRec t g) = hullAt q g := by
  change Sec4.regHull (stopRec q (stopRec t g)) = Sec4.regHull (stopRec q g)
  rw [isRecordStop_stopRec.stop_stop q t g hqt]

/-- The deterministic comparison hull is recorded at the raised rule stop. -/
theorem measurable_comparisonHull {Y : Type*} [MeasurableSpace Y] {nL nR : ℕ}
    (Y₀ : X → Y) (R₀ : X → HistorySpace nL nR)
    (rule : Y × HistorySpace nL nR → ℝ≥0∞) (q : ℝ≥0) :
    Measurable[ruleMarks stopRec (fun p => max (rule p) (q : ℝ≥0∞)) Y₀ R₀, hittingSigma]
      (fun x => hullAt q (R₀ x)) := by
  have hm : Measurable[ruleMarks stopRec (fun _ => (q : ℝ≥0∞)) Y₀ R₀, hittingSigma]
      (fun x => hullAt q (stopAt stopRec (q : ℝ≥0∞) (R₀ x))) :=
    (measurable_hullAt q).comp (measurable_snd.comp (comap_measurable _))
  have he : (fun x => hullAt q (stopAt stopRec (q : ℝ≥0∞) (R₀ x))) =
      (fun x => hullAt q (R₀ x)) := by
    funext x
    simp only [stopAt, ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]
    exact hullAt_stopRec _ le_rfl
  rw [he] at hm
  exact hm.mono (comparisonMarks_le_max isRecordStop_stopRec Y₀ R₀ q) le_rfl

section Germ
variable {ℋ ℋ₀ ℳ : MeasurableSpace X} [mX : MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {h : X → DistOn upperHalfPlaneOpens}
  {A₀ A L R : X → Set ℂ} {S₀ : Set X}

/-- The actual comparison union can retain the initial live germ. Outside
the initial live event it is `H`, as the assembly's conditioning requires. -/
theorem isHistoryAvoidanceLocal_comparison_live_germ
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h μ) (hℳ : ℳ ≤ mX)
    (hℋ : ℋ ≤ ℳ) (h₀ : ℋ₀ ≤ ℳ) (hS : MeasurableSet[ℋ₀] S₀)
    (hA₀ : Measurable[ℋ₀, hittingSigma] A₀) (hA : Measurable[ℋ, hittingSigma] A)
    (hL : Measurable[ℳ, hittingSigma] L) (hnest : ∀ x, A₀ x ⊆ A x)
    (hraw : IsHistoryAvoidanceLocal ℳ R h μ)
    (hsub : ∀ᵐ x ∂μ, R x ⊆ A x ∪ L x) :
    IsHistoryAvoidanceLocal (ℳ ⊔ germSigma (liveSet S₀ A₀) h)
      (liveSet S₀ (fun x => A x ∪ L x)) h μ := by
  have hU : Measurable[ℳ, hittingSigma] (fun x => A x ∪ L x) :=
    @measurable_union_hitting X ℳ A L (hA.mono hℋ le_rfl) hL
  have hloc := Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hraw hU hsub
  have hlive := isHistoryAvoidanceLocal_liveSet hloc (h₀ _ hS)
  have hUm := (Aux61Nest.measurable_liveSet (h₀ _ hS) hU).mono hℳ le_rfl
  have hA₀m := Aux61Nest.measurable_liveSet (h₀ _ hS) (hA₀.mono h₀ le_rfl)
  apply Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℳ hUm hlive hA₀m
  intro x z hz
  by_cases hx : x ∈ S₀
  · rw [liveSet_of_mem hx] at hz ⊢
    exact Or.inl (hnest x hz.1)
  · rw [liveSet_of_notMem hx] at hz ⊢
    exact hz.1

end Germ
end InteractingSLE.Sec5.Aux61SlitW
