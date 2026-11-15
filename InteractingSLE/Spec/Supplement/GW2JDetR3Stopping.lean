/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR3Actual
import InteractingSLE.Spec.Supplement.GW2KM2PostStop
import InteractingSLE.Spec.Sec7.Lemma71IStop

/-!
# A physical-capacity rule measurable for the killed relative path

Freeze rational driver samples at the rational capacity being tested, read
their inverse-hull capacity, and apply the existing attained-level rule.
The resulting rule is measurable for the killed path at every time, exactly
as required by `GW2KM2.ae_condExp_recField_post_stop`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2JDetR3

open Exist.StagedLaw Sec7.Lemma71I

/-- A rational prefix record with the driver frozen at its endpoint. -/
def prefixRecord (q : ℚ≥0) (c : ℚ≥0 → ℝ) : RecData :=
  (fun r : ℚ => c (min r.toNNRat q), ((q : ℝ≥0) : ℝ≥0∞), false)

theorem measurable_prefixRecord (q : ℚ≥0) : Measurable (prefixRecord q) :=
  (measurable_pi_iff.mpr fun r => measurable_pi_apply (min r.toNNRat q)).prodMk
    (measurable_const.prodMk measurable_const)

theorem prefixRecord_congr (q : ℚ≥0) {c c' : ℚ≥0 → ℝ}
    (h : ∀ r ≤ q, c r = c' r) : prefixRecord q c = prefixRecord q c' := by
  apply Prod.ext
  · exact funext fun r => h _ (min_le_right _ _)
  · rfl

/-- Physical half capacity read from a rational prefix of relative samples. -/
def prefixCapacity (s : ℝ≥0) (q : ℚ≥0) (r : RecData) (c : ℚ≥0 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (physicalCapacity s (q : ℝ≥0) (r, prefixRecord q c))

theorem measurable_prefixCapacity (s : ℝ≥0) (q : ℚ≥0) :
    Measurable fun p : RecData × (ℚ≥0 → ℝ) => prefixCapacity s q p.1 p.2 :=
  ((measurable_physicalCapacity s q).comp
    (measurable_fst.prodMk ((measurable_prefixRecord q).comp measurable_snd))).ennreal_ofReal

theorem prefixCapacity_local (s : ℝ≥0) (q : ℚ≥0) (r : RecData)
    (c c' : ℚ≥0 → ℝ) (h : ∀ u ≤ q, c u = c' u) :
    prefixCapacity s q r c' = prefixCapacity s q r c := by
  unfold prefixCapacity
  rw [prefixRecord_congr q h]

open scoped Classical in
/-- Rational observations of the relative driver killed at its lifetime. -/
def killedCode (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (q : ℚ≥0) : ℝ :=
  if (((q : ℝ≥0) : ℝ≥0∞) < e.2) then e.1 (q : ℝ≥0) else 0

theorem measurable_killedCode : Measurable killedCode := by
  classical
  apply measurable_pi_iff.mpr
  intro q
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    ((measurable_pi_apply (q : ℝ≥0)).comp measurable_fst) measurable_const

/-- The attained physical-capacity level rule on killed relative paths. -/
def physicalCapacityStop (s : ℝ≥0) (Δ : ℝ≥0∞) (r : RecData)
    (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ≥0∞ :=
  levelRule (prefixCapacity s) Δ r (killedCode e)

/-- Joint measurability before substitution of the killed coordinates. -/
theorem measurable_capacityLevel (s : ℝ≥0) (Δ : ℝ≥0∞) :
    Measurable fun p : RecData × (ℚ≥0 → ℝ) => levelRule (prefixCapacity s) Δ p.1 p.2 :=
  measurable_levelRule (f := prefixCapacity s) (a := Δ) (measurable_prefixCapacity s)

theorem measurable_physicalCapacityStop (s : ℝ≥0) (Δ : ℝ≥0∞) :
    Measurable fun p : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞) => physicalCapacityStop s Δ p.1 p.2 := by
  let F : RecData × (ℚ≥0 → ℝ) → ℝ≥0∞ := fun p => levelRule (prefixCapacity s) Δ p.1 p.2
  let G : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞) → RecData × (ℚ≥0 → ℝ) :=
    fun p => (p.1, killedCode p.2)
  change Measurable (F ∘ G)
  have hp : Measurable (fun p : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞) =>
      (p.1, killedCode p.2)) :=
    measurable_fst.prodMk (measurable_killedCode.comp measurable_snd)
  have hF : Measurable F := measurable_capacityLevel s Δ
  exact hF.comp hp

/-- A killed rational observation before `t` is measurable for the killed-path
sigma-algebra at `t`, including its zero value after death. -/
theorem measurable_killedCode_before (t : ℝ≥0) (q : ℚ≥0) (hq : (q : ℝ≥0) ≤ t) :
    Measurable[GW2KM2.pathKilledSigma t] (fun e => killedCode e q) := by
  classical
  intro A hA
  have hObs : MeasurableSet[GW2KM2.pathKilledSigma t]
      {e : (ℝ≥0 → ℝ) × ℝ≥0∞ |
        ((q : ℝ≥0) : ℝ≥0∞) < e.2 ∧ e.1 (q : ℝ≥0) ∈ A} :=
    MeasurableSpace.measurableSet_generateFrom ⟨q, hq, A, hA, rfl⟩
  by_cases h0 : (0 : ℝ) ∈ A
  · have hAlive : MeasurableSet[GW2KM2.pathKilledSigma t]
        {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | ((q : ℝ≥0) : ℝ≥0∞) < e.2} := by
      have h : MeasurableSet[GW2KM2.pathKilledSigma t]
          {e : (ℝ≥0 → ℝ) × ℝ≥0∞ |
            ((q : ℝ≥0) : ℝ≥0∞) < e.2 ∧ e.1 (q : ℝ≥0) ∈ univ} :=
        MeasurableSpace.measurableSet_generateFrom
          ⟨(q : ℝ≥0), hq, univ, MeasurableSet.univ, rfl⟩
      simpa only [mem_univ, and_true] using h
    have heq : (fun e => killedCode e q) ⁻¹' A =
        {e | ((q : ℝ≥0) : ℝ≥0∞) < e.2 ∧ e.1 (q : ℝ≥0) ∈ A} ∪
          {e | ((q : ℝ≥0) : ℝ≥0∞) < e.2}ᶜ := by
      ext e
      by_cases he : ((q : ℝ≥0) : ℝ≥0∞) < e.2 <;> simp [killedCode, he, h0]
    rw [heq]
    exact hObs.union hAlive.compl
  · have heq : (fun e => killedCode e q) ⁻¹' A =
        {e | ((q : ℝ≥0) : ℝ≥0∞) < e.2 ∧ e.1 (q : ℝ≥0) ∈ A} := by
      ext e
      by_cases he : ((q : ℝ≥0) : ℝ≥0∞) < e.2 <;> simp [killedCode, he, h0]
    rw [heq]
    exact hObs

/-- Whether the capacity rule has stopped by `t` depends only on samples
through `t`, on arbitrary input codes. -/
theorem levelRule_le_congr (s : ℝ≥0) (Δ : ℝ≥0∞) (r : RecData) (t : ℝ≥0)
    {c c' : ℚ≥0 → ℝ} (h : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → c q = c' q) :
    levelRule (prefixCapacity s) Δ r c ≤ (t : ℝ≥0∞) ↔
      levelRule (prefixCapacity s) Δ r c' ≤ (t : ℝ≥0∞) := by
  constructor
  · intro hc
    have he := levelRule_galmarino (f := prefixCapacity s) (a := Δ)
      (prefixCapacity_local s) (x := r) (c := c) (c' := c')
      (fun q hq => h q (ENNReal.coe_le_coe.mp (hq.trans hc)))
    rwa [he]
  · intro hc'
    have he := levelRule_galmarino (f := prefixCapacity s) (a := Δ)
      (prefixCapacity_local s) (x := r) (c := c') (c' := c)
      (fun q hq => (h q (ENNReal.coe_le_coe.mp (hq.trans hc'))).symm)
    rwa [he]

/-- The exact killed-path stopping-functional premise needed by the landed
random-stage GFF law is proved for this concrete physical-capacity rule. -/
theorem measurableSet_physicalCapacityStop_le (s : ℝ≥0) (Δ : ℝ≥0∞) (r : RecData)
    (t : ℝ≥0) :
    MeasurableSet[GW2KM2.pathKilledSigma t]
      {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | physicalCapacityStop s Δ r e ≤ (t : ℝ≥0∞)} := by
  classical
  let C : ((ℝ≥0 → ℝ) × ℝ≥0∞) → (ℚ≥0 → ℝ) :=
    fun e q => if (q : ℝ≥0) ≤ t then killedCode e q else 0
  let _ : MeasurableSpace ((ℝ≥0 → ℝ) × ℝ≥0∞) := GW2KM2.pathKilledSigma t
  have hC : Measurable[GW2KM2.pathKilledSigma t] C := by
    apply measurable_pi_iff.mpr
    intro q
    by_cases hq : (q : ℝ≥0) ≤ t
    · simpa only [C, hq, ↓reduceIte] using measurable_killedCode_before t q hq
    · simp only [C, hq, ↓reduceIte]
      exact measurable_const
  let F : RecData × (ℚ≥0 → ℝ) → ℝ≥0∞ := fun p => levelRule (prefixCapacity s) Δ p.1 p.2
  have hF : Measurable F := measurable_capacityLevel s Δ
  have hpair : Measurable (fun c : ℚ≥0 → ℝ => (r, c)) :=
    measurable_const.prodMk measurable_id
  have hRule : Measurable (F ∘ fun c : ℚ≥0 → ℝ => (r, c)) := hF.comp hpair
  have heq : {e | physicalCapacityStop s Δ r e ≤ (t : ℝ≥0∞)} =
      (fun e => levelRule (prefixCapacity s) Δ r (C e)) ⁻¹' Iic (t : ℝ≥0∞) := by
    ext e
    exact levelRule_le_congr s Δ r t (fun q hq => by simp only [C, hq, ↓reduceIte])
  rw [heq]
  exact (hRule.comp hC) measurableSet_Iic

end InteractingSLE.Theorem14.GW2JDetR3
