/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCThresholdDriverAEPath
import InteractingSLE.Spec.Restart.StoppedK2Wire

/-!
# Measurable realization of first-contact drivers

The source paths are only regular almost surely and only on their closed
available intervals. A measurable full event and clamping give continuous
measurable paths to which the prefix reconstruction applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

universe u

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- Clamping fixes every available time, including its endpoint. -/
theorem fcDriverStopTime_eq_of_le {U : Ω → ℝ≥0∞} {q : ℝ≥0} {ω : Ω}
    (hq : (q : ℝ≥0∞) ≤ U ω) : fcDriverStopTime U q ω = q := by
  classical
  unfold fcDriverStopTime
  split_ifs with ht
  · rfl
  · rw [min_eq_left]
    exact (ENNReal.coe_le_coe.1 (by simpa only [ENNReal.coe_toNNReal ht] using hq))

/-- Pointwise driver existence upgrades to measurable, everywhere continuous
zero-start drivers. The generating trace remains the supplied path, almost surely
on the given measurable live event. -/
theorem exists_measurable_driver_of_ae_exists_driver {P : Measure Ω} {M : Set Ω}
    (hM : MeasurableSet M) {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hm : ∀ t, Measurable fun ω => Γ ω t) (hU : Measurable U)
    (hgen : ∀ᵐ ω ∂P, ω ∈ M →
      ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧ IsGeneratingTrace W (U ω) (Γ ω)) :
    ∃ W : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (W t)) ∧
      (∀ ω, Continuous (W · ω)) ∧ (∀ ω, W 0 ω = 0) ∧
      ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (U ω) (Γ ω) := by
  classical
  let Good : Set Ω := {ω | ω ∈ M →
    ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧ IsGeneratingTrace W (U ω) (Γ ω)}
  let G : Set Ω := (toMeasurable P Goodᶜ)ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P _).compl
  have hGsub : G ⊆ Good := by
    intro ω hω
    by_contra hn
    exact hω (subset_toMeasurable P Goodᶜ hn)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have he : {ω | ¬ ω ∈ G} = toMeasurable P Goodᶜ := by
      ext ω
      simp only [G, mem_compl_iff, not_not, mem_ofPred_eq]
    rw [he, measure_toMeasurable]
    exact ae_iff.1 hgen
  let E : Set Ω := G ∩ M
  have hE : MeasurableSet E := hGm.inter hM
  have hg ω (hω : ω ∈ E) := hGsub hω.1 hω.2
  let Γc : Ω → ℝ≥0 → ℂ := fun ω t =>
    if ω ∈ E then Γ ω (fcDriverStopTime U t ω) else 0
  have hstopMeas (t : ℝ≥0) : Measurable (fcDriverStopTime U t) :=
    Measurable.ite (measurableSet_eq_fun hU measurable_const) measurable_const
      (measurable_const.min (ENNReal.measurable_toNNReal.comp hU))
  have hstopLe (t : ℝ≥0) (ω : Ω) : ((fcDriverStopTime U t ω : ℝ≥0) : ℝ≥0∞) ≤ U ω := by
    by_cases ht : U ω = ⊤
    · rw [ht]
      exact le_top
    · simp only [fcDriverStopTime, ht, ite_false]
      exact (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_eq (ENNReal.coe_toNNReal ht)
  have hcm : ∀ t, Measurable fun ω => Γc ω t := by
    intro t
    change Measurable (fun ω => if ω ∈ E then Γ ω (fcDriverStopTime U t ω) else 0)
    have hm' := measurable_piecewise_eval hE hm (hstopMeas t) fun ω hω =>
      (hg ω hω).choose_spec.2.2.2.1.mono fun r hr =>
        (ENNReal.coe_le_coe.2 hr).trans (hstopLe t ω)
    convert hm' using 1
    funext ω
    split_ifs <;> rfl
  have hc : ∀ ω, Continuous (Γc ω) := by
    intro ω
    by_cases hω : ω ∈ E
    · obtain ⟨W, -, -, htr⟩ := hg ω hω
      have he : Γc ω = fun t => Γ ω (fcDriverStopTime U t ω) :=
        funext fun t => by simp only [Γc, hω, ite_true]
      rw [he]
      by_cases ht : U ω = ⊤
      · have he' : (fun t => Γ ω (fcDriverStopTime U t ω)) = Γ ω :=
          funext fun t => by simp only [fcDriverStopTime, ht, ite_true]
        rw [he']
        apply continuousOn_univ.1
        apply htr.2.1.mono
        intro t _
        change (t : ℝ≥0∞) ≤ U ω
        rw [ht]
        exact le_top
      · have he' : (fun t => Γ ω (fcDriverStopTime U t ω)) =
            fun t => Γ ω (min t (U ω).toNNReal) :=
          funext fun t => by simp only [fcDriverStopTime, ht, ite_false]
        rw [he']
        exact htr.2.1.comp_continuous (continuous_id.min continuous_const) fun t =>
          (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_eq (ENNReal.coe_toNNReal ht)
    · simpa only [Γc, hω, ite_false] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℂ)))
  have hz : ∀ ω, Γc ω 0 = 0 := by
    intro ω
    by_cases hω : ω ∈ E
    · change (if ω ∈ E then Γ ω (fcDriverStopTime U 0 ω) else 0) = 0
      simp only [hω, ite_true]
      rw [fcDriverStopTime_eq_of_le (U := U) (q := 0) (ω := ω) (by exact zero_le)]
      exact (hg ω hω).choose_spec.2.2.1
    · simp only [Γc, hω, ite_false]
  refine ⟨fcTraceDriver Γc U, measurable_fcTraceDriver hc hcm hz hU,
    continuous_fcTraceDriver Γc U, fcTraceDriver_zero Γc U, ?_⟩
  filter_upwards [hGae] with ω hωG hωM
  have hω : ω ∈ E := ⟨hωG, hωM⟩
  obtain ⟨W, hW, hW0, ht⟩ := hg ω hω
  have he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U ω → Γc ω t = Γ ω t := by
    intro t htu
    change (if ω ∈ E then Γ ω (fcDriverStopTime U t ω) else 0) = Γ ω t
    simp only [hω, ite_true, fcDriverStopTime_eq_of_le htu]
  have htc := isGeneratingTrace_congr_le ht he
  exact StoppedK2.isGeneratingTrace_congr
    (fun t ht => (fcTraceDriver_eq hW hW0 htc ht).symm) ht

/-- Both canonical chart paths have measurable, everywhere continuous zero-start
 drivers on the actual source probability space. -/
theorem exists_measurable_drivers_canonClock
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hm₁ : ∀ t, Measurable fun ω => γ₁ ω t) (hm₂ : ∀ t, Measurable fun ω => γ₂ ω t)
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∃ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (W₁ t)) ∧ (∀ t, Measurable (W₂ t)) ∧
      (∀ ω, Continuous (W₁ · ω)) ∧ (∀ ω, Continuous (W₂ · ω)) ∧
      (∀ ω, W₁ 0 ω = 0) ∧ (∀ ω, W₂ 0 ω = 0) ∧
      ∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω) := by
  have hM : MeasurableSet (meetSet d) := retSigma_le P _ (hd.measurableSet_meetSet P)
  have hp := ae_exists_drivers_canonClock h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hcanon
  obtain ⟨W₁, hmW₁, hcW₁, hzW₁, hgW₁⟩ := exists_measurable_driver_of_ae_exists_driver hM hm₁ hU₁
    (hp.mono fun _ hω hM => (hω hM).1)
  obtain ⟨W₂, hmW₂, hcW₂, hzW₂, hgW₂⟩ := exists_measurable_driver_of_ae_exists_driver hM hm₂ hU₂
    (hp.mono fun _ hω hM => (hω hM).2)
  refine ⟨W₁, W₂, hmW₁, hmW₂, hcW₁, hcW₂, hzW₁, hzW₂, ?_⟩
  filter_upwards [hgW₁, hgW₂] with ω h₁ h₂ hm
  exact ⟨h₁ hm, h₂ hm⟩

end InteractingSLE.Restart.FCPlumb
