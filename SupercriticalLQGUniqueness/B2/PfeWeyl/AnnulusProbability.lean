import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPWeyl

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


def AnnulusTailInput {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    (P : Measure Ω) (a : Ω → ℝ≥0∞) (b : ι → Ω → ℝ≥0∞) : Prop :=
  (∀ η : ℝ≥0∞, 0 < η →
    ∃ T : ℝ≥0∞, T ≠ ⊤ ∧ P {ω | T ≤ a ω} ≤ η) ∧
  (∀ T : ℝ≥0∞, T ≠ ⊤ → ∀ η : ℝ≥0∞, 0 < η →
    ∀ᶠ R in atTop, P {ω | b R ω ≤ T} ≤ η)

 
private theorem annulus_cost_comparison {c a b T : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcfin : c ≠ ⊤) (ha : a < T)
    (hb : c * (c + T) < b) :
    c + a < c⁻¹ * b := by
  have hmul : (c + a) * c < (c + T) * c :=
    (ENNReal.mul_lt_mul_iff_left hc0 hcfin).2
      (ENNReal.add_lt_add_left hcfin ha)
  have hmul' : (c + a) * c < b := by
    exact hmul.trans (by simpa only [mul_comm] using hb)
  have hcancel : (c⁻¹ * b) * c = b := by
    calc
      (c⁻¹ * b) * c = b * (c⁻¹ * c) := by ac_rfl
      _ = b := by rw [ENNReal.inv_mul_cancel hc0 hcfin, mul_one]
  have hgoal : (c + a) * c < (c⁻¹ * b) * c := by
    rw [hcancel]
    exact hmul'
  exact (ENNReal.mul_lt_mul_iff_left hc0 hcfin).1 hgoal

 

theorem annulus_bad_probability_tendsto_zero_of_annulusInput
    {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι] (P : Measure Ω)
    (a : Ω → ℝ≥0∞) (b : ι → Ω → ℝ≥0∞)
    (hinput : AnnulusTailInput P a b)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcfin : c ≠ ⊤) :
    Tendsto (fun R : ι => P {ω | ¬ c + a ω < c⁻¹ * b R ω}) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨T, hTfin, hA⟩ := hinput.1 (η / 2)
    ((ENNReal.div_pos_iff).2 ⟨hη.ne', by simp⟩)
  have hthreshold : c * (c + T) ≠ ⊤ :=
    ENNReal.mul_ne_top hcfin
      ((ENNReal.add_lt_top).2
        ⟨lt_top_iff_ne_top.2 hcfin, lt_top_iff_ne_top.2 hTfin⟩).ne
  filter_upwards [hinput.2 (c * (c + T)) hthreshold (η / 2)
    ((ENNReal.div_pos_iff).2 ⟨hη.ne', by simp⟩)] with R hB
  have hsubset : {ω | ¬ c + a ω < c⁻¹ * b R ω} ⊆
      {ω | T ≤ a ω} ∪ {ω | b R ω ≤ c * (c + T)} := by
    intro ω hω
    by_cases ha : a ω < T
    · right
      by_contra hb
      exact hω (annulus_cost_comparison hc0 hcfin ha (lt_of_not_ge hb))
    · exact Or.inl (le_of_not_gt ha)
  calc
    P {ω | ¬ c + a ω < c⁻¹ * b R ω} ≤
        P ({ω | T ≤ a ω} ∪ {ω | b R ω ≤ c * (c + T)}) :=
      measure_mono hsubset
    _ ≤ P {ω | T ≤ a ω} + P {ω | b R ω ≤ c * (c + T)} :=
      measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hA hB
    _ = η := ENNReal.add_halves η

 

theorem geo_annuli_prob_of_annulusInput
    {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (a : Ω → ℝ≥0∞)
    (b : ι → Ω → ℝ≥0∞) (ha : Measurable a)
    (hb : ∀ R, Measurable (b R))
    (hinput : AnnulusTailInput P a b)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcfin : c ≠ ⊤) :
    Tendsto (fun R : ι => P {ω | c + a ω < c⁻¹ * b R ω}) atTop (𝓝 1) := by
  have hbad := annulus_bad_probability_tendsto_zero_of_annulusInput
    P a b hinput hc0 hcfin
  have hcompl (R : ι) :
      P {ω | c + a ω < c⁻¹ * b R ω} =
        1 - P {ω | ¬ c + a ω < c⁻¹ * b R ω} := by
    let E : Set Ω := {ω | c + a ω < c⁻¹ * b R ω}
    have hE : MeasurableSet E :=
      measurableSet_lt (measurable_const.add ha)
        (measurable_const.mul (hb R))
    have hEcfin : P Eᶜ ≠ ⊤ := by
      have hle : P Eᶜ ≤ 1 := by
        simpa only [measure_univ] using
          (measure_mono (subset_univ Eᶜ) : P Eᶜ ≤ P univ)
      exact (hle.trans_lt (by simp)).ne
    have heq := measure_compl hE.compl hEcfin
    simpa only [E, Set.compl_ofPred, measure_univ, compl_compl, not_not] using heq
  simp_rw [hcompl]
  have hpair : Tendsto (fun R : ι =>
      ((1 : ℝ≥0∞), P {ω | ¬ c + a ω < c⁻¹ * b R ω}))
      atTop (𝓝 ((1 : ℝ≥0∞), (0 : ℝ≥0∞))) :=
    tendsto_const_nhds.prodMk_nhds hbad
  have hsub := (ENNReal.tendsto_sub (Or.inl ENNReal.one_ne_top)).comp hpair
  simpa [Function.comp_def] using hsub

end SupercriticalLQGUniqueness.B2.PfeWeyl
