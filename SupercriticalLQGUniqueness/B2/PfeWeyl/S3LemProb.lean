import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

 














set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

variable {S T : Type*} [MeasurableSpace S] [PseudoEMetricSpace T] [MeasurableSpace T]
  [BorelSpace T] [SecondCountableTopology T]

 
theorem measure_le_edist_le {μ : Measure S} {f g : S → T} (hf : Measurable f)
    (hg : Measurable g) {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha1 : a ≤ 1) :
    μ {x | a ≤ edist (f x) (g x)} ≤ (∫⁻ x, min (edist (f x) (g x)) 1 ∂μ) / a :=
  calc μ {x | a ≤ edist (f x) (g x)} ≤ μ {x | a ≤ min (edist (f x) (g x)) 1} :=
        measure_mono fun _ hx => le_min hx ha1
    _ ≤ (∫⁻ x, min (edist (f x) (g x)) 1 ∂μ) / a :=
        meas_ge_le_lintegral_div (((hf.edist hg).min measurable_const).aemeasurable) ha0
          (ne_top_of_le_ne_top ENNReal.one_ne_top ha1)

 
theorem tendstoInMeasure_of_coupling
    (μ : Measure S) (R : ℕ → S → T) (Φ : S → T) (hR : ∀ n, Measurable (R n))
    (hΦ : Measurable Φ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → S) (Xl : Ω' → S) (hXm : ∀ n, Measurable (X n)) (hXlm : Measurable Xl)
    (hXlaw : ∀ n, P'.map (X n) = μ) (hXllaw : P'.map Xl = μ)
    (Y : ℕ → Ω' → T) (hYm : ∀ n, Measurable (Y n)) (hY : ∀ n, Y n =ᵐ[P'] R n ∘ X n)
    (hYconv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Φ (Xl ω))))
    (happrox : ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : S → T, Measurable Ψ ∧
      (∫⁻ g, min (edist (Φ g) (Ψ g)) 1 ∂μ) < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (X n ω)) atTop (𝓝 (Ψ (Xl ω)))) :
    TendstoInMeasure μ R atTop Φ := by
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  
  set a : ℝ≥0∞ := min (ε / 2 / 2) 1 with hadef
  have ha0 : a ≠ 0 := by
    rw [hadef]
    exact (lt_min (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne') one_pos).ne'
  have ha1 : a ≤ 1 := min_le_right _ _
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have haε : a ≤ ε / 2 / 2 := min_le_left _ _
  have hκ4 : 0 < κ / 2 / 2 := ENNReal.half_pos (ENNReal.half_pos hκ.ne').ne'
  obtain ⟨Ψ, hΨ, hΨint, hΨconv⟩ := happrox (κ / 2 / 2 * a)
    (ENNReal.mul_pos hκ4.ne' ha0)
  have hP'fin : ∀ s, P' s ≠ ⊤ := fun s => measure_ne_top P' s
  
  have hA : Tendsto (fun n => P' {ω | a ≤ edist (Y n ω) (Φ (Xl ω))}) atTop (𝓝 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hYm n).aestronglyMeasurable) hYconv a
      (pos_iff_ne_zero.2 ha0)
  have hC : Tendsto (fun n => P' {ω | a ≤ edist (Ψ (X n ω)) (Ψ (Xl ω))}) atTop (𝓝 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hΨ.comp (hXm n)).aestronglyMeasurable)
      hΨconv a (pos_iff_ne_zero.2 ha0)
  
  have hB : μ {g | a ≤ edist (Φ g) (Ψ g)} ≤ κ / 2 / 2 := by
    refine (measure_le_edist_le hΦ hΨ ha0 ha1).trans ?_
    calc (∫⁻ g, min (edist (Φ g) (Ψ g)) 1 ∂μ) / a ≤ (κ / 2 / 2 * a) / a :=
          ENNReal.div_le_div_right hΨint.le a
      _ = κ / 2 / 2 := ENNReal.mul_div_cancel_right ha0 hatop
  have hsetB : ∀ (Z : Ω' → S), Measurable Z → P'.map Z = μ →
      P' {ω | a ≤ edist (Φ (Z ω)) (Ψ (Z ω))} ≤ κ / 2 / 2 := by
    intro Z hZ hZlaw
    have hmeas : MeasurableSet {g : S | a ≤ edist (Φ g) (Ψ g)} :=
      measurableSet_le measurable_const (hΦ.edist hΨ)
    have := Measure.map_apply hZ hmeas (μ := P')
    rw [hZlaw] at this
    rw [show {ω | a ≤ edist (Φ (Z ω)) (Ψ (Z ω))} = Z ⁻¹' {g | a ≤ edist (Φ g) (Ψ g)} from rfl,
      ← this]
    exact hB
  have hsum : Tendsto (fun n => P' {ω | a ≤ edist (Y n ω) (Φ (Xl ω))} +
      P' {ω | a ≤ edist (Ψ (X n ω)) (Ψ (Xl ω))}) atTop (𝓝 0) := by
    simpa using hA.add hC
  have hev := (ENNReal.tendsto_nhds_zero.1 hsum) (κ / 2) (ENNReal.half_pos hκ.ne')
  filter_upwards [hev] with n hn
  
  have hmeasn : MeasurableSet {g : S | ε ≤ edist (R n g) (Φ g)} :=
    measurableSet_le measurable_const ((hR n).edist hΦ)
  have hmap := Measure.map_apply (hXm n) hmeasn (μ := P')
  rw [hXlaw n] at hmap
  rw [hmap]
  have hcongr : P' (X n ⁻¹' {g | ε ≤ edist (R n g) (Φ g)}) =
      P' {ω | ε ≤ edist (Y n ω) (Φ (X n ω))} := by
    refine measure_congr ?_
    filter_upwards [hY n] with ω hω
    simp only [eq_iff_iff]
    change ε ≤ edist (R n (X n ω)) (Φ (X n ω)) ↔ ε ≤ edist (Y n ω) (Φ (X n ω))
    rw [hω]
    rfl
  rw [hcongr]
  
  have hsub : {ω | ε ≤ edist (Y n ω) (Φ (X n ω))} ⊆
      {ω | a ≤ edist (Y n ω) (Φ (Xl ω))} ∪ {ω | a ≤ edist (Φ (Xl ω)) (Ψ (Xl ω))} ∪
        {ω | a ≤ edist (Ψ (X n ω)) (Ψ (Xl ω))} ∪ {ω | a ≤ edist (Φ (X n ω)) (Ψ (X n ω))} := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hnot
    have h1' : edist (Y n ω) (Φ (Xl ω)) < a := not_le.1 h1
    have h2' : edist (Φ (Xl ω)) (Ψ (Xl ω)) < a := not_le.1 h2
    have h3' : edist (Ψ (X n ω)) (Ψ (Xl ω)) < a := not_le.1 h3
    have h4' : edist (Φ (X n ω)) (Ψ (X n ω)) < a := not_le.1 h4
    have htri : edist (Y n ω) (Φ (X n ω)) ≤ edist (Y n ω) (Φ (Xl ω)) +
        edist (Φ (Xl ω)) (Ψ (Xl ω)) + edist (Ψ (X n ω)) (Ψ (Xl ω)) +
        edist (Φ (X n ω)) (Ψ (X n ω)) := by
      calc edist (Y n ω) (Φ (X n ω))
          ≤ edist (Y n ω) (Φ (Xl ω)) + edist (Φ (Xl ω)) (Φ (X n ω)) := edist_triangle _ _ _
        _ ≤ edist (Y n ω) (Φ (Xl ω)) + (edist (Φ (Xl ω)) (Ψ (Xl ω)) +
              edist (Ψ (Xl ω)) (Ψ (X n ω)) + edist (Ψ (X n ω)) (Φ (X n ω))) := by
            gcongr
            exact edist_triangle4 _ _ _ _
        _ = _ := by
            rw [edist_comm (Ψ (Xl ω)), edist_comm (Ψ (X n ω)) (Φ (X n ω))]
            ring
    have hlt : edist (Y n ω) (Φ (Xl ω)) + edist (Φ (Xl ω)) (Ψ (Xl ω)) +
        edist (Ψ (X n ω)) (Ψ (Xl ω)) + edist (Φ (X n ω)) (Ψ (X n ω)) < ε := by
      have h4a : a + a + a + a ≤ ε := by
        calc a + a + a + a ≤ ε / 2 / 2 + ε / 2 / 2 + ε / 2 / 2 + ε / 2 / 2 := by gcongr
          _ = ε := by
            rw [ENNReal.add_halves, add_assoc, ENNReal.add_halves, ENNReal.add_halves]
      exact lt_of_lt_of_le (ENNReal.add_lt_add (ENNReal.add_lt_add (ENNReal.add_lt_add h1' h2')
        h3') h4') h4a
    exact (not_le.2 (htri.trans_lt hlt)) hω
  calc P' {ω | ε ≤ edist (Y n ω) (Φ (X n ω))}
      ≤ P' {ω | a ≤ edist (Y n ω) (Φ (Xl ω))} + P' {ω | a ≤ edist (Φ (Xl ω)) (Ψ (Xl ω))} +
        P' {ω | a ≤ edist (Ψ (X n ω)) (Ψ (Xl ω))} +
        P' {ω | a ≤ edist (Φ (X n ω)) (Ψ (X n ω))} := by
        refine (measure_mono hsub).trans ?_
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ (κ / 2) + (κ / 2 / 2 + κ / 2 / 2) := by
        have h2 := hsetB Xl hXlm hXllaw
        have h4 := hsetB (X n) (hXm n) (hXlaw n)
        calc _ = (P' {ω | a ≤ edist (Y n ω) (Φ (Xl ω))} +
                P' {ω | a ≤ edist (Ψ (X n ω)) (Ψ (Xl ω))}) +
              (P' {ω | a ≤ edist (Φ (Xl ω)) (Ψ (Xl ω))} +
                P' {ω | a ≤ edist (Φ (X n ω)) (Ψ (X n ω))}) := by ring
          _ ≤ _ := add_le_add hn (add_le_add h2 h4)
    _ = κ := by
        rw [ENNReal.add_halves, ENNReal.add_halves]

 

theorem exists_subseq_ae_of_coupling
    (μ : Measure S) (R : ℕ → S → T) (Φ : S → T) (hR : ∀ n, Measurable (R n))
    (hΦ : Measurable Φ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → S) (Xl : Ω' → S) (hXm : ∀ n, Measurable (X n)) (hXlm : Measurable Xl)
    (hXlaw : ∀ n, P'.map (X n) = μ) (hXllaw : P'.map Xl = μ)
    (Y : ℕ → Ω' → T) (hYm : ∀ n, Measurable (Y n)) (hY : ∀ n, Y n =ᵐ[P'] R n ∘ X n)
    (hYconv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Φ (Xl ω))))
    (happrox : ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : S → T, Measurable Ψ ∧
      (∫⁻ g, min (edist (Φ g) (Ψ g)) 1 ∂μ) < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (X n ω)) atTop (𝓝 (Ψ (Xl ω)))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → S), AEMeasurable h P →
        P.map h = μ → ∀ᵐ ω ∂P, Tendsto (fun k => R (ns k) (h ω)) atTop (𝓝 (Φ (h ω))) := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_coupling μ R Φ hR hΦ P' X Xl hXm hXlm
    hXlaw hXllaw Y hYm hY hYconv happrox).exists_seq_tendsto_ae
  refine ⟨ns, hns, fun P h hh hlaw => ?_⟩
  rw [← hlaw] at hae
  exact ae_of_ae_map hh hae

end SupercriticalLQGUniqueness.B2.PfeWeyl
