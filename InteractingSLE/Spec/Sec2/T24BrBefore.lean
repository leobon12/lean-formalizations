import InteractingSLE.Spec.Sec2.T24BrFiltration

/-!
# Curve information before a lifetime

The driver need only be adapted on its live interval. Curve events, restricted to a
later live event, are measurable in the augmented evolution filtration. No force-point
definition enters this comparison.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Ambient-measurable sets that agree a.s. are interchangeable after augmentation. -/
theorem measurableSet_usualAugmentation_of_ae_eq {A B : Set Ω} {t : ℝ≥0}
    (hA : MeasurableSet A) (hB : MeasurableSet[𝓕 t] B) (he : A =ᵐ[P] B) :
    MeasurableSet[usualAugmentation 𝓕 P t] A := by
  have hBm : MeasurableSet B := 𝓕.le t _ hB
  have hAB0 : P (A \ B) = 0 := by
    apply measure_mono_null (fun ω hω => show ω ∈ {ω | ¬ (ω ∈ A ↔ ω ∈ B)} from
      fun h => hω.2 (h.1 hω.1))
    exact ae_iff.1 (he.mono fun ω hω => Iff.of_eq hω)
  have hBA0 : P (B \ A) = 0 := by
    apply measure_mono_null (fun ω hω => show ω ∈ {ω | ¬ (ω ∈ A ↔ ω ∈ B)} from
      fun h => hω.2 (h.2 hω.1))
    exact ae_iff.1 (he.mono fun ω hω => Iff.of_eq hω)
  have heq : A = (B \ (B \ A)) ∪ (A \ B) := by ext ω; simp; tauto
  rw [heq]
  exact ((Ito.le_usualAugmentation 𝓕 P t _ hB).diff
    (Ito.measurableSet_usualAugmentation_of_null (hBm.diff hA) hBA0 t)).union
    (Ito.measurableSet_usualAugmentation_of_null (hA.diff hBm) hAB0 t)

/-- On a later live event the generating curve is a measurable function of the killed driver. -/
theorem measurable_curve_indicator_before {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hW : AdaptedBefore 𝓕 ζ W)
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    {u r : ℝ≥0} (hur : u ≤ r) :
    Measurable[usualAugmentation 𝓕 P r]
      ({ω | (r : ℝ≥0∞) < ζ ω}.indicator (η u)) := by
  classical
  let E : Set Ω := {ω | (r : ℝ≥0∞) < ζ ω}
  have hE : MeasurableSet[𝓕 r] E := by simpa [E] using hW r univ MeasurableSet.univ
  have hEm : MeasurableSet E := 𝓕.le r _ hE
  have ht : Measurable[𝓕 r] fun ω => LP.traceAt u (Girsanov.killed ζ W · ω) :=
    (measurable_traceAt_of_adapted (𝓕 := 𝓕) fun s hs =>
      (Girsanov.measurable_killed hW s).mono (𝓕.mono hs) le_rfl).mono (𝓕.mono hur) le_rfl
  have he : E.indicator (η u) =ᵐ[P]
      E.indicator (fun ω => LP.traceAt u (fun s => Girsanov.killed ζ W s ω)) := by
    filter_upwards [hgen] with ω hω
    by_cases h : ω ∈ E
    · rw [indicator_of_mem h, indicator_of_mem h]
      rw [LP.traceAt_congr (w' := (W · ω)) (fun s hs =>
        Girsanov.killed_of_lt (lt_of_le_of_lt (by exact_mod_cast hs.trans hur) h))]
      exact (LP.traceAt_eq_of_isGeneratingTrace hω.2 hω.1.continuousOn
        (Sec7.SideHeight.w_zero_of_isGeneratingTrace hω.2 ENNReal.zero_lt_top)
        ENNReal.coe_lt_top).symm
    · simp only [indicator_of_notMem h]
  exact measurable_usualAugmentation_of_ae_eq ((hη u).measurable.indicator hEm)
    (ht.indicator hE) he

/-- A raw curve-history event restricted to a live event is measurable. -/
theorem natural_curve_event_before_measurable {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hW : AdaptedBefore 𝓕 ζ W)
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    {u r : ℝ≥0} (hur : u ≤ r) {A : Set Ω}
    (hA : MeasurableSet[Filtration.natural η hη u] A) :
    MeasurableSet[usualAugmentation 𝓕 P r] (A ∩ {ω | (r : ℝ≥0∞) < ζ ω}) := by
  classical
  rw [Filtration.natural_eq_comap] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  let E : Set Ω := {ω | (r : ℝ≥0∞) < ζ ω}
  have hE : MeasurableSet[𝓕 r] E := by simpa [E] using hW r univ MeasurableSet.univ
  have hm : Measurable[usualAugmentation 𝓕 P r]
      (fun ω => fun q : Iic u => E.indicator (η q) ω) := by
    let : MeasurableSpace Ω := usualAugmentation 𝓕 P r
    exact measurable_pi_iff.2 fun q =>
      measurable_curve_indicator_before hη hW hgen (q.2.trans hur)
  have he : (fun ω (q : Iic u) => η q ω) ⁻¹' B ∩ E =
      (fun ω (q : Iic u) => E.indicator (η q) ω) ⁻¹' B ∩ E := by
    ext ω
    by_cases h : ω ∈ E
    · simp only [mem_inter_iff, mem_preimage, h, and_true]
      have heq : (fun q : Iic u => E.indicator (η q) ω) = fun q : Iic u => η q ω :=
        funext fun q => indicator_of_mem h _
      rw [heq]
    · simp [h]
  rw [he]
  exact (hm hB).inter (Ito.le_usualAugmentation 𝓕 P r _ hE)

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'}
  {𝓕' : Filtration ℝ≥0 mΩ'} {π : Ω' → Ω}

/-- The comparison allows an arbitrary measure-preserving probability extension. -/
theorem curve_event_before_measurable {W : ℝ≥0 → Ω → ℝ} {ζ : Ω' → ℝ≥0∞}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hπ : MeasurePreserving π Q P)
    (hW : AdaptedBefore 𝓕' ζ (fun t ω => W t (π ω)))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    {s r : ℝ≥0} (hsr : s < r) {A : Set Ω}
    (hA : MeasurableSet[usualAugmentation (Filtration.natural η hη) P s] A) :
    MeasurableSet[usualAugmentation 𝓕' Q r]
      (π ⁻¹' A ∩ {ω | (r : ℝ≥0∞) < ζ ω}) := by
  obtain ⟨u, hsu, hur⟩ := exists_between hsr
  obtain ⟨B, hB, he⟩ := Ito.exists_ae_eq_of_measurableSet_usualAugmentation hsu hA
  have hη' : ∀ t, StronglyMeasurable (fun ω => η t (π ω)) :=
    fun t => (hη t).comp_measurable hπ.measurable
  have hB' : MeasurableSet[Filtration.natural (fun t ω => η t (π ω)) hη' u]
      (π ⁻¹' B) := by
    rw [Filtration.natural_eq_comap] at hB ⊢
    obtain ⟨C, hC, rfl⟩ := hB
    exact ⟨C, hC, rfl⟩
  have hgen' := hπ.quasiMeasurePreserving.ae hgen
  have hm := natural_curve_event_before_measurable hη' hW hgen' hur.le hB'
  have hE : MeasurableSet[𝓕' r] {ω | (r : ℝ≥0∞) < ζ ω} := by
    simpa using hW r univ MeasurableSet.univ
  have hAm := (usualAugmentation (Filtration.natural η hη) P).le s _ hA
  have he' : (π ⁻¹' A ∩ {ω | (r : ℝ≥0∞) < ζ ω}) =ᵐ[Q]
      (π ⁻¹' B ∩ {ω | (r : ℝ≥0∞) < ζ ω}) := by
    filter_upwards [hπ.quasiMeasurePreserving.ae he] with ω hω
    simp only [mem_inter_iff, mem_preimage, hω]
  have hh := measurableSet_usualAugmentation_of_ae_eq
    ((hπ.measurable hAm).inter (𝓕'.le r _ hE)) hm he'
  rwa [usualAugmentation_idempotent] at hh

/-- A curve event supported on survival at its own time belongs to the evolution filtration. -/
theorem curve_event_supported_before_measurable {W : ℝ≥0 → Ω → ℝ} {ζ : Ω' → ℝ≥0∞}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hπ : MeasurePreserving π Q P)
    (hW : AdaptedBefore 𝓕' ζ (fun t ω => W t (π ω)))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    {s : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[usualAugmentation (Filtration.natural η hη) P s] A)
    (hlive : ∀ᵐ ω ∂Q, π ω ∈ A → (s : ℝ≥0∞) < ζ ω) :
    MeasurableSet[usualAugmentation 𝓕' Q s] (π ⁻¹' A) := by
  have hAm := hπ.measurable ((usualAugmentation (Filtration.natural η hη) P).le s _ hA)
  have hmeas (v : ℝ≥0) (hsv : s < v) :
      MeasurableSet[usualAugmentation 𝓕' Q v] (π ⁻¹' A) := by
    obtain ⟨r, -, hr, hlim⟩ := exists_seq_strictAnti_tendsto' hsv
    have hm : MeasurableSet[usualAugmentation 𝓕' Q v]
        (⋃ n : ℕ, π ⁻¹' A ∩ {ω | (r n : ℝ≥0∞) < ζ ω}) :=
      MeasurableSet.iUnion fun n => (usualAugmentation 𝓕' Q).mono (hr n).2.le _
        (curve_event_before_measurable hη hπ hW hgen (hr n).1 hA)
    have he : (π ⁻¹' A) =ᵐ[Q]
        (⋃ n : ℕ, π ⁻¹' A ∩ {ω | (r n : ℝ≥0∞) < ζ ω}) := by
      filter_upwards [hlive] with ω hω
      apply propext
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro h
        have hc : Tendsto (fun n => (r n : ℝ≥0∞)) atTop (𝓝 (s : ℝ≥0∞)) :=
          ENNReal.continuous_coe.continuousAt.tendsto.comp hlim
        obtain ⟨n, hn⟩ := ((tendsto_order.1 hc).2 _ (hω h)).exists
        exact ⟨n, h, hn⟩
      · rintro ⟨n, h, -⟩
        exact h
    have hh := measurableSet_usualAugmentation_of_ae_eq hAm hm he
    rwa [usualAugmentation_idempotent] at hh
  rw [← Filtration.IsRightContinuous.eq (𝓕 := usualAugmentation 𝓕' Q), Filtration.rightCont_eq]
  exact MeasurableSpace.measurableSet_iInf.2 fun v =>
    MeasurableSpace.measurableSet_iInf.2 fun hsv => hmeas v hsv

/-- Curve stopping times bounded by the lifetime remain stopping times on the extension. -/
theorem isStoppingTime_curve_pullback_before {W : ℝ≥0 → Ω → ℝ} {ζ : Ω' → ℝ≥0∞}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hπ : MeasurePreserving π Q P)
    (hW : AdaptedBefore 𝓕' ζ (fun t ω => W t (π ω)))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation (Filtration.natural η hη) P) σ)
    (hσζ : ∀ᵐ ω ∂Q, σ (π ω) ≤ ζ ω) :
    IsStoppingTime (usualAugmentation 𝓕' Q) (σ ∘ π) := by
  intro s
  have hA : MeasurableSet[usualAugmentation (Filtration.natural η hη) P s]
      {ω | (s : WithTop ℝ≥0) < σ ω} := by
    simpa only [Set.compl_ofPred, not_le] using (hσ s).compl
  have hh := curve_event_supported_before_measurable hη hπ hW hgen hA
    (hσζ.mono fun ω hω h => lt_of_lt_of_le h hω)
  simpa only [Set.preimage_ofPred_eq, Set.compl_ofPred, not_lt, Function.comp_def] using hh.compl

/-- The event needed for stopped-martingale descent. -/
theorem curve_event_before_stop_measurable {W : ℝ≥0 → Ω → ℝ} {ζ : Ω' → ℝ≥0∞}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hπ : MeasurePreserving π Q P)
    (hW : AdaptedBefore 𝓕' ζ (fun t ω => W t (π ω)))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation (Filtration.natural η hη) P) σ)
    (hσζ : ∀ᵐ ω ∂Q, σ (π ω) ≤ ζ ω)
    {s r : ℝ≥0} (hsr : s ≤ r) {A : Set Ω}
    (hA : MeasurableSet[usualAugmentation (Filtration.natural η hη) P s] A) :
    MeasurableSet[usualAugmentation 𝓕' Q r]
      (π ⁻¹' A ∩ {ω | (r : WithTop ℝ≥0) < σ (π ω)}) := by
  have hAr := (usualAugmentation (Filtration.natural η hη) P).mono hsr _ hA
  have hB : MeasurableSet[usualAugmentation (Filtration.natural η hη) P r]
      (A ∩ {ω | (r : WithTop ℝ≥0) < σ ω}) := by
    exact hAr.inter (by simpa only [Set.compl_ofPred, not_le] using (hσ r).compl)
  exact curve_event_supported_before_measurable hη hπ hW hgen hB
    (hσζ.mono fun ω hω h => lt_of_lt_of_le h.2 hω)

end InteractingSLE.Sec2.T24Bridge
